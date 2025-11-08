import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Even
import Lean
import Mathlib.Order.RelClasses
--import Mathlib.Init.Algebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupWithZero.Basic

open Lean Meta
open Set
open Real
open Mathlib.Tactic

/-!
# Schule

This file defines torsors of additive group actions.

## Notation

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/


/-- Beispiel 2 -/
theorem zweite_lemma (x : ℝ) : x + 100 * x^2 + 120 * x^2 +1= 220 * x^2 +1 +x :=
by ring

/-- Beispiel 3 -/
theorem dritte_lemma (a b : ℝ) : (2*a+b)^2 = 4*a^2+4*a*b+b^2 :=
by ring

/--
das soll da erscheinen3!!
$$
\frac{a}{b} \cdot \frac{c}{d} = \frac{a \cdot c}{b \cdot d}
$$
-/
theorem frac_mul
 {R : Type*} [Field R] (a b c d : R) (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) * (c / d) = (a*c) / (b*d) := by
field_simp [hb, hd]


theorem axiom_mul_inv_cancel
 {R : Type*} [g : Field R] (a : R) (h : a ≠ 0) :
      a * a⁻¹  =  a    := by
  apply GroupWithZero.mul_inv_cancel
  assumption
