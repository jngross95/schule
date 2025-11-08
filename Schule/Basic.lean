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

/-- Beispiel 2 -/
theorem zweite_lemma (x : ℝ) : x + 100 * x^2 + 120 * x^2 +1= 220 * x^2 +1 +x :=
by ring

/-- Beispiel 3 -/
theorem dritte_lemma (a b : ℝ) : (2*a+b)^2 = 4*a^2+4*a*b+b^2 :=
by ring

/--
das soll da erscheinen3!!
$$
\frac{a}{c} \cdot \frac{b}{d} = \frac{a \cdot b}{c \cdot d}
$$
-/
theorem frac_mul
 {R : Type*} [Field R] (a b c d : R) (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) * (c / d) = (a*c) / (b*d) := by
field_simp [hb, hd]


theorem axiom_mul_inv_cancel
 {R : Type*} [g : Field R] (a : R) (h : a ≠ 0) :
      a * a⁻¹  =  1    := by
  apply GroupWithZero.mul_inv_cancel
  assumption
