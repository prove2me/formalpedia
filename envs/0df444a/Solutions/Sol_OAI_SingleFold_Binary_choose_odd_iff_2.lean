-- Prove2me | solution 2 for OAI.SingleFold.Binary.choose_odd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:51:56.531983+00:00
-- url     : https://prove2.me/submissions/f0123c28-ddc8-42ce-b47c-b54b3e198c42

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Binary.lean:L32-L45
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Binary.choose_odd_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary

-- ---- from OAI.NumberTheory.SingleFold.Binary ----
namespace OAI

namespace SingleFold.Binary

lemma split (x y : ℕ) : Bits x y ↔ x%2 ≤ y%2 ∧ Bits (x/2) (y/2) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    simpa [Nat.div_div_eq_div_mul, pow_succ', mul_comm] using h (i+1)
  · rintro ⟨h,h'⟩ (_|i)
    · simpa using h
    · simpa [Nat.div_div_eq_div_mul, pow_succ', mul_comm] using h' i

lemma zero_right (x : ℕ) : Bits x 0 ↔ x=0 := by
  constructor
  · induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx
      by_cases h : x=0
      · exact h
      have he := (split x 0).mp hx
      have hh := ih (x/2) (Nat.div_lt_self (by omega) (by omega)) (by simpa using he.2)
      simp only [Nat.zero_mod] at he
      omega
  · rintro rfl; intro i; simp

lemma choose_odd_iff (x y : ℕ) : y.choose x % 2=1 ↔ Bits x y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y=0
    · subst y
      rw [zero_right]
      cases x <;> simp
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=y) (k:=x) (p:=2)
    change y.choose x%2 = (y%2).choose (x%2)*(y/2).choose (x/2)%2 at hl
    rw [hl,Nat.mul_mod,split, ← ih (y/2) (Nat.div_lt_self (by omega) (by omega))]
    have hx := Nat.mod_lt x (by omega : 0<2)
    have hy' := Nat.mod_lt y (by omega : 0<2)
    have hz := Nat.mod_lt ((y/2).choose (x/2)) (by omega : 0<2)
    interval_cases hxm : x%2 <;> interval_cases hym : y%2 <;> simp_all

end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
end SingleFold.Binary

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Binary


theorem solution : type_of% @_root_.OAI.SingleFold.Binary.choose_odd_iff := @_root_.OAI.SingleFold.Binary.choose_odd_iff
