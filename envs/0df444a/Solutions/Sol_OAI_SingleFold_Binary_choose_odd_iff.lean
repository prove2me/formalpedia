-- Prove2me | solution 1 for OAI.SingleFold.Binary.choose_odd_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:12:50.28799+00:00
-- url     : https://prove2.me/submissions/6eae4d2a-d21a-4fd3-b324-f983592730e8

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

open OAI OAI.SingleFold OAI.SingleFold.Binary
theorem h49_bits_iff (x y : ℕ) : OAI.SingleFold.Binary.Bits x y ↔
    x%2 ≤ y%2 ∧ OAI.SingleFold.Binary.Bits (x/2) (y/2) := by
  unfold OAI.SingleFold.Binary.Bits
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun i => ?_⟩
    have := h (i+1)
    rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      exact h i

theorem h49_lucas2 (n : ℕ) : ∀ x y : ℕ, x + y = n →
    (y.choose x % 2 = 1 ↔ OAI.SingleFold.Binary.Bits x y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hn
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0; simp [OAI.SingleFold.Binary.Bits]
  rw [h49_bits_iff, ← ih (x/2+y/2) (by omega) _ _ rfl]
  have hl : y.choose x % 2 = (y%2).choose (x%2) * (y/2).choose (x/2) % 2 :=
    @Choose.choose_modEq_choose_mod_mul_choose_div_nat y x 2 ⟨Nat.prime_two⟩
  rw [hl, Nat.mul_mod]
  have hx : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hy : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : (y/2).choose (x/2) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize x % 2 = a at *
  generalize y % 2 = b at *
  generalize (y/2).choose (x/2) % 2 = c at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp

theorem solution (x y : ℕ) : y.choose x % 2=1 ↔ Bits x y := by
  exact h49_lucas2 _ x y rfl

