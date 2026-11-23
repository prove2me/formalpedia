-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiLinearClockWitness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:25:28.622693+00:00
-- url     : https://prove2.me/submissions/732be8a2-bc88-4a6d-a1ba-0531f76cde75

import Mathlib
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (y : Nat) (t : NNReal) (A : Real)
    (hBefore : (y : Real) * (t : Real) < A) :
    ∃ s : NNReal, (s : Real) < A ∧
      (t : ENNReal) < (y : ENNReal)⁻¹ * (s : ENNReal) := by
  have hB0 : 0 ≤ (y : Real) * (t : Real) := by positivity
  have hA : 0 < A := lt_of_le_of_lt hB0 hBefore
  let B : Real := (y : Real) * (t : Real)
  let M : Real := (B + A) / 2
  have hM : 0 ≤ M := by dsimp [M, B]; linarith
  let s : NNReal := Real.toNNReal M
  have hsA : (s : Real) < A := by
    change (Real.toNNReal M : Real) < A
    rw [Real.coe_toNNReal M hM]
    dsimp [M, B]
    linarith
  have hBS : (y : Real) * (t : Real) < (s : Real) := by
    change (y : Real) * (t : Real) < (Real.toNNReal M : Real)
    rw [Real.coe_toNNReal M hM]
    dsimp [M, B]
    linarith
  refine ⟨s, hsA, ?_⟩
  by_cases hy : y = 0
  · have hsPos : (0 : NNReal) < s := by
      apply NNReal.coe_lt_coe.mp
      simpa [hy] using hBS
    have hsNe : (s : ENNReal) ≠ 0 := ne_of_gt
      (ENNReal.coe_lt_coe.mpr hsPos)
    subst y
    simp only [Nat.cast_zero, ENNReal.inv_zero]
    rw [ENNReal.top_mul hsNe]
    exact ENNReal.coe_lt_top
  · have hBS' : (y : NNReal) * t < s := by
      exact_mod_cast hBS
    have hCore : (t : ENNReal) * (y : ENNReal) < (s : ENNReal) := by
      simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm] using
        (ENNReal.coe_lt_coe.mpr hBS')
    have hyZero : (y : ENNReal) ≠ 0 := by exact_mod_cast hy
    have hyTop : (y : ENNReal) ≠ ⊤ := by simp
    have hDiv : (t : ENNReal) < (s : ENNReal) / (y : ENNReal) :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hyZero) (Or.inl hyTop)).mpr hCore
    simpa only [div_eq_mul_inv, mul_comm] using hDiv