-- Prove2me | solution 1 for JHolomorphic.enorm_integral_smul_le_eLpNorm_mul_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T09:26:00.974292+00:00
-- url     : https://prove2.me/submissions/8394ec32-2925-40a4-a93c-01e4218280e7

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic



namespace JHolomorphic

open MeasureTheory
open scoped ENNReal

theorem enorm_integral_smul_le_eLpNorm_mul_eLpNorm_aux2 {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} (p : ℝ) (hp : 1 < p) {φ : α → ℝ}
    {f : α → E} (hφ : AEStronglyMeasurable φ μ) (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, φ x • f x ∂μ‖ₑ ≤
      eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm f (ENNReal.ofReal p) μ := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one, add_comm]; exact hpq.inv_add_inv_ennreal⟩
  calc ‖∫ x, φ x • f x ∂μ‖ₑ ≤ ∫⁻ x, ‖φ x • f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (φ • f) 1 μ := by rw [eLpNorm_one_eq_lintegral_enorm]; rfl
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm hf hφ

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ENNReal

theorem solution {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} (p : ℝ) (hp : 1 < p) {φ : α → ℝ}
    {f : α → E} (hφ : AEStronglyMeasurable φ μ) (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, φ x • f x ∂μ‖ₑ ≤
      eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm f (ENNReal.ofReal p) μ :=
  enorm_integral_smul_le_eLpNorm_mul_eLpNorm_aux2 p hp hφ hf
