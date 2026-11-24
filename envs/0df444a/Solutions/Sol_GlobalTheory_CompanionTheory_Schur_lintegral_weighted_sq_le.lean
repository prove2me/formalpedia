-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Schur.lintegral_weighted_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:11.906241+00:00
-- url     : https://prove2.me/submissions/609cd184-3639-400c-8fdb-d786758a1109

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralWeightedSqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Schur
namespace GlobalTheory.CompanionTheory.Schur
theorem _root_.solution {α : Type} [MeasurableSpace α] (ν : Measure α)
    (u g : α → ℝ≥0∞) (hu : Measurable u) (hg : Measurable g) :
    (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ (∫⁻ y, u y ∂ν) * ∫⁻ y, u y * g y ^ 2 ∂ν := by
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs : Measurable fun y => u y ^ (1 / 2 : ℝ) := hu.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hs.aemeasurable
    (hs.mul hg).aemeasurable
  have e1 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * ((fun y => u y ^ (1 / 2 : ℝ)) * g)) a ∂ν
      = ∫⁻ y, u y * g y ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← sq, hsq]
  have e2 : ∫⁻ a, (u a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ν = ∫⁻ y, u y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.rpow_two, hsq]
  have e3 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * g) a ^ (2 : ℝ) ∂ν = ∫⁻ y, u y * g y ^ 2 ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.rpow_two, mul_pow, hsq]
  rw [e1, e2, e3] at h
  calc (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ _ := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, hsq, hsq]
end GlobalTheory.CompanionTheory.Schur
