-- Prove2me | solution 1 for GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:40.032506+00:00
-- url     : https://prove2.me/submissions/1bf57443-90b2-4443-9cdd-f93b65513210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasFDerivAtSetIntegral
import Theorems.Thm_GlobalTheory_SetIntegralSmoothness_hasFDerivAt_setIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ContDiff
open GlobalTheory GlobalTheory.SetIntegralSmoothness
namespace GlobalTheory.SetIntegralSmoothness
theorem _root_.solution {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ) := by
  induction m generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun p₀ =>
      (hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀).continuousAt
  | succ m IH =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ x in K, (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ, ?_,
      fun p₀ => hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀⟩
    have hΨ' : ContDiff ℝ ∞ fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E) :=
      (hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    exact IH (fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E)) hΨ'
end GlobalTheory.SetIntegralSmoothness
