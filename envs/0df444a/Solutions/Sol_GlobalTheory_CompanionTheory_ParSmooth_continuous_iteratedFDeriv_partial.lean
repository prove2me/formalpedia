-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ParSmooth.continuous_iteratedFDeriv_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:42.452794+00:00
-- url     : https://prove2.me/submissions/43af15fa-7313-4717-a3b5-177def8c56a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_JetProofs_ContinuousIteratedFDerivPartial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ParSmooth
namespace GlobalTheory.CompanionTheory.ParSmooth
theorem _root_.solution {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (k : ℕ) :
    Continuous fun z : P × Q => iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 := by
  have key : ∀ z : P × Q, iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 =
      (iteratedFDeriv ℝ k Ψ z).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    intro z
    have h1 : (fun y => Ψ (y, z.2)) =
        (fun w => Ψ (((0 : P), z.2) + w)) ∘ ContinuousLinearMap.inl ℝ P Q := by
      funext y; simp
    have h2 : ContDiff ℝ ∞ (fun w => Ψ (((0 : P), z.2) + w)) :=
      hΨ.comp (contDiff_const.add contDiff_id)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_left]
    simp
  simp_rw [key]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
    (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
end GlobalTheory.CompanionTheory.ParSmooth
