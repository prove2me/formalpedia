-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothLog.exists_smooth_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:01.819119+00:00
-- url     : https://prove2.me/submissions/44822990-337d-4042-8605-fb9e6aeb57d1

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothLog_exists_log_banach

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothLog
namespace GlobalTheory.CompanionTheory.SmoothLog
theorem _root_.solution : ∀ (n : ℕ), ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧ (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧ (∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X) ∧ ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by
  intro n
  obtain ⟨U, L, hU, h1, hL, hL1, hexp, hev⟩ := exists_log_banach (OpMat n)
  let φ := toOp n
  have hφexp : ∀ X, NormedSpace.exp (φ X) = φ (NormedSpace.exp X) := fun _ => rfl
  refine ⟨φ ⁻¹' U, fun g => φ.symm (L (φ g)), hU.preimage φ.continuous, h1, ?_, ?_, ?_, ?_, ?_⟩
  · exact φ.symm.contDiff.comp_contDiffOn (hL.comp φ.contDiff.contDiffOn fun _ hx => hx)
  · change φ.symm (L 1) = 0
    rw [hL1, map_zero]
  · intro g hg
    apply φ.injective
    rw [← hφexp, φ.apply_symm_apply]
    exact hexp _ hg
  · have ht : Tendsto φ (𝓝 0) (𝓝 0) := by
      simpa using φ.continuous.tendsto 0
    filter_upwards [ht.eventually hev] with X hX
    change φ.symm (L (φ (NormedSpace.exp X))) = X
    rw [← hφexp, hX, φ.symm_apply_apply]
  · exact φ.symm.contDiff.comp ((CompanionTheory.D.Upq.contDiff_exp ℝ (OpMat n)).comp φ.contDiff)
end GlobalTheory.CompanionTheory.SmoothLog
