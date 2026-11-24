-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.norm_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:59.406453+00:00
-- url     : https://prove2.me/submissions/0ad8b216-9815-4b69-809b-1d7c3b76ee40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_beta_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_beta_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
namespace GlobalTheory.CompanionTheory.SW.GaussOne
theorem _root_.solution (τ : ℂ) {e : ℝ} (he : e = 1 ∨ e = -1) : ‖beta τ e‖ = ‖τ‖ := by
  rcases he with rfl | rfl
  · rw [beta_one]; simp
  · rw [beta_neg_one]; simp
end GlobalTheory.CompanionTheory.SW.GaussOne
