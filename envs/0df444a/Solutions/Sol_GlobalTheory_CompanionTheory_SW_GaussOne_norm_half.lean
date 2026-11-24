-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.norm_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:16.976987+00:00
-- url     : https://prove2.me/submissions/620eadde-af85-4245-992c-975dde5a6c68

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_norm_beta

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
theorem _root_.solution (τ : ℂ) {e : ℝ} (he : e = 1 ∨ e = -1) :
    ‖((beta τ e)⁻¹) ^ (1 / 2 : ℂ)‖ = (Real.sqrt ‖τ‖)⁻¹ := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_cpow_real, norm_inv, norm_beta τ he, Real.inv_rpow (norm_nonneg _),
    Real.sqrt_eq_rpow]
end GlobalTheory.CompanionTheory.SW.GaussOne
