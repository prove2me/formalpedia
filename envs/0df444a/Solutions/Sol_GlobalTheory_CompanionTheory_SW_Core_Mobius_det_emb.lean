-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Mobius.det_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:29.754595+00:00
-- url     : https://prove2.me/submissions/8e28c3b4-7c78-4ee5-af22-4dd293fb865d

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlane

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Mobius
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.SW.Core.Mobius
theorem _root_.solution (σ : F →+* ℝ) (γ : SL(2, F)) :
    σ (γ 0 0) * σ (γ 1 1) - σ (γ 0 1) * σ (γ 1 0) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg σ h
  simpa using this
end GlobalTheory.CompanionTheory.SW.Core.Mobius
