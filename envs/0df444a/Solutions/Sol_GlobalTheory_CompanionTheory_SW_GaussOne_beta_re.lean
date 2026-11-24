-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.beta_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:54.534966+00:00
-- url     : https://prove2.me/submissions/2dd15359-f4ba-43f4-8393-84e90bdf9d5e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform

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
theorem _root_.solution (τ : ℂ) {e : ℝ} : (beta τ e).re = τ.im := by
  simp [beta]
end GlobalTheory.CompanionTheory.SW.GaussOne
