-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.beta_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:56.42494+00:00
-- url     : https://prove2.me/submissions/9aca480a-f57d-48a6-b413-57445b2b614f

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
theorem _root_.solution (τ : ℂ) : beta τ (-1) = Complex.I * (starRingEnd ℂ) τ := by
  apply Complex.ext <;> simp [beta]
end GlobalTheory.CompanionTheory.SW.GaussOne
