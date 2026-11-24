-- Prove2me | solution 1 for GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:57.646657+00:00
-- url     : https://prove2.me/submissions/97f07123-5ea5-40c1-b3f4-5c17b6f19ab0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_eq_of_setLIntegral_compact_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B → ContinuousOn D' B → (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) → ∀ b ∈ B, D b = D' b := by
  first | exact @GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | exact GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | (intros; apply GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq <;> assumption)
end _root_.GlobalTheory.T
