-- Prove2me | solution 1 for GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:49.547149+00:00
-- url     : https://prove2.me/submissions/2bd3a904-53a6-4391-b08d-b2055f8d4d7a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureProdOfAddGroups
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureProdOfAddGroupsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarTransport_map_addEquiv_haar


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
theorem _root_.solution : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V') [μ'.IsAddHaarMeasure] (e : V ≃+ V'), Continuous e → Continuous e.symm → (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧ ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty → (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | exact GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | (intros; apply GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar <;> assumption)
end _root_.GlobalTheory.T
