-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.transvection_map_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:46.717528+00:00
-- url     : https://prove2.me/submissions/92f2ab9a-87c9-45d4-8461-c5c81a6a4671

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvection
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Transv_map_toMatrix_mulVec

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
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  intro K _ _ _ _ _ _ _ _ ι _ _ μ _ t
  exact GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec K ι μ t
end GlobalTheory.CompanionTheory.SW
