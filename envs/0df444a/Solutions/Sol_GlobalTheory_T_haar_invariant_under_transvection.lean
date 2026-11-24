-- Prove2me | solution 1 for GlobalTheory.T.haar_invariant_under_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:16.503887+00:00
-- url     : https://prove2.me/submissions/a497b9d2-ce24-4d1e-94df-17afb9e7fb73

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvection
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvectionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_transvection_map_addHaar


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
theorem _root_.solution : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | exact GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | (intros; apply GlobalTheory.CompanionTheory.SW.transvection_map_addHaar <;> assumption)
end _root_.GlobalTheory.T
