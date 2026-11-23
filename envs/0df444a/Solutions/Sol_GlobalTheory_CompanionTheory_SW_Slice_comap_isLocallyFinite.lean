-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.comap_isLocallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:52.163558+00:00
-- url     : https://prove2.me/submissions/32be35fe-0a7f-4935-b27b-6b427f6e1b33

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution {W V : Type} [TopologicalSpace W] [MeasurableSpace W]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace W] [BorelSpace V] {T : W → V}
    (hT : IsOpenEmbedding T) (μ : Measure V) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.comap T) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hxs, hs, hfin⟩ := μ.exists_isOpen_measure_lt_top (T x)
  have hme : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨T ⁻¹' s, (hs.preimage hT.continuous).mem_nhds hxs, ?_⟩
  rw [hme.comap_apply]
  exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) hfin
end GlobalTheory.CompanionTheory.SW.Slice
