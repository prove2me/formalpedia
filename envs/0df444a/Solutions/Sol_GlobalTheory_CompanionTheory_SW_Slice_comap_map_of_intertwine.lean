-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.comap_map_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:42.318804+00:00
-- url     : https://prove2.me/submissions/802475eb-8450-4bf4-8f12-45241aecf352

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
theorem _root_.solution {W V : Type} [MeasurableSpace W] [MeasurableSpace V]
    {T : W → V} (hT : MeasurableEmbedding T) {L L' : W → W} {A A' : V → V}
    (hL : Measurable L) (hA : Measurable A) (hLL' : ∀ w, L (L' w) = w)
    (hAA' : ∀ v, A' (A v) = v)
    (hint : ∀ w, T (L w) = A (T w)) (hint' : ∀ w, T (L' w) = A' (T w))
    (μ : Measure V) (c : ℝ≥0∞) (hμ : μ.map A = c • μ) :
    (μ.comap T).map L = c • μ.comap T := by
  ext s hs
  have himg : T '' (L ⁻¹' s) = A ⁻¹' (T '' s) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨L w, hw, hint w⟩
    · rintro ⟨y, hy, hyv⟩
      refine ⟨L' y, ?_, ?_⟩
      · change L (L' y) ∈ s
        rwa [hLL']
      · rw [hint', hyv, hAA']
  rw [Measure.map_apply hL hs, Measure.smul_apply, hT.comap_apply, hT.comap_apply, himg,
    ← Measure.map_apply hA (hT.measurableSet_image.2 hs), hμ, Measure.smul_apply]
end GlobalTheory.CompanionTheory.SW.Slice
