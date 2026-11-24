-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.withDensity_map_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:46.438873+00:00
-- url     : https://prove2.me/submissions/99cdaed9-609e-4756-9322-a2a9f8ef221e

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
theorem _root_.solution {W : Type} [MeasurableSpace W] {L : W → W} (hL : Measurable L)
    (ρ : Measure W) (c k : ℝ≥0∞) (hρ : ρ.map L = c • ρ) {d : W → ℝ≥0∞} (hd : Measurable d)
    (hk : ∀ w, d w = k * d (L w)) (hck : k * c = 1) :
    (ρ.withDensity d).map L = ρ.withDensity d := by
  ext s hs
  rw [Measure.map_apply hL hs, withDensity_apply _ (hL hs), withDensity_apply _ hs]
  calc ∫⁻ w in L ⁻¹' s, d w ∂ρ = ∫⁻ w, (L ⁻¹' s).indicator d w ∂ρ :=
        (lintegral_indicator (hL hs) _).symm
    _ = ∫⁻ w, k * s.indicator d (L w) ∂ρ := by
        refine lintegral_congr fun w => ?_
        by_cases hw : L w ∈ s
        · rw [Set.indicator_of_mem (show w ∈ L ⁻¹' s from hw), Set.indicator_of_mem hw, ← hk]
        · rw [Set.indicator_of_notMem (show w ∉ L ⁻¹' s from hw), Set.indicator_of_notMem hw,
            mul_zero]
    _ = k * ∫⁻ w, s.indicator d (L w) ∂ρ :=
        lintegral_const_mul _ ((hd.indicator hs).comp hL)
    _ = k * ∫⁻ w, s.indicator d w ∂(ρ.map L) := by
        rw [lintegral_map (hd.indicator hs) hL]
    _ = ∫⁻ w in s, d w ∂ρ := by
        rw [hρ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hck, one_mul,
          lintegral_indicator hs]
end GlobalTheory.CompanionTheory.SW.Slice
