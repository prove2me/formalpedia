-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreGlue.piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:13.368697+00:00
-- url     : https://prove2.me/submissions/764cf94b-a83e-4e60-85c0-ed5e88b6691c

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreGlue_ae_g_eq

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreGlue
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}
namespace GlobalTheory.CompanionTheory.SW.FibreGlue
theorem _root_.solution (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {s D : Set X} (hD : MeasurableSet D) (hDs : D ⊆ s) {F : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' s) ν s F) {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ b in D, ∫⁻ v, φ v ∂(F b) ∂ν := by
  have hm : MeasurableSet (g ⁻¹' D) := hg.measurable hD
  have e1 : ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ v in g ⁻¹' s, (g ⁻¹' D).indicator φ v ∂μ := by
    rw [setLIntegral_indicator hm, Set.inter_eq_left.2 (Set.preimage_mono hDs)]
  rw [e1, h.2.1 _ (hφ.indicator hm), ← lintegral_indicator hD]
  refine lintegral_congr fun b => ?_
  have hae := ae_g_eq hι hf (h.1 b)
  by_cases hb : b ∈ D
  · rw [Set.indicator_of_mem hb]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have : v ∈ g ⁻¹' D := by
      show g v ∈ D
      rw [hv]; exact hb
    simp only [Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem hb]
    have e : ∫⁻ v, (g ⁻¹' D).indicator φ v ∂(F b) = ∫⁻ _, 0 ∂(F b) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      have : v ∉ g ⁻¹' D := by
        show g v ∉ D
        rw [hv]; exact hb
      simp only [Set.indicator_of_notMem this]
    simpa using e
end GlobalTheory.CompanionTheory.SW.FibreGlue
