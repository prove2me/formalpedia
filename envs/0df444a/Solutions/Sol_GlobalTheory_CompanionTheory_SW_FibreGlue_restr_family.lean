-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreGlue.restr_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:19.721135+00:00
-- url     : https://prove2.me/submissions/09ec5a48-9bd5-4686-8b48-9e4b326bd11b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreGlue_piece

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
    {B B₂ : Set X} (hB₂ : IsOpen B₂) (hsub : B₂ ⊆ B) {fam : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' B) ν B fam) :
    IsFibreFamily μ f ι (g ⁻¹' B₂) ν B₂ (restr B₂ fam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B₂
    · simp only [restr, if_pos hb]
      refine measure_mono_null ?_ (h.1 b)
      intro v hv hv2
      apply hv
      refine ⟨hv2.1, ?_⟩
      show g v ∈ B₂
      have : g v = b := by
        apply hι
        rw [← hf v]
        exact hv2.1
      rw [this]; exact hb
    · simp [restr, hb]
  · intro φ hφ
    rw [piece hι hg hf hB₂.measurableSet hsub h hφ, ← lintegral_indicator hB₂.measurableSet]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ B₂
    · simp [restr, hb]
    · simp [restr, hb]
  · intro φ hφ hφc hφs
    have H := h.2.2 φ hφ hφc (hφs.trans (Set.preimage_mono hsub))
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [restr, if_pos hb]
      exact H.1 b (hsub hb)
    · refine (H.2.mono hsub).congr fun b hb => ?_
      simp only [restr, if_pos hb]
end GlobalTheory.CompanionTheory.SW.FibreGlue
