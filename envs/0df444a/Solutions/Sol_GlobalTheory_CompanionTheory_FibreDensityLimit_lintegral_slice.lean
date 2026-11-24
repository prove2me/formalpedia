-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibreDensityLimit.lintegral_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:05.12882+00:00
-- url     : https://prove2.me/submissions/ff1a89ef-55cd-4ccf-a306-b8d420e458a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
theorem _root_.solution (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {w : V → ℝ≥0∞}
    (hw : Measurable w) (hw0 : ∀ v, v ∉ U → w v = 0) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), w v ∂μ = ∫⁻ s in A, ∫⁻ v, w v ∂(fib s) ∂ν := by
  have hpre : f ⁻¹' (ι '' A) = g ⁻¹' A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hfg]
    exact ⟨fun ⟨x, hx, he⟩ => hι he ▸ hx, fun hv => ⟨g v, hv, rfl⟩⟩
  rw [hpre]
  have hgA : MeasurableSet (g ⁻¹' A) := hg hA
  rw [← lintegral_indicator hgA, ← lintegral_indicator hA]
  have hsupp : Function.support ((g ⁻¹' A).indicator w) ⊆ U := by
    intro v hv
    by_contra hU
    apply hv
    simp [Set.indicator, hw0 v hU]
  rw [← setLIntegral_eq_of_support_subset hsupp, h.2.1 _ (hw.indicator hgA)]
  refine lintegral_congr fun s => ?_
  have hae : ∀ᵐ v ∂(fib s), v ∈ f ⁻¹' {ι s} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s)
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_mem (show v ∈ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]
  · rw [Set.indicator_of_notMem hs]
    refine (lintegral_congr_ae (hae.mono fun v hv => ?_)).trans lintegral_zero
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_notMem (show v ∉ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]
end GlobalTheory.CompanionTheory.FibreDensityLimit
