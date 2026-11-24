-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.fibFam_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:45.776838+00:00
-- url     : https://prove2.me/submissions/3789853e-0830-4c46-8f3f-468d767e1c58

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_orbit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_off
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_continuous_smul_fib

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
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution {Y : Type} {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι)
    (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (b : X) :
    fibFam g b₀ w m b (f ⁻¹' {ι b} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ = 0 := by
  by_cases hb : b ∈ Set.range (fun q : Q => q • b₀)
  · obtain ⟨q, rfl⟩ := hb
    have hfib : f ⁻¹' {ι (q • b₀)} = g ⁻¹' {q • b₀} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
      exact hι.eq_iff
    have hBm : MeasurableSet (Set.range (fun q : Q => q • b₀)) :=
      ho.isOpen_range.measurableSet
    have hS : MeasurableSet (f ⁻¹' {ι (q • b₀)} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ := by
      rw [hfib]
      exact ((hg.measurable (measurableSet_singleton _)).inter (hg.measurable hBm)).compl
    change fibFam g b₀ w m ((fun q : Q => q • b₀) q) _ = 0
    change fibFam g b₀ w m (q • b₀) _ = 0
    rw [fibFam_orbit w m ho.injective, Measure.smul_apply,
      Measure.map_apply (continuous_smul_fib g b₀ q).measurable hS]
    have : (fun z : (g ⁻¹' {b₀}) => q • (z : V)) ⁻¹'
        (f ⁻¹' {ι (q • b₀)} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ = ∅ := by
      ext z
      have hz : g (z : V) = b₀ := z.2
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff,
        hf, heq, hz, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨trivial, ⟨q, rfl⟩⟩
    rw [this]
    simp
  · rw [fibFam_off w m hb]
    simp
end GlobalTheory.CompanionTheory.SW.Slice
