-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.integrable_and_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:54.877258+00:00
-- url     : https://prove2.me/submissions/f5e617fb-37e7-4f20-bf78-d64bd0cb9737

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_orbit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_continuous_smul_fib
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_exists_compact_fib

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
theorem _root_.solution [T2Space V] {g : V → X} (hg : Continuous g) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) {w : Q → ℝ≥0} (hw : Continuous w)
    (m : Measure (g ⁻¹' {b₀})) [IsLocallyFiniteMeasure m] {φ : V → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    (∀ b ∈ Set.range (fun q : Q => q • b₀), Integrable φ (fibFam g b₀ w m b)) ∧
      ContinuousOn (fun b => ∫ v, φ v ∂(fibFam g b₀ w m b))
        (Set.range (fun q : Q => q • b₀)) := by
  have hvan : ∀ {K : Set Q} {k : Set (g ⁻¹' {b₀})},
      (∀ q ∈ K, ∀ z : (g ⁻¹' {b₀}), q • (z : V) ∈ tsupport φ → z ∈ k) →
      ∀ q, ∀ z : (g ⁻¹' {b₀}), q ∈ K → z ∉ k → φ (q • (z : V)) = 0 := by
    intro K k hk q z hq hz
    by_contra hne
    exact hz (hk q hq z (subset_tsupport _ hne))
  have hint : ∀ q : Q, Integrable (fun z : (g ⁻¹' {b₀}) => φ (q • (z : V))) m := by
    intro q
    obtain ⟨k, hk, hkz⟩ := exists_compact_fib hg b₀ (isCompact_singleton (x := q)) hφc
    refine (hφ.comp (continuous_smul_fib g b₀ q)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hk fun z hz => ?_
    exact hvan hkz q z rfl hz
  have hval : ∀ q : Q, ∫ v, φ v ∂(fibFam g b₀ w m (q • b₀)) =
      (w q : ℝ) * ∫ z, φ (q • (z : V)) ∂m := by
    intro q
    rw [fibFam_orbit w m ho.injective, integral_smul_measure,
      integral_map (continuous_smul_fib g b₀ q).aemeasurable hφ.aestronglyMeasurable]
    simp
  have hG : Continuous (fun q : Q => ∫ z, φ (q • (z : V)) ∂m) := by
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds q₀
    obtain ⟨k, hk, hkz⟩ := exists_compact_fib hg b₀ hK hφc
    have hcont : ContinuousOn (fun q : Q => ∫ z, φ (q • (z : V)) ∂m) K := by
      refine continuousOn_integral_of_compact_support
        (f := fun (q : Q) (z : (g ⁻¹' {b₀})) => φ (q • (z : V))) hk ?_ ?_
      · exact (hφ.comp (continuous_fst.smul
          (continuous_subtype_val.comp continuous_snd))).continuousOn
      · intro q z hq hz
        exact hvan hkz q z hq hz
    exact hcont.continuousAt hKn
  constructor
  · rintro b ⟨q, rfl⟩
    change Integrable φ (fibFam g b₀ w m (q • b₀))
    rw [fibFam_orbit w m ho.injective]
    refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
    exact (integrable_map_measure hφ.aestronglyMeasurable
      (continuous_smul_fib g b₀ q).aemeasurable).2 (hint q)
  · rintro b ⟨q, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    refine (ho.continuousAt_iff).1 ?_
    have : ((fun b => ∫ v, φ v ∂(fibFam g b₀ w m b)) ∘ fun q : Q => q • b₀) =
        fun q : Q => (w q : ℝ) * ∫ z, φ (q • (z : V)) ∂m := funext hval
    rw [this]
    exact ((NNReal.continuous_coe.comp hw).mul hG).continuousAt
end GlobalTheory.CompanionTheory.SW.Slice
