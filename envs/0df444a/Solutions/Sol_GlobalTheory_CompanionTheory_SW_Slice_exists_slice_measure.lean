-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.exists_slice_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:51.081649+00:00
-- url     : https://prove2.me/submissions/1f184635-2a22-445a-bd88-350223049ee5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_comap_map_of_intertwine
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_withDensity_map_of_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_comap_isLocallyFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_theta_isOpenEmbedding
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_measure_eq_haar_prod_of_left_invariant


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
theorem _root_.solution [T2Space V] [LocallyCompactSpace V] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (χ χ' : Q →* ℝ≥0) (hχ : Continuous χ) (hχ' : Continuous χ')
    (hμ : ∀ q : Q, μ.map (fun v => q • v) = χ q • μ)
    (hν : ∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) :
    ∃ m : Measure (g ⁻¹' {b₀}), IsLocallyFiniteMeasure m ∧
      (μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞)) =
        ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))).prod m := by
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  haveI : LocallyCompactSpace (g ⁻¹' {b₀}) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hΘ, -⟩ := theta_isOpenEmbedding (Q := Q) hg heq ho
  have hΘm := hΘ.measurableEmbedding
  have hom := ho.measurableEmbedding
  have hinvmul : ∀ (c : Q →* ℝ≥0) (a : Q), ((c a⁻¹ : ℝ≥0) : ℝ≥0∞) * (c a : ℝ≥0) = 1 := by
    intro c a
    rw [← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one]
  have hsc : ∀ (c : Q →* ℝ≥0) (a q : Q), ((c q : ℝ≥0) : ℝ≥0∞) =
      (c a⁻¹ : ℝ≥0) * (c (a * q) : ℝ≥0) := by
    intro c a q
    rw [← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_left]
  haveI := comap_isLocallyFinite hΘ μ
  haveI := comap_isLocallyFinite ho ν
  set η := (ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞)) with hη
  haveI hηf : IsLocallyFiniteMeasure η := IsLocallyFiniteMeasure.withDensity_coe hχ'
  have hηinv : η.IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    refine withDensity_map_of_scale (measurable_const_mul a) _ (χ' a) (χ' a⁻¹) ?_
      (measurable_coe_nnreal_ennreal.comp hχ'.measurable) (hsc χ' a) (hinvmul χ' a)
    refine comap_map_of_intertwine hom (measurable_const_mul a) (L' := fun q => a⁻¹ * q)
      (A := fun x => a • x) (A' := fun x => a⁻¹ • x) (measurable_const_smul a)
      (fun q => mul_inv_cancel_left a q) (fun x => inv_smul_smul a x)
      (fun q => mul_smul _ _ _) (fun q => mul_smul _ _ _) ν _ ?_
    rw [hν a, ENNReal.smul_def]
  have hν₀ : (ν.comap (fun q : Q => q • b₀)).IsOpenPosMeasure := by
    refine ⟨fun s hs hne h0 => ?_⟩
    rw [hom.comap_apply] at h0
    exact (ho.isOpenMap s hs).measure_pos ν (hne.image _) |>.ne' h0
  have hηpos : η.IsOpenPosMeasure := by
    have hac : (ν.comap (fun q : Q => q • b₀)) ≪ η := by
      refine withDensity_absolutelyContinuous'
        (measurable_coe_nnreal_ennreal.comp hχ'.measurable).aemeasurable
        (Filter.Eventually.of_forall fun q => ?_)
      intro h0
      have := hinvmul χ' q
      rw [ENNReal.coe_eq_zero.1 h0] at this
      simp at this
    exact hac.isOpenPosMeasure
  haveI : η.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := hηinv
      toIsOpenPosMeasure := hηpos }
  haveI : IsLocallyFiniteMeasure
      ((μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe (f := fun p : Q × (g ⁻¹' {b₀}) => χ p.1)
      (hχ.comp continuous_fst)
  refine GlobalTheory.CompanionTheory.SW.measure_eq_haar_prod_of_left_invariant Q (g ⁻¹' {b₀}) η _ fun a => ?_
  have hLm : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (a * p.1, p.2)) :=
    (continuous_const.mul continuous_fst).measurable.prodMk measurable_snd
  refine withDensity_map_of_scale hLm _ (χ a) (χ a⁻¹) ?_
    (measurable_coe_nnreal_ennreal.comp (hχ.measurable.comp measurable_fst))
    (fun p => hsc χ a p.1) (hinvmul χ a)
  refine comap_map_of_intertwine hΘm hLm (L' := fun p => (a⁻¹ * p.1, p.2))
    (A := fun x => a • x) (A' := fun x => a⁻¹ • x) (measurable_const_smul a)
    (fun p => by simp) (fun x => inv_smul_smul a x)
    (fun p => mul_smul _ _ _) (fun p => mul_smul _ _ _) μ _ ?_
  rw [hμ a, ENNReal.smul_def]
end GlobalTheory.CompanionTheory.SW.Slice
