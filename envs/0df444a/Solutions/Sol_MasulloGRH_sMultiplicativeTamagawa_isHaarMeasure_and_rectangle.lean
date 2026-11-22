-- Prove2me | solution 1 for MasulloGRH.sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:34:19.043118+00:00
-- url     : https://prove2.me/submissions/c9d83328-0925-4301-ae89-db9047d2c30e

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar
import Theorems.Thm_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The `S`-local multiplicative Tamagawa measure is the product of the local ones

* `rectangle`: the product formula `μ_S(∏ B_v) = ∏ μ_v(B_v)` on Borel rectangles.  The density of
  `μ_S` is the product of the local densities and `ν_S` is the product of the `ν_v`, so this is
  Tonelli's theorem (`setLIntegral_pi_prod`, `lintegral_prod_mul`).
* `haar`: `μ_S` is a Haar measure.  By the product formula and the uniqueness of a σ-finite measure
  with given values on rectangles, `μ_S` is the image of `⊗_{v ∈ S} μ_v` under the isomorphism of
  topological groups `∏ F_vˣ ≃ GL₁(𝔸_{F,S})`; the local measures are Haar by the platform theorems
  `MasulloGRH.infiniteLocalMulTamagawa_isHaarMeasure` and
  `MasulloGRH.finiteLocalMulTamagawa_isHaarMeasure_and_units`.
-/

namespace Sol_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle

/-- Tonelli for a finite product: the integral of a product of functions of the individual
coordinates is the product of the integrals. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (x₀ : ∀ i, X i) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  classical
  have hF : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ∀ i, X i,
      (∫⋯∫⁻_s, (fun x : ∀ i, X i => ∏ i, f i (x i)) ∂μ) x =
        (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * ∏ i ∈ sᶜ, f i (x i) := by
    intro s
    induction s using Finset.induction with
    | empty => intro x; simp
    | insert j s hj ih =>
      intro x
      rw [lmarginal_insert _ hF hj]
      have hcompl : sᶜ = insert j (insert j s)ᶜ := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [hij]
      have hjc : j ∉ (insert j s)ᶜ := by simp
      have hint : ∀ t : X j, (∫⋯∫⁻_s, (fun x : ∀ i, X i => ∏ i, f i (x i)) ∂μ)
          (Function.update x j t) =
          (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * (f j t * ∏ i ∈ (insert j s)ᶜ, f i (x i)) := by
        intro t
        rw [ih, hcompl, Finset.prod_insert hjc, Function.update_self]
        congr 2
        refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j := fun h => hjc (h ▸ hi)
        rw [Function.update_of_ne hij]
      simp_rw [hint]
      rw [lintegral_const_mul _ ((hf j).mul_const _), lintegral_mul_const _ (hf j),
        Finset.prod_insert hj]
      ring
  rw [lintegral_eq_lmarginal_univ x₀, key]
  simp

/-- Tonelli for a finite product, over a rectangle. -/
theorem setLIntegral_pi_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (s : ∀ i, Set (X i)) (x₀ : ∀ i, X i) :
    ∫⁻ x in Set.pi Set.univ s, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t in s i, f i t ∂μ i := by
  rw [Measure.restrict_pi_pi]
  exact lintegral_pi_prod (fun i => (μ i).restrict (s i)) f hf x₀

/-- For finitely many topological monoids with open unit groups, the coordinatewise inclusion
`∏ Mᵢˣ → ∏ Mᵢ` is an open embedding. -/
theorem isOpenEmbedding_pi_units_val {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsOpenUnits (M i)] :
    Topology.IsOpenEmbedding (fun (u : ∀ i, (M i)ˣ) (i : ι) => (u i : M i)) := by
  have h : ∀ i, Topology.IsOpenEmbedding (Units.val : (M i)ˣ → M i) :=
    fun i => IsOpenUnits.isOpenEmbedding_unitsVal
  exact ⟨Topology.IsEmbedding.piMap fun i => (h i).isEmbedding,
    (IsOpenMap.piMap (fun i => (h i).isOpenMap)
      (Filter.eventually_cofinite.mpr (Set.toFinite _))).isOpen_range⟩

open MasulloGRH InfinitePlace.Completion

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
/-- The completion at an infinite place embeds isometrically in `ℂ`, so it is second countable. -/
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

/-- A number field is countable: all its elements are algebraic over `ℚ`. -/
theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

/-- The completion at a finite place is a metric space in which the countable field `F` is dense,
so it is second countable. -/
theorem secondCountable_finite (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

omit [NumberField F] in
/-- The local additive Tamagawa measure at an infinite place is a Haar measure: it is the image of
(a positive multiple of) Lebesgue measure under an isomorphism of topological groups. -/
theorem infinite_haar (w : InfinitePlace F) :
    (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- The coordinates of an `S`-idele: the isomorphism `GL₁(𝔸_{F,S}) ≃ ∏_{w ∣ ∞} F_wˣ × ∏_{v ∈ S_f} F_vˣ`. -/
noncomputable def coordEquiv : SIdeleGroup F Sf ≃*
    ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :=
  (MulEquiv.prodUnits (M := (w : InfinitePlace F) → w.Completion)
      (N := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).trans
    (MulEquiv.prodCongr MulEquiv.piUnits MulEquiv.piUnits)

theorem continuous_coordEquiv : Continuous (coordEquiv F Sf) :=
  ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).continuous.prodMap
    (ContinuousMulEquiv.piUnits
      (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous).comp
    (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous

theorem continuous_coordEquiv_symm : Continuous (coordEquiv F Sf).symm :=
  (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous.comp
    ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.continuous.prodMap
      (ContinuousMulEquiv.piUnits
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous)

/-- The coordinatewise inclusion `∏ F_wˣ × ∏ F_vˣ → 𝔸_{F,S}`. -/
noncomputable def coordVal (p : ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)) : SAdeleRing F Sf :=
  (fun w => (p.1 w : w.Completion), fun v => (p.2 v : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

theorem coordVal_coordEquiv (g : SIdeleGroup F Sf) :
    coordVal F Sf (coordEquiv F Sf g) = (g : SAdeleRing F Sf) := rfl

theorem val_coordEquiv_symm (p : ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)) :
    (((coordEquiv F Sf).symm p : SIdeleGroup F Sf) : SAdeleRing F Sf) = coordVal F Sf p := rfl

/-- `GL₁(𝔸_{F,S})` is an open subset of `𝔸_{F,S}` with the subspace topology. -/
theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) := by
  have h1 : Topology.IsOpenEmbedding (coordVal F Sf) :=
    (isOpenEmbedding_pi_units_val (M := fun w : InfinitePlace F => w.Completion)).prodMap
      (isOpenEmbedding_pi_units_val
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))
  have h2 : Topology.IsOpenEmbedding (coordEquiv F Sf) :=
    (Homeomorph.mk (coordEquiv F Sf).toEquiv (continuous_coordEquiv F Sf)
      (continuous_coordEquiv_symm F Sf)).isOpenEmbedding
  exact h1.comp h2

/-- The product formula on Borel rectangles, by Tonelli's theorem. -/
theorem rectangle
    (A : (w : InfinitePlace F) → Set w.Completionˣ)
    (B : (v : Sf) → Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)
    (hA : ∀ w, MeasurableSet (A w)) (hB : ∀ v, MeasurableSet (B v)) :
    sMultiplicativeTamagawa F Sf
        {g | (∀ w : InfinitePlace F, ∃ a ∈ A w, (a : w.Completion) = (g : SAdeleRing F Sf).1 w) ∧
          ∀ v : Sf, ∃ b ∈ B v,
            (b : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = (g : SAdeleRing F Sf).2 v} =
      (∏ w : InfinitePlace F, infiniteLocalMulTamagawa F w (A w)) *
        ∏ v : Sf, finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F)) (B v) := by
  -- topology of the factors
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  -- the local additive measures are σ-finite Haar measures
  have hinf : ∀ w : InfinitePlace F,
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infinite_haar F
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    fun v => RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hsf_inf : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) :=
    fun w => inferInstance
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F),
      SigmaFinite (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) :=
    fun v => inferInstance
  have hs1 : SigmaFinite (infiniteAdditiveTamagawa F) :=
    inferInstanceAs
      (SigmaFinite (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)))
  -- Borel structures
  have hsc1 : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  have hb1 : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  have hbX : BorelSpace (SAdeleRing F Sf) := inferInstance
  -- measurable embeddings of the unit groups
  have hembX : MeasurableEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) :=
    (isOpenEmbedding_val F Sf).measurableEmbedding
  have hval_inf : ∀ w : InfinitePlace F,
      MeasurableEmbedding (Units.val : w.Completionˣ → w.Completion) :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hval_fin : ∀ v : HeightOneSpectrum (𝓞 F),
      MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    fun v => (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).measurableEmbedding
  -- the image of the rectangle in `𝔸_{F,S}` is a rectangle
  set P : Set (InfiniteAdeleRing F) := Set.pi Set.univ fun w => Units.val '' A w with hP
  set Q : Set ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :=
    Set.pi Set.univ fun v => Units.val '' B v with hQ
  have hPm : MeasurableSet P :=
    MeasurableSet.univ_pi fun w => (hval_inf w).measurableSet_image.mpr (hA w)
  have hQm : MeasurableSet Q :=
    MeasurableSet.univ_pi fun v => (hval_fin v).measurableSet_image.mpr (hB v)
  have himg : (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) ''
      {g | (∀ w : InfinitePlace F, ∃ a ∈ A w, (a : w.Completion) = (g : SAdeleRing F Sf).1 w) ∧
          ∀ v : Sf, ∃ b ∈ B v,
            (b : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = (g : SAdeleRing F Sf).2 v} =
      P ×ˢ Q := by
    ext x
    constructor
    · rintro ⟨g, ⟨hgA, hgB⟩, rfl⟩
      refine ⟨fun w _ => ?_, fun v _ => ?_⟩
      · obtain ⟨a, ha, hag⟩ := hgA w
        exact ⟨a, ha, hag⟩
      · obtain ⟨b, hb, hbg⟩ := hgB v
        exact ⟨b, hb, hbg⟩
    · rintro ⟨hx1, hx2⟩
      choose a ha hax using fun w => hx1 w (Set.mem_univ w)
      choose b hb hbx using fun v => hx2 v (Set.mem_univ v)
      refine ⟨(coordEquiv F Sf).symm (a, b),
        ⟨fun w => ⟨a w, ha w, rfl⟩, fun v => ⟨b v, hb v, rfl⟩⟩, ?_⟩
      rw [val_coordEquiv_symm]
      exact Prod.ext (funext hax) (funext hbx)
  -- the local densities
  set ρ : (w : InfinitePlace F) → w.Completion → ℝ≥0∞ :=
    fun w t => ((‖t‖₊ : ℝ≥0∞) ^ w.mult)⁻¹ with hρ
  set σ : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F → ℝ≥0∞ :=
    fun v t => (‖t‖₊ : ℝ≥0∞)⁻¹ with hσ
  have hρm : ∀ w, Measurable (ρ w) := fun w => by
    simp only [hρ]
    fun_prop
  have hσm : ∀ v, Measurable (σ v) := fun v => by
    simp only [hσ]
    fun_prop
  -- the density of `μ_S` is the product of the local densities
  have hdens : (fun x : SAdeleRing F Sf =>
      ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
        ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹) =
      fun x : SAdeleRing F Sf => (∏ w, ρ w (x.1 w)) * ∏ v, σ v (x.2 v) := by
    funext x
    have h1 : (∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) ≠ ⊤ :=
      ENNReal.prod_ne_top fun w _ => ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h2 : (∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.prod_ne_top fun v _ => ENNReal.coe_ne_top
    rw [ENNReal.mul_inv (Or.inr h2) (Or.inl h1),
      ENNReal.prod_inv_distrib fun w _ w' _ _ =>
        Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      ENNReal.prod_inv_distrib fun v _ v' _ _ => Or.inr ENNReal.coe_ne_top]
  -- Tonelli
  have hT1 : ∫⁻ y in P, ∏ w, ρ w (y w) ∂(infiniteAdditiveTamagawa F) =
      ∏ w, ∫⁻ t in Units.val '' A w, ρ w t
        ∂(RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) :=
    setLIntegral_pi_prod (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F) ρ hρm _
      (fun _ => 0)
  have hT2 : ∫⁻ z in Q, ∏ v, σ v (z v) ∂(Measure.pi fun v : Sf =>
        RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) =
      ∏ v : Sf, ∫⁻ t in Units.val '' B v, σ v t
        ∂(RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) :=
    setLIntegral_pi_prod _ σ hσm _ (fun _ => 0)
  have hm1 : Measurable fun y : InfiniteAdeleRing F => ∏ w, ρ w (y w) :=
    Finset.measurable_prod _ fun w _ => (hρm w).comp (measurable_pi_apply w)
  have hm2 : Measurable fun z : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F =>
      ∏ v, σ v (z v) :=
    Finset.measurable_prod _ fun v _ => (hσm v).comp (measurable_pi_apply v)
  have hT : ∫⁻ x in P ×ˢ Q, (∏ w, ρ w (x.1 w)) * ∏ v, σ v (x.2 v) ∂(sAdditiveTamagawa F Sf) =
      (∏ w, ∫⁻ t in Units.val '' A w, ρ w t
        ∂(RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w)) *
      ∏ v : Sf, ∫⁻ t in Units.val '' B v, σ v t
        ∂(RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) := by
    rw [sAdditiveTamagawa, ← Measure.prod_restrict, ← hT1, ← hT2]
    exact lintegral_prod_mul (f := fun y : InfiniteAdeleRing F => ∏ w, ρ w (y w))
      (g := fun z : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F => ∏ v, σ v (z v))
      hm1.aemeasurable hm2.aemeasurable
  -- the local measures of the sides
  have hloc_inf : ∀ w : InfinitePlace F, infiniteLocalMulTamagawa F w (A w) =
      ∫⁻ t in Units.val '' A w, ρ w t
        ∂(RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := by
    intro w
    rw [infiniteLocalMulTamagawa, (hval_inf w).comap_apply,
      withDensity_apply _ ((hval_inf w).measurableSet_image.mpr (hA w))]
  have hloc_fin : ∀ v : Sf, finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F)) (B v) =
      ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0∞) /
        ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0∞) - 1)) *
      ∫⁻ t in Units.val '' B v, σ v t
        ∂(RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) := by
    intro v
    rw [finiteLocalMulTamagawa, Measure.smul_apply, smul_eq_mul, (hval_fin v).comap_apply,
      withDensity_apply _ ((hval_fin v).measurableSet_image.mpr (hB v))]
  rw [sMultiplicativeTamagawa, Measure.smul_apply, smul_eq_mul, hembX.comap_apply, himg,
    withDensity_apply _ (hPm.prod hQm), hdens, hT]
  simp_rw [hloc_inf, hloc_fin]
  rw [Finset.prod_mul_distrib, ← Finset.prod_coe_sort Sf
    (fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ≥0∞) /
      ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))]
  ring

/-- `μ_S` is the image of the product of the local multiplicative Tamagawa measures under the
isomorphism `∏ F_wˣ × ∏ F_vˣ ≃ GL₁(𝔸_{F,S})`, hence a Haar measure. -/
theorem haar : (sMultiplicativeTamagawa F Sf).IsHaarMeasure := by
  -- topology of the factors
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  have hscu_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have hscu_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F)ˣ :=
    fun v => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := v.adicCompletion F)).isEmbedding.secondCountableTopology
  -- the local multiplicative measures are σ-finite Haar measures
  have hinf : ∀ w : InfinitePlace F, (infiniteLocalMulTamagawa F w).IsHaarMeasure :=
    fun w => infiniteLocalMulTamagawa_isHaarMeasure F w
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (finiteLocalMulTamagawa F v).IsHaarMeasure :=
    fun v => (finiteLocalMulTamagawa_isHaarMeasure_and_units F v).1
  have hsf_inf : ∀ w : InfinitePlace F, SigmaFinite (infiniteLocalMulTamagawa F w) :=
    fun w => inferInstance
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (finiteLocalMulTamagawa F v) :=
    fun v => inferInstance
  -- the product measure is a Haar measure of the product group
  set π : Measure (((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)) :=
    (Measure.pi (infiniteLocalMulTamagawa F)).prod
      (Measure.pi fun v : Sf => finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F))) with hπ
  have hπH : π.IsHaarMeasure := by
    rw [hπ]
    infer_instance
  have hme : Measurable (coordEquiv F Sf) := (continuous_coordEquiv F Sf).measurable
  have hme' : Measurable (coordEquiv F Sf).symm := (continuous_coordEquiv_symm F Sf).measurable
  -- `μ_S` and the product measure agree on rectangles
  have key : π = (sMultiplicativeTamagawa F Sf).map (coordEquiv F Sf) := by
    rw [hπ]
    refine Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
      (Measure.FiniteSpanningSetsIn.pi fun w => (infiniteLocalMulTamagawa F w).toFiniteSpanningSetsIn)
      (Measure.FiniteSpanningSetsIn.pi fun v : Sf =>
        (finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F))).toFiniteSpanningSetsIn) ?_
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have hA' : ∀ w, MeasurableSet (A w) := fun w => hA w (Set.mem_univ w)
    have hB' : ∀ v, MeasurableSet (B v) := fun v => hB v (Set.mem_univ v)
    rw [Measure.map_apply hme ((MeasurableSet.univ_pi hA').prod (MeasurableSet.univ_pi hB')),
      Measure.pi_pi, Measure.pi_pi, ← rectangle F Sf A B hA' hB']
    congr 1
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun w => ⟨_, h1 w (Set.mem_univ w), rfl⟩, fun v => ⟨_, h2 v (Set.mem_univ v), rfl⟩⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun w _ => ?_, fun v _ => ?_⟩
      · obtain ⟨a, ha, hag⟩ := h1 w
        have : a = (coordEquiv F Sf g).1 w := Units.ext hag
        exact this ▸ ha
      · obtain ⟨b, hb, hbg⟩ := h2 v
        have : b = (coordEquiv F Sf g).2 v := Units.ext hbg
        exact this ▸ hb
  have hμ : sMultiplicativeTamagawa F Sf = π.map (coordEquiv F Sf).symm := by
    rw [key, Measure.map_map hme' hme]
    have : (coordEquiv F Sf).symm ∘ (coordEquiv F Sf) = id := by
      funext g
      simp
    rw [this, Measure.map_id]
  rw [hμ]
  exact (coordEquiv F Sf).symm.isHaarMeasure_map π (continuous_coordEquiv_symm F Sf)
    (continuous_coordEquiv F Sf)

end Sol_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle

open MasulloGRH Sol_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (sMultiplicativeTamagawa F Sf).IsHaarMeasure ∧
    ∀ (A : (w : InfinitePlace F) → Set w.Completionˣ)
      (B : (v : Sf) → Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ),
      (∀ w, MeasurableSet (A w)) → (∀ v, MeasurableSet (B v)) →
      sMultiplicativeTamagawa F Sf
          {g | (∀ w : InfinitePlace F, ∃ a ∈ A w, (a : w.Completion) = (g : SAdeleRing F Sf).1 w) ∧
            ∀ v : Sf, ∃ b ∈ B v,
              (b : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = (g : SAdeleRing F Sf).2 v} =
        (∏ w : InfinitePlace F, infiniteLocalMulTamagawa F w (A w)) *
          ∏ v : Sf, finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F)) (B v) :=
  ⟨haar F Sf, fun A B hA hB => rectangle F Sf A B hA hB⟩
