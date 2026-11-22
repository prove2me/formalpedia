-- Prove2me | solution 1 for MasulloGRH.sAdditiveTamagawa_isAddHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:22:34.244147+00:00
-- url     : https://prove2.me/submissions/6088f176-46c4-4b41-804c-a8c46d0a5d0b

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The `S`-local additive Tamagawa measure is a Haar measure

`ν_S = (⊗_{w ∣ ∞} ν_w) ⊗ (⊗_{v ∈ S_f} ν_v)` is a product of finitely many σ-finite Haar measures,
hence a Haar measure of the product group.

* At an infinite place `ν_w` is the image of Lebesgue measure on `ℝ`, or of twice Lebesgue measure
  on `ℂ`, under a ring isomorphism which is an isometry.
* At a finite place `ν_v` is Haar by the platform theorem
  `RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar`.
* Every completion is second countable and locally compact (at a finite place by the platform
  theorem `RiemannMasullo.locallyCompactSpace_adicCompletion`), hence σ-compact, so each `ν_v` is
  σ-finite.
-/

namespace Sol_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure

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

end Sol_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure

open MasulloGRH Sol_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (sAdditiveTamagawa F Sf).IsAddHaarMeasure := by
  -- topology of the factors: second countable and locally compact
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  -- the local factors are Haar measures
  have hinf : ∀ w : InfinitePlace F,
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infinite_haar F
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    fun v => RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  -- a Haar measure of a σ-compact group is σ-finite
  have hsf_inf : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) :=
    fun w => inferInstance
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F),
      SigmaFinite (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) :=
    fun v => inferInstance
  -- the two finite products are Haar measures
  have h1 : (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have h2 : (Measure.pi fun v : Sf => RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F
      (v : HeightOneSpectrum (𝓞 F))).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have h1' : (infiniteAdditiveTamagawa F).IsAddHaarMeasure := h1
  have hs1 : SigmaFinite (infiniteAdditiveTamagawa F) :=
    inferInstanceAs
      (SigmaFinite (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)))
  have hm1 : MeasurableAdd (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableAdd ((w : InfinitePlace F) → w.Completion))
  -- and so is their product
  unfold sAdditiveTamagawa
  exact Measure.prod.instIsAddHaarMeasure _ _
