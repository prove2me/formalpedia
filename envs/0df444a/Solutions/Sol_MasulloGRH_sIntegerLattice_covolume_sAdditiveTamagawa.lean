-- Prove2me | solution 1 for MasulloGRH.sIntegerLattice_covolume_sAdditiveTamagawa
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T13:03:52.344806+00:00
-- url     : https://prove2.me/submissions/2633986e-5bfe-47fa-a305-b7851caaa06d

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain
import Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_existsUnique
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The covolume of the `S`-integers for the `S`-local additive Tamagawa measure

All fundamental domains of the countable group `𝒪_{F,S}` acting by translations on `𝔸_{F,S}` have
the same measure for the translation invariant measure `ν_S`, so it suffices to compute the measure
of the standard domain `D_{F,S} = D_{F,∞} × ∏_{v ∈ S_f} 𝒪_v`:

* `D_{F,S}` is a strict fundamental domain by the platform theorem
  `MasulloGRH.sIntegerFundamentalDomain_existsUnique`;
* `ν_S` is a Haar measure by the platform theorem `MasulloGRH.sAdditiveTamagawa_isAddHaarMeasure`;
* `ν_∞(D_{F,∞}) = √|d_F|`: in the coordinates `ℝ^{r₁} × ℂ^{r₂}` the measure `ν_∞` is `2^{r₂}` times
  Lebesgue measure (`map_mixedSpace`), and the Lebesgue measure of a fundamental parallelepiped of
  the lattice `𝒪_F` is `2^{-r₂} √|d_F|` (Mathlib,
  `NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis`);
* `ν_v(𝒪_v) = N(𝔡_v)^{-1/2}` by the definition of `ν_v` (`finite_mass`).

The two archimedean lemmas `map_mixedSpace` and `infinite_mass` follow the proofs in the open
formalization mccorvie/riemann-masullo (Apache-2.0).
-/

namespace Sol_MasulloGRH_sIntegerLattice_covolume_sAdditiveTamagawa

open MasulloGRH InfinitePlace.Completion

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
/-- The completion at an infinite place embeds isometrically in `ℂ`, so it is second countable. -/
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

omit [NumberField F] in
/-- The local additive Tamagawa measure at an infinite place is a Haar measure. -/
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

open scoped Classical in
/-- In mixed real and complex coordinates, the archimedean product measure is Lebesgue
measure multiplied by two for each complex place. -/
theorem map_mixedSpace :
    (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      ((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) •
        (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  let μ := RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F
  have hsc : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion :=
    secondCountable_infinite F
  have hhaar : ∀ v : InfinitePlace F, (μ v).IsAddHaarMeasure := infinite_haar F
  have hsf : ∀ v : InfinitePlace F, SigmaFinite (μ v) := fun v => inferInstance
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun v ↦ v.IsReal)
  let reindex : {v : InfinitePlace F // ¬ v.IsReal} ≃ {v : InfinitePlace F // v.IsComplex} :=
    Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      MeasurePreserving (ringEquivRealOfIsReal v.2) (μ v) volume := by
    let e := (isometryEquivRealOfIsReal v.2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos v.2]
    change (volume.map e.symm).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hc (v : {v : InfinitePlace F // ¬ v.IsReal}) :
      MeasurePreserving (ringEquivComplexOfIsComplex (reindex v).2)
        (μ v) ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    let e := (isometryEquivComplexOfIsComplex (reindex v).2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg v.2]
    change (Measure.map e.symm (2 • (volume : Measure ℂ))).map e = _
    rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0) • volume by simp [two_smul]]
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hright := (measurePreserving_piCongrLeft
    (fun _ : {v : InfinitePlace F // v.IsComplex} ↦ (2 : ℝ≥0) • (volume : Measure ℂ)) reindex).comp
      (measurePreserving_pi (ι := {v : InfinitePlace F // ¬ v.IsReal}) _ _ hc)
  let μreal := fun v : {v : InfinitePlace F // v.IsReal} ↦ μ v
  let μcomplex := fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ μ v
  have hsfr : ∀ v : {v : InfinitePlace F // v.IsReal}, SigmaFinite (μreal v) :=
    fun v => hsf v.val
  have hsfc : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, SigmaFinite (μcomplex v) :=
    fun v => hsf v.val
  have hpr : SigmaFinite (Measure.pi μreal) := Measure.pi.sigmaFinite μreal
  have hpc : SigmaFinite (Measure.pi μcomplex) := Measure.pi.sigmaFinite μcomplex
  have hleft := measurePreserving_pi μreal (fun _ ↦ volume) hr
  have hmap := (hleft.prod (μc := Measure.pi μcomplex) hright).comp hsplit
  let μr : Measure ({v : InfinitePlace F // v.IsReal} → ℝ) := volume
  let μc : Measure ({v : InfinitePlace F // v.IsComplex} → ℂ) := volume
  let k : ℝ≥0 := 2 ^ InfinitePlace.nrComplexPlaces F
  have hpow : (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
      (2 : ℝ≥0) • (volume : Measure ℂ)) = k • μc := by
    apply Measure.pi_eq
    intro T hT
    rw [Measure.coe_nnreal_smul_apply, show μc = Measure.pi (fun _ ↦ volume) from volume_pi,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply, k, ENNReal.coe_pow, ENNReal.coe_ofNat,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, InfinitePlace.nrComplexPlaces]
  have hmap' : (Measure.pi μ).map (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      μr.prod (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
        (2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [show μr = Measure.pi (fun _ ↦ volume) from volume_pi]
    exact hmap.map_eq
  rw [hmap', hpow]
  have hk : (k : ℝ≥0∞) = (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F := by simp [k]
  rw [← hk, ← ENNReal.smul_def]
  change μr.prod (k • μc) = k • μr.prod μc
  refine Measure.prod_eq fun U V _ _ ↦ ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.coe_nnreal_smul_apply,
    mul_left_comm]

/-- The archimedean fundamental domain of the integral basis `RingOfIntegers.basis F` is measurable
and has Tamagawa mass `√|d_F|`. -/
theorem infinite_mass :
    MeasurableSet (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) ∧
      Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)
          (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) =
        ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let D := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
  have hsc : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion :=
    secondCountable_infinite F
  have hbs : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
  have he : Continuous e := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  have hD : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
  have hB : RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) = e ⁻¹' D := by
    unfold RiemannMasullo.infiniteAdeleFundamentalDomain
    dsimp only [D]
    congr 2
    apply DFunLike.ext
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply,
      mixedEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  have hmap : (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)) (e ⁻¹' D) =
      ((Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F)) D :=
    (Measure.map_apply he.measurable hD).symm
  have hval : ((Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F)) D = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [map_mixedSpace, Measure.smul_apply, smul_eq_mul,
      mixedEmbedding.volume_fundamentalDomain_latticeBasis]
    rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, one_mul]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  rw [hB]
  exact ⟨hD.preimage he.measurable, hmap.trans hval⟩

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

/-- The local additive Tamagawa measure at a finite place gives the ring of local integers the
mass `N(𝔡_v)^{-1/2}`. -/
theorem finite_mass (v : HeightOneSpectrum (𝓞 F)) :
    RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  have hlc : LocallyCompactSpace (v.adicCompletion F) :=
    RiemannMasullo.locallyCompactSpace_adicCompletion v
  have hhaar : (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hne : (v.adicCompletionIntegers F : Set (v.adicCompletion F)).Nonempty :=
    ⟨0, zero_mem _⟩
  have hpos : 0 < RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hO.measure_pos _ hne
  have hμpos : 0 < Measure.addHaar (G := v.adicCompletion F)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hO.measure_pos _ hne
  have hval : RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      ((ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ /
        Measure.addHaar (G := v.adicCompletion F)
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))) *
        Measure.addHaar (G := v.adicCompletion F)
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := rfl
  have hμtop : Measure.addHaar (G := v.adicCompletion F)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ := by
    intro htop
    rw [hval, htop, ENNReal.div_top, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [hval]
  exact ENNReal.div_mul_cancel hμpos.ne' hμtop

/-- The diagonal image of the `S`-integers is a countable group. -/
theorem countable_sIntegerLattice (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Countable (sIntegerLattice Sf) := by
  have : Countable F := countable_numberField F
  have h : (sIntegerLattice Sf : Set (SAdeleRing F Sf)).Countable := by
    rw [sIntegerLattice, AddSubgroup.coe_map]
    exact (Set.to_countable _).image _
  exact h.to_subtype

/-- The standard domain `D_{F,S}` is a strict fundamental domain: every `S`-adele has exactly one
translate by an element of the lattice in it. -/
theorem existsUnique_vadd_mem {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) :
    ∃! g : sIntegerLattice Sf, g +ᵥ x ∈ sIntegerFundamentalDomain F b Sf := by
  obtain ⟨ξ, ⟨hξ, hx⟩, huniq⟩ := sIntegerFundamentalDomain_existsUnique F b Sf x
  have hmem : ∀ η : F, η ∈ SIntegers (F := F) Sf → sDiagonal Sf η ∈ sIntegerLattice Sf :=
    fun η hη => ⟨η, hη, rfl⟩
  refine ⟨⟨-sDiagonal Sf ξ, neg_mem (hmem ξ hξ)⟩, ?_, ?_⟩
  · change -sDiagonal Sf ξ + x ∈ sIntegerFundamentalDomain F b Sf
    rw [neg_add_eq_sub]
    exact hx
  · rintro ⟨g, η, hη, rfl⟩ hgx
    have hgx' : sDiagonal Sf η + x ∈ sIntegerFundamentalDomain F b Sf := hgx
    have h1 : -η = ξ := by
      refine huniq (-η) ⟨neg_mem hη, ?_⟩
      rw [map_neg, sub_neg_eq_add, add_comm]
      exact hgx'
    apply Subtype.ext
    change sDiagonal Sf η = -sDiagonal Sf ξ
    rw [← h1, map_neg, neg_neg]

end Sol_MasulloGRH_sIntegerLattice_covolume_sAdditiveTamagawa

open MasulloGRH Sol_MasulloGRH_sIntegerLattice_covolume_sAdditiveTamagawa in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (D : Set (SAdeleRing F Sf))
    (hD : IsAddFundamentalDomain (sIntegerLattice Sf) D (sAdditiveTamagawa F Sf)) :
    sAdditiveTamagawa F Sf D =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) *
        ∏ v ∈ Sf, (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  -- topology of the factors: second countable and locally compact
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  -- the local factors are σ-finite Haar measures
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
  have hm1 : MeasurableAdd (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableAdd ((w : InfinitePlace F) → w.Completion))
  -- the measure is translation invariant and the lattice is countable
  have hhaar : (sAdditiveTamagawa F Sf).IsAddHaarMeasure := sAdditiveTamagawa_isAddHaarMeasure F Sf
  have hcount : Countable (sIntegerLattice Sf) := countable_sIntegerLattice F Sf
  have hmeasadd : MeasurableConstVAdd (sIntegerLattice Sf) (SAdeleRing F Sf) := by
    refine ⟨fun c => ?_⟩
    change Measurable fun x : SAdeleRing F Sf =>
      ((c : SAdeleRing F Sf).1 + x.1, (c : SAdeleRing F Sf).2 + x.2)
    exact ((measurable_const_add _).comp measurable_fst).prodMk
      ((measurable_const_add _).comp measurable_snd)
  -- the standard fundamental domain `D_{F,S} = D_{F,∞} × ∏_{v ∈ S_f} 𝒪_v`
  have hprod : sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf =
      (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) ×ˢ
        (Set.univ.pi fun v : Sf =>
          (((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F : Set
            ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v _ => h2 v⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v => h2 v (Set.mem_univ v)⟩
  have hmeas : MeasurableSet (sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf) := by
    rw [hprod]
    exact (infinite_mass F).1.prod (MeasurableSet.univ_pi fun v =>
      (Valued.isOpen_valuationSubring _).measurableSet)
  have hD0 : IsAddFundamentalDomain (sIntegerLattice Sf)
      (sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf) (sAdditiveTamagawa F Sf) :=
    IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet
      (existsUnique_vadd_mem F (RingOfIntegers.basis F) Sf)
  -- all fundamental domains have the same measure
  rw [hD.measure_eq hD0, hprod]
  unfold sAdditiveTamagawa
  rw [Measure.prod_prod, Measure.pi_pi]
  have h1 : infiniteAdditiveTamagawa F
      (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := (infinite_mass F).2
  rw [h1]
  congr 1
  refine (Finset.prod_congr rfl fun (v : Sf) _ => finite_mass F v.1).trans ?_
  exact Finset.prod_coe_sort Sf (fun v : HeightOneSpectrum (𝓞 F) =>
    (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹)
