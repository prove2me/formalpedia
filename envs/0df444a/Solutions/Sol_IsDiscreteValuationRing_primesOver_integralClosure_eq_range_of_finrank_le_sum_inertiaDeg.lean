-- Prove2me | solution 1 for IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/42e0a69f-8c23-503b-91a4-58fb2e0f0515

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace AlgVert

open IsLocalRing IsDedekindDomain

section Setup

variable {O : Type*} [CommRing O] [IsDomain O]
  {F : Type*} [Field F] [Algebra O F]

theorem mem_of_isIntegral (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)
    {y : F} (hy : IsIntegral O y) : y ∈ V := by
  let φ : O →+* ↥V := (algebraMap O F).codRestrict V.toSubring hOV
  have hy' : IsIntegral ↥V y := by
    obtain ⟨p, hp, hpy⟩ := hy
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpy
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := F)).mp hy'
  rw [← hz]
  exact z.2

variable (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)

noncomputable def toV : ↥(integralClosure O F) →+* ↥V :=
  (algebraMap (↥(integralClosure O F)) F).codRestrict V.toSubring
    (fun b => mem_of_isIntegral V hOV b.2)

@[scoped simp] theorem coe_toV (b : ↥(integralClosure O F)) : ((toV V hOV b : ↥V) : F) = (b : F) := rfl

noncomputable def centre : Ideal ↥(integralClosure O F) := (maximalIdeal ↥V).comap (toV V hOV)

scoped instance isPrime_centre : (centre V hOV).IsPrime := Ideal.comap_isPrime _ _

theorem mem_centre_iff (b : ↥(integralClosure O F)) : b ∈ centre V hOV ↔ (b : F) ∈ V.nonunits := by
  rw [centre, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toV]

end Setup

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]

theorem instances_B (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] :
    IsDedekindDomain ↥(integralClosure O F) ∧ Module.Finite O ↥(integralClosure O F) ∧
      IsFractionRing ↥(integralClosure O F) F :=
  ⟨integralClosure.isDedekindDomain O E F, IsIntegralClosure.finite O E F ↥(integralClosure O F),
    IsIntegralClosure.isFractionRing_of_finite_extension O E F ↥(integralClosure O F)⟩

scoped instance faithfulSMul_B : FaithfulSMul O ↥(integralClosure O F) :=
  (faithfulSMul_iff_algebraMap_injective O ↥(integralClosure O F)).mpr
    (fun a b h => FaithfulSMul.algebraMap_injective O F (congrArg Subtype.val h))

variable (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)
  (hdom : ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V.nonunits)

include hdom in

theorem comap_centre : (centre V hOV).comap (algebraMap O ↥(integralClosure O F)) = maximalIdeal O := by
  ext x
  rw [Ideal.mem_comap, mem_centre_iff]
  constructor
  · intro hx
    by_contra hx'
    have hu : IsUnit x := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hx'
    obtain ⟨u, rfl⟩ := hu
    have hmem : ((algebraMap O ↥(integralClosure O F) ↑u : ↥(integralClosure O F)) : F) ∈ V.nonunits := hx
    have hcoe : ((algebraMap O ↥(integralClosure O F) ↑u : ↥(integralClosure O F)) : F) = algebraMap O F ↑u := rfl
    rw [hcoe] at hmem

    have hunit : IsUnit (⟨algebraMap O F ↑u, hOV ↑u⟩ : ↥V) :=
      (Units.map ((algebraMap O F).codRestrict V.toSubring hOV : O →* ↥V) u).isUnit
    have hmem' := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨algebraMap O F ↑u, hOV ↑u⟩)).mp hmem
    exact (mem_nonunits_iff.mp (mem_maximalIdeal _ |>.mp hmem')) hunit
  · intro hx
    exact hdom x hx

include hdom in
theorem liesOver_centre : (centre V hOV).LiesOver (maximalIdeal O) :=
  ⟨(comap_centre V hOV hdom).symm⟩

include hdom in
theorem centre_ne_bot : centre V hOV ≠ ⊥ := by
  intro h
  have h1 := comap_centre V hOV hdom
  rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O ↥(integralClosure O F))] at h1
  exact IsDiscreteValuationRing.not_a_field O h1.symm

include hdom in
theorem card_le_inertiaDeg [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    {ι : Type*} [Fintype ι] (b : ι → F) (hb : ∀ i, IsIntegral O (b i))
    (hres : ∀ c : ι → O, (∑ i, algebraMap O F (c i) * b i) ∈ V.nonunits → ∀ i, c i ∈ maximalIdeal O) :
    Fintype.card ι ≤ (maximalIdeal O).inertiaDeg' (centre V hOV) := by
  classical
  haveI := liesOver_centre V hOV hdom
  rw [Ideal.inertiaDeg_algebraMap]
  let b' : ι → ↥(integralClosure O F) ⧸ centre V hOV := fun i => Ideal.Quotient.mk _ ⟨b i, hb i⟩
  have hli : LinearIndependent (O ⧸ maximalIdeal O) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨c, hc⟩ : ∃ c : ι → O, ∀ i, Ideal.Quotient.mk (maximalIdeal O) (c i) = g i :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (g i)).choose, fun i => (Ideal.Quotient.mk_surjective (g i)).choose_spec⟩
    have hsum : (Ideal.Quotient.mk (centre V hOV)) (∑ j, algebraMap O ↥(integralClosure O F) (c j) * ⟨b j, hb j⟩) = 0 := by
      rw [map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← hc j, map_mul, Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.algebraMap_eq, Algebra.smul_def,
        IsScalarTower.algebraMap_apply O (O ⧸ maximalIdeal O) (↥(integralClosure O F) ⧸ centre V hOV)]
      rfl
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_centre_iff] at hsum
    have hcoe : ((∑ j, algebraMap O ↥(integralClosure O F) (c j) * ⟨b j, hb j⟩ : ↥(integralClosure O F)) : F)
        = ∑ j, algebraMap O F (c j) * b j := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rfl
    rw [hcoe] at hsum
    have := hres c hsum i
    rw [← hc i, Ideal.Quotient.eq_zero_iff_mem]
    exact this
  exact hli.fintype_card_le_finrank

include hdom in
theorem primesOverFinset_eq_and_ramificationIdx_eq
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F]
    (hd : Module.finrank E F ≤ (maximalIdeal O).inertiaDeg' (centre V hOV)) :
    IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) = {centre V hOV} ∧
      Ideal.ramificationIdx' (maximalIdeal O) (centre V hOV) = 1 ∧
      (maximalIdeal O).inertiaDeg' (centre V hOV) = Module.finrank E F := by
  classical
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  haveI := liesOver_centre V hOV hdom
  have hsum := Ideal.sum_ramification_inertia (R := O) (S := ↥(integralClosure O F)) E F (p := maximalIdeal O) hp0
  have hmem : centre V hOV ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨inferInstance, inferInstance⟩
  have hmap0 : Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective O _)).not.mpr hp0

  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F),
      1 ≤ Ideal.ramificationIdx' (maximalIdeal O) P * (maximalIdeal O).inertiaDeg' P := by
    intro P hP
    have hP' := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver (maximalIdeal O) := hP'.2
    have he : Ideal.ramificationIdx' (maximalIdeal O) P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    have hf : (maximalIdeal O).inertiaDeg' P ≠ 0 := Ideal.inertiaDeg_ne_zero _ _
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero he hf)

  rw [← Finset.sum_erase_add _ _ hmem] at hsum
  set e := Ideal.ramificationIdx' (maximalIdeal O) (centre V hOV) with he_def
  set f := (maximalIdeal O).inertiaDeg' (centre V hOV) with hf_def
  set rest := ∑ P ∈ (IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F)).erase (centre V hOV),
      Ideal.ramificationIdx' (maximalIdeal O) P * (maximalIdeal O).inertiaDeg' P
    with hrest_def
  have he1 : 1 ≤ e := by
    have := hpos _ hmem
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by rw [← he_def, h, zero_mul] at this; exact absurd this (by norm_num))
  have hfe : f ≤ e * f := Nat.le_mul_of_pos_left f he1
  have hrest0 : rest = 0 := by
    generalize e * f = ef at hsum hfe
    omega
  have hef : e * f = f := by
    generalize e * f = ef at hsum hfe hrest0 ⊢
    omega
  have hfpos : 0 < f := Ideal.inertiaDeg'_pos _ _
  have he_eq : e = 1 := Nat.eq_of_mul_eq_mul_right hfpos (by rw [hef, one_mul])
  refine ⟨?_, he_eq, ?_⟩
  ·
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun P hP => ?_⟩
    by_contra hne
    have hPm : P ∈ (IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F)).erase (centre V hOV) :=
      Finset.mem_erase.mpr ⟨hne, hP⟩
    have h1 := Finset.single_le_sum (f := fun P => Ideal.ramificationIdx' (maximalIdeal O) P * (maximalIdeal O).inertiaDeg' P)
      (fun P _ => Nat.zero_le _) hPm
    have h2 := hpos P hP
    rw [← hrest_def, hrest0] at h1
    omega
  · generalize e * f = ef at hsum hfe hrest0 hef
    omega

noncomputable def centreHOS [IsDedekindDomain ↥(integralClosure O F)] (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum ↥(integralClosure O F) :=
  ⟨centre V hOV, inferInstance, h0⟩

theorem valuationSubringAtPrime_le [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) ≤ V := by
  rintro x ⟨a, s, hs, rfl⟩
  have ha : ((a : ↥(integralClosure O F)) : F) ∈ V := mem_of_isIntegral V hOV a.2
  have hs' : ((s : ↥(integralClosure O F)) : F) ∉ V.nonunits := fun h => hs ((mem_centre_iff V hOV s).mpr h)
  rw [ValuationSubring.mem_nonunits_iff_or, not_or] at hs'
  exact V.mul_mem _ _ ha (not_not.mp hs'.2)

theorem eq_valuationSubringAtPrime [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (hV : V ≠ ⊤) (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) = V :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le V hOV h0) hV

include hdom in
theorem centre_eq_map [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    (hprimes : IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) = {centre V hOV})
    (he : Ideal.ramificationIdx' (maximalIdeal O) (centre V hOV) = 1) :
    centre V hOV = (maximalIdeal O).map (algebraMap O ↥(integralClosure O F)) := by
  classical
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective O _)).not.mpr hp0
  have h0 := centre_ne_bot V hOV hdom
  have hcount : (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O))).count
      (centre V hOV) = 1 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count hmap0 inferInstance h0, he]
  have hall : ∀ P ∈ UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O)),
      P = centre V hOV := by
    intro P hP
    have : P ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) := Multiset.mem_toFinset.mpr hP
    rw [hprimes, Finset.mem_singleton] at this
    exact this
  have hcard : (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O))).card = 1 := by
    rw [Multiset.eq_replicate_of_mem hall, Multiset.count_replicate_self] at hcount
    exact hcount
  have hfac : UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O))
      = {centre V hOV} := by
    rw [Multiset.eq_replicate_of_mem hall, hcard, Multiset.replicate_one]
  have hprod := UniqueFactorizationMonoid.factors_prod hmap0
  rw [hfac, Multiset.prod_singleton] at hprod
  exact (associated_iff_eq.mp hprod)

omit V hOV hdom in

theorem valuationSubring_unique_of_residues_linearIndependent
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (V : ValuationSubring F) (hV : V ≠ ⊤) (hOV : ∀ x : O, algebraMap O F x ∈ V)
    (hdom : ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V.nonunits)
    (b : Fin (Module.finrank E F) → F) (hb : ∀ i, IsIntegral O (b i))
    (hres : ∀ c : Fin (Module.finrank E F) → O,
      (∑ i, algebraMap O F (c i) * b i) ∈ V.nonunits → ∀ i, c i ∈ maximalIdeal O) :
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V'.nonunits) → V' = V) ∧
    (∀ ϖ : O, Irreducible ϖ → ∀ x ∈ V, x ∈ V.nonunits → ∃ y ∈ V, x = algebraMap O F ϖ * y) := by
  classical
  obtain ⟨hDed, hFin, hFrac⟩ := instances_B (O := O) (F := F) E
  have hd : Module.finrank E F ≤ (maximalIdeal O).inertiaDeg' (centre V hOV) := by
    simpa using card_le_inertiaDeg V hOV hdom b hb hres
  obtain ⟨hprimes, he, -⟩ := primesOverFinset_eq_and_ramificationIdx_eq V hOV hdom E hd
  have h0 := centre_ne_bot V hOV hdom
  have hVW := eq_valuationSubringAtPrime V hOV hV h0
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  refine ⟨?_, ?_⟩
  · intro V' hV' hOV' hdom'
    have h0' := centre_ne_bot V' hOV' hdom'
    haveI := liesOver_centre V' hOV' hdom'
    have hmem' : centre V' hOV' ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨inferInstance, inferInstance⟩
    rw [hprimes, Finset.mem_singleton] at hmem'
    have hVW' := eq_valuationSubringAtPrime V' hOV' hV' h0'
    rw [← hVW, ← hVW']
    congr 1
    exact HeightOneSpectrum.ext hmem'
  · intro ϖ hϖ x hxV hxn
    have hcen := centre_eq_map V hOV hdom hprimes he

    haveI : IsLocalization.AtPrime (↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))) (centre V hOV) := by
      show IsLocalization ((centreHOS V hOV h0).asIdeal.primeCompl) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))
      infer_instance
    have hxW : x ∈ HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) := by rw [hVW]; exact hxV
    have hxn' : (⟨x, hxW⟩ : ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))) ∈ maximalIdeal ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0)) := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      show x ∈ (HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0)).nonunits
      rw [hVW]; exact hxn
    have hmax : maximalIdeal ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))
        = Ideal.span {((algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))).comp (algebraMap O ↥(integralClosure O F))) ϖ} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (centre V hOV) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))]
      show Ideal.map (algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0))) (centre V hOV) = _
      rw [hcen, hϖ.maximalIdeal_eq, Ideal.map_map, Ideal.map_span, Set.image_singleton]
    rw [hmax, Ideal.mem_span_singleton'] at hxn'
    obtain ⟨a, ha⟩ := hxn'
    refine ⟨(a : F), hVW.le a.2, ?_⟩
    have := congrArg (fun z : ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0)) => (z : F)) ha
    simp only [RingHom.comp_apply] at this
    rw [← this, mul_comm]
    rfl

omit V hOV hdom in

theorem exists_valuationSubring_mem_iff_presentation
    {R : Type*} [CommRing R] [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (𝔭 : Ideal R) [𝔭.IsPrime] [ValuationRing (Localization.AtPrime 𝔭)] :
    ∃ W : ValuationSubring F, ∀ x : F, x ∈ W ↔ ∃ r s : R, s ∉ 𝔭 ∧ x * algebraMap R F s = algebraMap R F r := by
  classical
  have hle : 𝔭.primeCompl ≤ nonZeroDivisors R := 𝔭.primeCompl_le_nonZeroDivisors

  letI : Algebra (Localization.AtPrime 𝔭) F :=
    (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) (g := algebraMap R F)
      (fun y => IsUnit.mk0 _ (fun h => nonZeroDivisors.ne_zero (hle y.2)
        ((FaithfulSMul.algebraMap_injective R F) (by rw [h, map_zero]))))).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔭) F := IsScalarTower.of_algebraMap_eq (fun c =>
    (IsLocalization.lift_eq (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) _ c).symm)
  haveI : IsFractionRing (Localization.AtPrime 𝔭) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭) F
  let W : ValuationSubring F := ValuationSubring.ofSubring (algebraMap (Localization.AtPrime 𝔭) F).range (by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (Localization.AtPrime 𝔭) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨y, hy⟩)
  refine ⟨W, fun x => ?_⟩
  show x ∈ (algebraMap (Localization.AtPrime 𝔭) F).range ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj 𝔭.primeCompl y
    refine ⟨r, s, s.2, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime 𝔭) F) hrs
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this
  · rintro ⟨r, s, hs, hx⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔭) r ⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩, ?_⟩
    have hs0 : algebraMap R F s ≠ 0 := fun h => nonZeroDivisors.ne_zero (hle hs)
      ((FaithfulSMul.algebraMap_injective R F) (by rw [h, map_zero]))
    apply mul_right_cancel₀ hs0
    rw [hx]
    have := IsLocalization.mk'_spec (Localization.AtPrime 𝔭) r ⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩
    have := congrArg (algebraMap (Localization.AtPrime 𝔭) F) this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this

end Main

namespace Several

open IsLocalRing IsDedekindDomain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]

theorem centre_injective [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} (V : ι → ValuationSubring F) (hV : ∀ i, V i ≠ ⊤) (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (hinj : Function.Injective V) :
    Function.Injective (fun i => centre (V i) (hOV i)) := by
  intro i j h
  apply hinj
  have hi := eq_valuationSubringAtPrime (V i) (hOV i) (hV i) (centre_ne_bot (V i) (hOV i) (hdom i))
  have hj := eq_valuationSubringAtPrime (V j) (hOV j) (hV j) (centre_ne_bot (V j) (hOV j) (hdom j))
  rw [← hi, ← hj]
  congr 1
  exact HeightOneSpectrum.ext h

theorem primesOverFinset_eq_image
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ι → ValuationSubring F) (hV : ∀ i, V i ≠ ⊤)
    (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (hinj : Function.Injective V)
    (d : ι → ℕ) (hd : ∀ i, d i ≤ (maximalIdeal O).inertiaDeg' (centre (V i) (hOV i)))
    (hsum : Module.finrank E F ≤ ∑ i, d i) :
    IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) = Finset.univ.image (fun i => centre (V i) (hOV i)) ∧
    (∀ i, Ideal.ramificationIdx' (maximalIdeal O) (centre (V i) (hOV i)) = 1) ∧
    (∀ i, (maximalIdeal O).inertiaDeg' (centre (V i) (hOV i)) = d i) ∧
    ∑ i, d i = Module.finrank E F := by
  classical
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hsumEF := Ideal.sum_ramification_inertia (R := O) (S := ↥(integralClosure O F)) E F (p := maximalIdeal O) hp0
  set s := IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) with hs
  set 𝔓 : ι → Ideal ↥(integralClosure O F) := fun i => centre (V i) (hOV i) with h𝔓
  set I := Finset.univ.image 𝔓 with hI
  have h𝔓inj : Function.Injective 𝔓 := centre_injective V hV hOV hdom hinj
  have hmem : ∀ i, 𝔓 i ∈ s := fun i => by
    haveI := liesOver_centre (V i) (hOV i) (hdom i)
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨inferInstance, inferInstance⟩
  have hIs : I ⊆ s := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hP
    exact hmem i

  set t : Ideal ↥(integralClosure O F) → ℕ :=
    fun P => Ideal.ramificationIdx' (maximalIdeal O) P * (maximalIdeal O).inertiaDeg' P with ht
  have hpos : ∀ P ∈ s, 1 ≤ t P := by
    intro P hP
    have hP' := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver (maximalIdeal O) := hP'.2
    have he : Ideal.ramificationIdx' (maximalIdeal O) P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    have hf : (maximalIdeal O).inertiaDeg' P ≠ 0 := Ideal.inertiaDeg_ne_zero _ _
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero he hf)
  have he1 : ∀ i, 1 ≤ Ideal.ramificationIdx' (maximalIdeal O) (𝔓 i) := by
    intro i
    haveI := liesOver_centre (V i) (hOV i) (hdom i)
    exact Nat.one_le_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (𝔓 i) hp0)

  have h1 : ∑ P ∈ I, t P ≤ ∑ P ∈ s, t P := Finset.sum_le_sum_of_subset_of_nonneg hIs (fun P _ _ => Nat.zero_le _)
  have h2 : ∑ P ∈ I, t P = ∑ i, t (𝔓 i) := by
    rw [hI, Finset.sum_image (fun i _ j _ h => h𝔓inj h)]
  have h3 : ∀ i, (maximalIdeal O).inertiaDeg' (𝔓 i) ≤ t (𝔓 i) := fun i =>
    Nat.le_mul_of_pos_left _ (he1 i)
  have h4 : ∑ i, d i ≤ ∑ i, (maximalIdeal O).inertiaDeg' (𝔓 i) := Finset.sum_le_sum (fun i _ => hd i)
  have h5 : ∑ i, (maximalIdeal O).inertiaDeg' (𝔓 i) ≤ ∑ i, t (𝔓 i) := Finset.sum_le_sum (fun i _ => h3 i)

  have hsumEF' : ∑ P ∈ s, t P = Module.finrank E F := hsumEF
  have hchain : ∑ P ∈ s, t P ≤ ∑ i, d i := hsumEF' ▸ hsum
  have hEq1 : ∑ P ∈ I, t P = ∑ P ∈ s, t P := by omega
  have hEq2 : ∑ i, (maximalIdeal O).inertiaDeg' (𝔓 i) = ∑ i, t (𝔓 i) := by omega
  have hEq3 : ∑ i, d i = ∑ i, (maximalIdeal O).inertiaDeg' (𝔓 i) := by omega

  have hsI : s = I := by
    refine (Finset.Subset.antisymm ?_ hIs)
    intro P hP
    by_contra hPI
    have hlt : ∑ Q ∈ I, t Q < ∑ Q ∈ s, t Q :=
      Finset.sum_lt_sum_of_subset hIs hP hPI (hpos P hP) (fun Q _ _ => Nat.zero_le _)
    omega

  have hterm : ∀ i ∈ Finset.univ, (maximalIdeal O).inertiaDeg' (𝔓 i) = t (𝔓 i) :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => h3 i)).mp hEq2
  have hterm' : ∀ i ∈ Finset.univ, d i = (maximalIdeal O).inertiaDeg' (𝔓 i) :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hd i)).mp hEq3
  refine ⟨hsI, fun i => ?_, fun i => (hterm' i (Finset.mem_univ i)).symm, by omega⟩
  have hfpos : 0 < (maximalIdeal O).inertiaDeg' (𝔓 i) := by
    haveI := liesOver_centre (V i) (hOV i) (hdom i)
    exact Ideal.inertiaDeg'_pos _ _
  have := hterm i (Finset.mem_univ i)
  rw [ht] at this
  exact (Nat.eq_of_mul_eq_mul_right hfpos (by rw [one_mul]; exact this.symm))

theorem map_eq_prod_centre [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ι → ValuationSubring F)
    (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (h𝔓inj : Function.Injective (fun i => centre (V i) (hOV i)))
    (hprimes : IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) = Finset.univ.image (fun i => centre (V i) (hOV i)))
    (he : ∀ i, Ideal.ramificationIdx' (maximalIdeal O) (centre (V i) (hOV i)) = 1) :
    (maximalIdeal O).map (algebraMap O ↥(integralClosure O F)) = ∏ i, centre (V i) (hOV i) := by
  classical
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective O _)).not.mpr hp0
  set m := UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O F)) (maximalIdeal O)) with hm

  have hcount : ∀ P, m.count P ≤ 1 := by
    intro P
    by_cases hP : P ∈ m
    · have hP' : P ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) := Multiset.mem_toFinset.mpr hP
      rw [hprimes] at hP'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hP'
      rw [hm, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count hmap0 inferInstance
        (centre_ne_bot (V i) (hOV i) (hdom i)), he i]
    · rw [Multiset.count_eq_zero_of_notMem hP]; exact Nat.zero_le _
  have hnodup : m.Nodup := Multiset.nodup_iff_count_le_one.mpr hcount
  have hprod := UniqueFactorizationMonoid.factors_prod hmap0
  rw [← hm] at hprod
  rw [← associated_iff_eq.mp hprod]

  have hmf : m.toFinset = Finset.univ.image (fun i => centre (V i) (hOV i)) := by rw [← hprimes]
  calc m.prod = (m.toFinset.val).prod := by rw [Multiset.toFinset_val, hnodup.dedup]
    _ = ∏ P ∈ m.toFinset, P := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    _ = ∏ i, centre (V i) (hOV i) := by rw [hmf, Finset.prod_image (fun i _ j _ h => h𝔓inj h)]

theorem valuationSubring_mem_of_inertiaDeg_le
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ι → ValuationSubring F) (hV : ∀ i, V i ≠ ⊤)
    (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (hinj : Function.Injective V)
    (d : ι → ℕ)
    (hd : ∀ (hB : IsDedekindDomain ↥(integralClosure O F)) (hBf : Module.Finite O ↥(integralClosure O F)),
      ∀ i, d i ≤ (maximalIdeal O).inertiaDeg' (centre (V i) (hOV i)))
    (hsum : Module.finrank E F ≤ ∑ i, d i) :
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V'.nonunits) → ∃ i, V' = V i) ∧
    (∀ i, ∀ ϖ : O, Irreducible ϖ → ∀ x ∈ V i, x ∈ (V i).nonunits → ∃ y ∈ V i, x = algebraMap O F ϖ * y) ∧
    (∑ i, d i = Module.finrank E F) ∧
    (∀ i, (maximalIdeal O).inertiaDeg' (centre (V i) (hOV i)) = d i) ∧
    (∀ i, Ideal.ramificationIdx' (maximalIdeal O) (centre (V i) (hOV i)) = 1) := by
  classical
  obtain ⟨hDed, hFin, hFrac⟩ := instances_B (O := O) (F := F) E
  obtain ⟨hprimes, he, hf, hsumEq⟩ := primesOverFinset_eq_image E V hV hOV hdom hinj d (hd hDed hFin) hsum
  have h𝔓inj : Function.Injective (fun i => centre (V i) (hOV i)) := centre_injective V hV hOV hdom hinj
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  refine ⟨?_, ?_, hsumEq, hf, he⟩
  · intro V' hV' hOV' hdom'
    have h0' := centre_ne_bot V' hOV' hdom'
    haveI := liesOver_centre V' hOV' hdom'
    have hmem' : centre V' hOV' ∈ IsDedekindDomain.primesOverFinset (maximalIdeal O) ↥(integralClosure O F) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨inferInstance, inferInstance⟩
    rw [hprimes] at hmem'
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem'
    refine ⟨i, ?_⟩
    have hW' := eq_valuationSubringAtPrime V' hOV' hV' h0'
    have hWi := eq_valuationSubringAtPrime (V i) (hOV i) (hV i) (centre_ne_bot (V i) (hOV i) (hdom i))
    rw [← hW', ← hWi]
    congr 1
    exact HeightOneSpectrum.ext hi.symm
  · intro i ϖ hϖ x hxV hxn
    have h0 := centre_ne_bot (V i) (hOV i) (hdom i)
    have hVW := eq_valuationSubringAtPrime (V i) (hOV i) (hV i) h0
    have hmapO := map_eq_prod_centre V hOV hdom h𝔓inj hprimes he
    haveI : IsLocalization.AtPrime (↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))) (centre (V i) (hOV i)) := by
      show IsLocalization ((centreHOS (V i) (hOV i) h0).asIdeal.primeCompl) _
      infer_instance
    have hxW : x ∈ HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0) := by rw [hVW]; exact hxV
    have hxn' : (⟨x, hxW⟩ : ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))) ∈
        maximalIdeal ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)) := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      show x ∈ (HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)).nonunits
      rw [hVW]; exact hxn

    have hothers : ∀ j, j ≠ i → Ideal.map (algebraMap ↥(integralClosure O F)
        ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))) (centre (V j) (hOV j)) = ⊤ := by
      intro j hji

      haveI : (centre (V j) (hOV j)).IsMaximal := by
        haveI := liesOver_centre (V j) (hOV j) (hdom j)
        exact Ideal.IsMaximal.of_liesOver_isMaximal (centre (V j) (hOV j)) (maximalIdeal O)
      have hne : centre (V j) (hOV j) ≠ centre (V i) (hOV i) := fun h => hji (h𝔓inj h)
      have hnle : ¬ centre (V j) (hOV j) ≤ centre (V i) (hOV i) := fun hle =>
        hne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) hle)
      obtain ⟨y, hyj, hyi⟩ := Set.not_subset.mp hnle
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hyj)
      exact (IsLocalization.AtPrime.isUnit_to_map_iff
        (↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))) (centre (V i) (hOV i)) y).mpr
          (Ideal.mem_primeCompl_iff.mpr hyi)
    have hA : Ideal.map ((algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))).comp
            (algebraMap O ↥(integralClosure O F))) (maximalIdeal O)
        = Ideal.span {((algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))).comp
            (algebraMap O ↥(integralClosure O F))) ϖ} := by
      rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    have hB : Ideal.map ((algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0))).comp
            (algebraMap O ↥(integralClosure O F))) (maximalIdeal O)
        = maximalIdeal ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)) := by
      rw [← Ideal.map_map, hmapO]
      rw [show Ideal.map (algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)))
          (∏ j, centre (V j) (hOV j))
          = ∏ j, Ideal.map (algebraMap ↥(integralClosure O F) ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)))
              (centre (V j) (hOV j)) from map_prod (Ideal.mapHom _) _ _]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        IsLocalization.AtPrime.map_eq_maximalIdeal (centre (V i) (hOV i))
          ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)),
        Finset.prod_eq_one (fun j hj => ?_), mul_one]
      rw [Ideal.one_eq_top]
      exact hothers j (Finset.ne_of_mem_erase hj)
    have hmax := hB.symm.trans hA
    rw [hmax, Ideal.mem_span_singleton'] at hxn'
    obtain ⟨a, ha⟩ := hxn'
    refine ⟨(a : F), hVW.le a.2, ?_⟩
    have := congrArg (fun z : ↥(HeightOneSpectrum.valuationSubringAtPrime F (centreHOS (V i) (hOV i) h0)) => (z : F)) ha
    simp only [RingHom.comp_apply] at this
    rw [← this, mul_comm]
    rfl

theorem valuationSubring_mem_of_residues_linearIndependent_family
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ι → ValuationSubring F) (hV : ∀ i, V i ≠ ⊤)
    (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (hinj : Function.Injective V)
    (d : ι → ℕ) (b : ∀ i, Fin (d i) → F) (hb : ∀ i j, IsIntegral O (b i j))
    (hres : ∀ i, ∀ c : Fin (d i) → O,
      (∑ j, algebraMap O F (c j) * b i j) ∈ (V i).nonunits → ∀ j, c j ∈ maximalIdeal O)
    (hsum : Module.finrank E F ≤ ∑ i, d i) :
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V'.nonunits) → ∃ i, V' = V i) ∧
    (∀ i, ∀ ϖ : O, Irreducible ϖ → ∀ x ∈ V i, x ∈ (V i).nonunits → ∃ y ∈ V i, x = algebraMap O F ϖ * y) ∧
    (∑ i, d i = Module.finrank E F) ∧
    (∀ i, (maximalIdeal O).inertiaDeg' (centre (V i) (hOV i)) = d i) ∧
    (∀ i, Ideal.ramificationIdx' (maximalIdeal O) (centre (V i) (hOV i)) = 1) :=
  valuationSubring_mem_of_inertiaDeg_le E V hV hOV hdom hinj d
    (fun _ _ i => by simpa using card_le_inertiaDeg (V i) (hOV i) (hdom i) (b i) (hb i) (hres i)) hsum

end Several

namespace Primes

open IsLocalRing IsDedekindDomain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]

theorem mem_valuationSubringAtPrime_iff {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    (v : HeightOneSpectrum B) (x : F) :
    x ∈ HeightOneSpectrum.valuationSubringAtPrime F v ↔ ∃ a s : B, s ∉ v.asIdeal ∧ x * algebraMap B F s = algebraMap B F a := by
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    refine ⟨a, s, hs, ?_⟩
    have hs0 : algebraMap B F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ v.asIdeal.zero_mem)))
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  · rintro ⟨a, s, hs, hx⟩
    have hs0 : algebraMap B F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ v.asIdeal.zero_mem)))
    refine ⟨a, s, hs, ?_⟩
    rw [← hx, mul_assoc, mul_inv_cancel₀ hs0, mul_one]

theorem valuationSubringAtPrime_data [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (𝔓 : Ideal ↥(integralClosure O F)) [𝔓.IsPrime] (h0 : 𝔓 ≠ ⊥) [𝔓.LiesOver (maximalIdeal O)] :
    let W := HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓, inferInstance, h0⟩
    ∃ (hOV : ∀ x : O, algebraMap O F x ∈ W),
      (∀ x ∈ maximalIdeal O, algebraMap O F x ∈ W.nonunits) ∧ W ≠ ⊤ ∧ centre W hOV = 𝔓 := by
  intro W
  have hB : ∀ b : ↥(integralClosure O F), (b : F) ∈ W := fun b =>
    (mem_valuationSubringAtPrime_iff _ _).mpr ⟨b, 1, fun h => (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance) h,
      by rw [map_one, mul_one]; rfl⟩
  have hOV : ∀ x : O, algebraMap O F x ∈ W := fun x => hB (algebraMap O ↥(integralClosure O F) x)

  have hnon : ∀ b : ↥(integralClosure O F), b ∈ 𝔓 → (b : F) ∈ W.nonunits := by
    intro b hb
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases hb0 : (b : F) = 0
    · exact Or.inl hb0
    · refine Or.inr (fun hinv => ?_)
      obtain ⟨a, s, hs, has⟩ := (mem_valuationSubringAtPrime_iff _ _).mp hinv
      apply hs
      have : s = a * b := by
        apply FaithfulSMul.algebraMap_injective ↥(integralClosure O F) F
        rw [map_mul, ← has]
        change _ = (b : F)⁻¹ * algebraMap _ F s * (b : F)
        field_simp
      rw [this]; exact 𝔓.mul_mem_left a hb
  have hcen : ∀ b : ↥(integralClosure O F), (b : F) ∈ W.nonunits → b ∈ 𝔓 := by
    intro b hb
    by_contra hbn
    rw [ValuationSubring.mem_nonunits_iff_or] at hb
    rcases hb with hb0 | hinv
    · exact hbn (by rw [show b = 0 from Subtype.ext hb0]; exact 𝔓.zero_mem)
    · apply hinv
      refine (mem_valuationSubringAtPrime_iff _ _).mpr ⟨1, b, hbn, ?_⟩
      have hb0 : (b : F) ≠ 0 := fun h => hbn (by rw [show b = 0 from Subtype.ext h]; exact 𝔓.zero_mem)
      rw [map_one]
      exact inv_mul_cancel₀ hb0
  refine ⟨hOV, ?_, ?_, ?_⟩
  · intro x hx
    have : algebraMap O ↥(integralClosure O F) x ∈ 𝔓 := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def 𝔓 (maximalIdeal O)]; exact hx
    exact hnon _ this
  · intro htop
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖm : ϖ ∈ maximalIdeal O := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ ▸ Ideal.mem_span_singleton_self ϖ
    have hmem : algebraMap O ↥(integralClosure O F) ϖ ∈ 𝔓 := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def 𝔓 (maximalIdeal O)]; exact hϖm
    have hn := hnon _ hmem
    rw [ValuationSubring.mem_nonunits_iff_or] at hn
    rcases hn with h0 | hinv
    · exact hϖ.ne_zero (FaithfulSMul.algebraMap_injective O F (by rw [map_zero]; exact h0))
    · exact hinv (htop ▸ ValuationSubring.mem_top _)
  · ext b
    rw [mem_centre_iff]
    exact ⟨hcen b, hnon b⟩

theorem of_primes
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔓 : ι → Ideal ↥(integralClosure O F))
    [hprime : ∀ i, (𝔓 i).IsPrime] (h0 : ∀ i, 𝔓 i ≠ ⊥) [hover : ∀ i, (𝔓 i).LiesOver (maximalIdeal O)]
    (hinj : Function.Injective 𝔓)
    (d : ι → ℕ) (hd : ∀ i, d i ≤ (maximalIdeal O).inertiaDeg' (𝔓 i)) (hsum : Module.finrank E F ≤ ∑ i, d i) :
    (maximalIdeal O).primesOver ↥(integralClosure O F) = Set.range 𝔓 ∧
    (∀ i, Ideal.ramificationIdx' (maximalIdeal O) (𝔓 i) = 1) ∧
    (∀ i, (maximalIdeal O).inertiaDeg' (𝔓 i) = d i) ∧
    (∑ i, d i = Module.finrank E F) ∧
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V'.nonunits) →
        ∃ i, V' = HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩) ∧
    (∀ i, ∀ ϖ : O, Irreducible ϖ → ∀ x ∈ HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩,
        x ∈ (HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩).nonunits →
        ∃ y ∈ HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩, x = algebraMap O F ϖ * y) := by
  classical
  let W : ι → ValuationSubring F := fun i => HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩
  have hdata := fun i => valuationSubringAtPrime_data (O := O) (F := F) (𝔓 i) (h0 i)
  choose hOV hdom hne hcen using hdata
  have hWinj : Function.Injective W := by
    intro i j h
    apply hinj
    rw [← hcen i, ← hcen j]

    have : ∀ (U U' : ValuationSubring F) (hU : ∀ x : O, algebraMap O F x ∈ U) (hU' : ∀ x : O, algebraMap O F x ∈ U'),
        U = U' → centre U hU = centre U' hU' := by
      intro U U' hU hU' h; subst h; rfl
    exact this _ _ (hOV i) (hOV j) h
  have hd' : ∀ (hB : IsDedekindDomain ↥(integralClosure O F)) (hBf : Module.Finite O ↥(integralClosure O F)),
      ∀ i, d i ≤ (maximalIdeal O).inertiaDeg' (centre (W i) (hOV i)) := fun _ _ i => by rw [hcen i]; exact hd i
  obtain ⟨huniq, hgen, hsumEq, hf, he⟩ :=
    Several.valuationSubring_mem_of_inertiaDeg_le E W hne hOV hdom hWinj d hd' hsum
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  obtain ⟨hprimes, -, -, -⟩ := Several.primesOverFinset_eq_image E W hne hOV hdom hWinj d (hd' inferInstance inferInstance) hsum
  refine ⟨?_, fun i => (hcen i) ▸ he i, fun i => (hcen i) ▸ hf i, hsumEq, huniq, hgen⟩
  rw [← IsDedekindDomain.coe_primesOverFinset hp0 ↥(integralClosure O F), hprimes, Finset.coe_image, Finset.coe_univ,
    Set.image_univ]
  congr 1
  funext i
  exact hcen i

end Primes

end AlgVert
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg.AlgVert"

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔓 : ι → Ideal ↥(integralClosure O F))
    [hprime : ∀ i, (𝔓 i).IsPrime] (h0 : ∀ i, 𝔓 i ≠ ⊥) [hover : ∀ i, (𝔓 i).LiesOver (IsLocalRing.maximalIdeal O)]
    (hinj : Function.Injective 𝔓)
    (d : ι → ℕ) (hd : ∀ i, d i ≤ (IsLocalRing.maximalIdeal O).inertiaDeg' (𝔓 i)) (hsum : Module.finrank E F ≤ ∑ i, d i) :
    (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O F) = Set.range 𝔓 ∧
    (∀ i, Ideal.ramificationIdx' (IsLocalRing.maximalIdeal O) (𝔓 i) = 1) ∧
    (∀ i, (IsLocalRing.maximalIdeal O).inertiaDeg' (𝔓 i) = d i) ∧
    (∑ i, d i = Module.finrank E F) ∧
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ V'.nonunits) →
        ∃ i, V' = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩) ∧
    (∀ i, ∀ ϖ : O, Irreducible ϖ → ∀ x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩,
        x ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩).nonunits →
        ∃ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩, x = algebraMap O F ϖ * y) :=
  AlgVert.Primes.of_primes E 𝔓 h0 hinj d hd hsum

end S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
end P2MW
export P2MW.S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg (solution)
