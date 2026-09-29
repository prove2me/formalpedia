-- Prove2me | solution 1 for IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7afb713f-5a4c-56e7-9801-5f534a1bff3a

import Mathlib
import Theorems.Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

set_option autoImplicit false

universe u v

open IsLocalRing

namespace DvrDomination

theorem dimensionLEOne_of_ringKrullDim_le_one (C : Type u) [CommRing C] [IsDomain C]
    (h : ringKrullDim C ≤ 1) : Ring.DimensionLEOne C := by
  refine Ring.DimensionLEOne.mk (fun {p} hp0 hp => ?_)
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  by_contra hnot
  have hlt : p < m := lt_of_le_of_ne hpm (fun h => hnot (h ▸ hm))
  have hbot : (⊥ : Ideal C) < p := bot_lt_iff_ne_bot.mpr hp0
  haveI := hm.isPrime
  have h1 : (⊥ : Ideal C).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 : p.height + 1 ≤ m.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (m.height : WithBot ℕ∞) ≤ ringKrullDim C := Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
  rw [Ideal.height_bot, zero_add] at h1
  have h4 : (2 : ℕ∞) ≤ m.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := add_le_add h1 le_rfl
      _ ≤ m.height := h2
  have h5 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C := le_trans (by exact_mod_cast h4) h3
  have h6 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := le_trans h5 h
  exact absurd h6 (by decide)

section StepB

variable {K : Type v} [Field K]

theorem exists_dvr_of_height_le_one (S : Subring K) [IsNoetherianRing S] [IsFractionRing S K]
    (P : Ideal S) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hP1 : P.height ≤ 1) :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧ S ≤ V.toSubring ∧
      ∀ s : S, s ∈ P ↔ (s : K) ∈ V.nonunits := by
  classical
  set R₁ : Subring K := (LocalSubring.ofPrime S P).toSubring with hR₁
  haveI : IsLocalization.AtPrime (↥R₁) P := LocalSubring.instAtPrimeSubtypeMemSubringToSubringOfPrime S P
  haveI : IsLocalRing ↥R₁ := (LocalSubring.ofPrime S P).isLocalRing
  haveI : IsNoetherianRing ↥R₁ := IsLocalization.isNoetherianRing P.primeCompl (↥R₁) inferInstance
  haveI : IsFractionRing (↥R₁) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl (↥R₁) K
  have hdim : ringKrullDim ↥R₁ ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (↥R₁)]
    exact_mod_cast hP1
  have hnf : ¬ IsField ↥R₁ := by
    intro hf
    have h1 : maximalIdeal ↥R₁ = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf
    have h2 : Ideal.under (↥S) (maximalIdeal ↥R₁) = P := IsLocalization.AtPrime.under_maximalIdeal (↥R₁) P
    rw [h1] at h2
    apply hP0
    rw [← h2]
    ext s
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    have hinj : Function.Injective (algebraMap (↥S) (↥R₁)) :=
      IsLocalization.injective (↥R₁) P.primeCompl_le_nonZeroDivisors
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

  set C : Subalgebra (↥R₁) K := integralClosure (↥R₁) K with hC
  obtain ⟨hCnoeth, hCdim⟩ := IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra hdim K K C
  haveI : IsNoetherianRing ↥C := hCnoeth
  haveI : IsFractionRing (↥C) K := integralClosure.isFractionRing_of_finite_extension K K
  haveI : Ring.DimensionLEOne ↥C := dimensionLEOne_of_ringKrullDim_le_one (↥C) hCdim
  haveI : IsIntegrallyClosedIn (↥C) K := IsIntegrallyClosedIn.of_isIntegralClosure (↥R₁)
  haveI : IsIntegrallyClosed ↥C := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  haveI : IsDedekindRing ↥C := IsDedekindRing.mk
  haveI : IsDedekindDomain ↥C := IsDedekindDomain.mk
  have hker : RingHom.ker (algebraMap (↥R₁) (↥C)) ≤ maximalIdeal ↥R₁ := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := FaithfulSMul.algebraMap_injective (↥R₁) (↥C) (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥C) (maximalIdeal ↥R₁) hker
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hQ, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun hx => FaithfulSMul.algebraMap_injective (↥R₁) (↥C) (hx.trans (map_zero _).symm),
      fun hx => by rw [hx, map_zero]⟩
  haveI : Q.IsPrime := hQmax.isPrime
  let w : IsDedekindDomain.HeightOneSpectrum ↥C := ⟨Q, hQmax.isPrime, hQ0⟩
  haveI hlocV : IsLocalization.AtPrime (↥(w.valuationSubringAtPrime K)) w.asIdeal :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime w
  refine ⟨w.valuationSubringAtPrime K, ?_, ?_, ?_⟩
  · exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (↥C) (P := w.asIdeal) hQ0 _
  · intro s hs
    have h1 : s ∈ R₁ := LocalSubring.le_ofPrime S P hs
    have h2 : (algebraMap (↥C) K) (algebraMap (↥R₁) (↥C) ⟨s, h1⟩) = s := by
      rw [← IsScalarTower.algebraMap_apply]; rfl
    rw [← h2, IsScalarTower.algebraMap_apply (↥C) (↥(w.valuationSubringAtPrime K)) K]
    exact Subtype.mem _
  · intro s
    set V := w.valuationSubringAtPrime K with hV
    haveI : IsLocalization.AtPrime (↥V) w.asIdeal :=
      IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime w
    have e1 : s ∈ P ↔ (algebraMap (↥S) (↥R₁) s) ∈ maximalIdeal ↥R₁ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (↥R₁) P s).symm
    have e2 : (algebraMap (↥S) (↥R₁) s) ∈ maximalIdeal ↥R₁ ↔
        algebraMap (↥R₁) (↥C) (algebraMap (↥S) (↥R₁) s) ∈ w.asIdeal := by
      rw [← hQ, Ideal.mem_comap]
    have e3 : algebraMap (↥R₁) (↥C) (algebraMap (↥S) (↥R₁) s) ∈ w.asIdeal ↔
        algebraMap (↥C) (↥V) (algebraMap (↥R₁) (↥C) (algebraMap (↥S) (↥R₁) s)) ∈ maximalIdeal ↥V :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (↥V) w.asIdeal _).symm
    rw [e1, e2, e3, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
    have k1 : ∀ c : ↥C, ((algebraMap (↥C) (↥V) c : ↥V) : K) = (c : K) := fun c =>
      (IsScalarTower.algebraMap_apply (↥C) (↥V) K c).symm
    have k2 : ∀ r : ↥R₁, ((algebraMap (↥R₁) (↥C) r : ↥C) : K) = (r : K) := fun r => rfl
    have k3 : ∀ t : ↥S, ((algebraMap (↥S) (↥R₁) t : ↥R₁) : K) = (t : K) := fun t =>
      (IsScalarTower.algebraMap_apply (↥S) (↥R₁) K t).symm
    rw [k1, k2, k3]

end StepB

section StepA

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_subalgebra_prime_height_le_one (hR : ¬ IsField R) :
    ∃ (S : Subalgebra R K) (P : Ideal ↥S) (_ : P.IsPrime), IsNoetherianRing ↥S ∧ P ≠ ⊥ ∧ P.height ≤ 1 ∧
      ∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R ↥S r ∈ P := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨V₀, hV₀⟩ := (LocalSubring.range (algebraMap R K)).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV₀
  have hRV : ∀ r : R, algebraMap R K r ∈ V₀ := by
    intro r
    have : algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring := by
      rw [LocalSubring.range_toSubring]; exact ⟨r, rfl⟩
    exact hle this
  have hrange : ∀ z : K, z ∈ (LocalSubring.range (algebraMap R K)).toSubring ↔ z ∈ Set.range (algebraMap R K) := by
    intro z; rw [LocalSubring.range_toSubring]; rfl
  have hunitV : ∀ r : R, r ∉ maximalIdeal R → V₀.valuation (algebraMap R K r) = 1 := by
    intro r hr
    have hu : IsUnit r := by
      by_contra h; exact hr ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have : IsUnit (⟨algebraMap R K r, hRV r⟩ : ↥V₀) := by
      obtain ⟨u, rfl⟩ := hu
      exact ⟨⟨⟨algebraMap R K u, hRV u⟩, ⟨algebraMap R K (u⁻¹ : Rˣ), hRV _⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    exact (V₀.valuation_eq_one_iff ⟨algebraMap R K r, hRV r⟩).mp this
  have hdomV : ∀ r : R, r ∈ maximalIdeal R → V₀.valuation (algebraMap R K r) < 1 := by
    intro r hr
    have hle1 : V₀.valuation (algebraMap R K r) ≤ 1 := (V₀.valuation_le_one_iff _).mpr (hRV r)
    rcases hle1.lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hmemA : algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring := (hrange _).mpr ⟨r, rfl⟩
    have huV : IsUnit (Subring.inclusion hle ⟨algebraMap R K r, hmemA⟩) :=
      (V₀.valuation_eq_one_iff ⟨algebraMap R K r, hRV r⟩).mpr heq
    have huA : IsUnit (⟨algebraMap R K r, hmemA⟩ : ↥(LocalSubring.range (algebraMap R K)).toSubring) :=
      hloc.map_nonunit _ huV
    obtain ⟨⟨a, b, hab, hba⟩, ha⟩ := huA
    have ha' : (a : K) = algebraMap R K r := congrArg Subtype.val ha
    obtain ⟨r', hr'⟩ := (hrange _).mp b.2
    have hmul : algebraMap R K (r * r') = algebraMap R K 1 := by
      rw [map_mul, map_one, ← ha', hr']
      exact congrArg Subtype.val hab
    have hunit : IsUnit r := IsUnit.of_mul_eq_one r' (hinj hmul)
    exact (IsLocalRing.mem_maximalIdeal _).mp hr hunit

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hR
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hs]
    simp
  obtain ⟨x, hxs, hxmax⟩ := s.exists_max_image (fun y => V₀.valuation (algebraMap R K y)) hsne
  have hsm : ∀ y ∈ s, y ∈ maximalIdeal R := fun y hy => hs ▸ Ideal.subset_span hy
  have hx0 : algebraMap R K x ≠ 0 := by
    intro h0
    obtain ⟨y, hys, hy0⟩ : ∃ y ∈ s, y ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hR
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hs, Ideal.span_eq_bot]
      exact hall
    have := hxmax y hys
    rw [h0, map_zero] at this
    exact (map_ne_zero_iff _ hinj).mpr hy0 ((Valuation.zero_iff _).mp (le_zero_iff.mp this))

  set T : Finset K := s.image (fun y => algebraMap R K y / algebraMap R K x) with hT
  set S : Subalgebra R K := Algebra.adjoin R (T : Set K) with hS
  haveI hSnoeth : IsNoetherianRing ↥S := by
    haveI : Algebra.FiniteType R ↥S := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
    exact Algebra.FiniteType.isNoetherianRing R ↥S

  let V₀' : Subalgebra R K :=
    { V₀.toSubring with algebraMap_mem' := fun r => hRV r }
  have hSV : S ≤ V₀' := by
    rw [hS]
    refine Algebra.adjoin_le ?_
    intro t ht
    rw [hT, Finset.coe_image] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    show algebraMap R K y / algebraMap R K x ∈ V₀
    rw [← V₀.valuation_le_one_iff, map_div₀, div_le_one₀ (by
      rw [Valuation.pos_iff]; exact hx0)]
    exact hxmax y hy
  have hSV' : ∀ z : ↥S, (z : K) ∈ V₀ := fun z => hSV z.2

  let x' : ↥S := ⟨algebraMap R K x, Subalgebra.algebraMap_mem S x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  let toV : ↥S →+* ↥V₀ :=
    { toFun := fun z => ⟨z, hSV' z⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let 𝔮 : Ideal ↥S := (maximalIdeal ↥V₀).comap toV
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime toV _
  have hx'𝔮 : x' ∈ 𝔮 := by
    show toV x' ∈ maximalIdeal ↥V₀
    rw [ValuationSubring.valuation_lt_one_iff]
    exact hdomV x (hsm x hxs)
  obtain ⟨P, hPmin, hP𝔮⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x'}) (J := 𝔮)
    ((Ideal.span_singleton_le_iff_mem _).mpr hx'𝔮)
  have hPprime : P.IsPrime := hPmin.1.1
  have hxP : x' ∈ P := hPmin.1.2 (Ideal.mem_span_singleton_self x')
  refine ⟨S, P, hPprime, hSnoeth, ?_, ?_, ?_⟩
  · intro h; rw [h] at hxP; exact hx'0 ((Submodule.mem_bot _).mp hxP)
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x'}) P hPmin
  · intro r
    constructor
    · intro hr

      apply hPmin.1.2
      have hmap : Ideal.map (algebraMap R ↥S) (maximalIdeal R) ≤ Ideal.span {x'} := by
        rw [← hs, Ideal.map_span]
        refine Ideal.span_le.mpr ?_
        rintro z ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_span_singleton']
        refine ⟨⟨algebraMap R K y / algebraMap R K x, ?_⟩, ?_⟩
        · rw [hS]; exact Algebra.subset_adjoin (by rw [hT, Finset.coe_image]; exact ⟨y, hy, rfl⟩)
        · apply Subtype.ext
          show algebraMap R K y / algebraMap R K x * algebraMap R K x = (algebraMap R ↥S y : K)
          rw [div_mul_cancel₀ _ hx0]
          rfl
      exact hmap (Ideal.mem_map_of_mem _ hr)
    · intro hr
      by_contra hnot
      have h1 := hunitV r hnot
      have h2 : toV (algebraMap R ↥S r) ∈ maximalIdeal ↥V₀ := hP𝔮 hr
      rw [ValuationSubring.valuation_lt_one_iff] at h2
      change V₀.valuation (algebraMap R K r) < 1 at h2
      rw [h1] at h2
      exact lt_irrefl _ h2

end StepA

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) := by
  classical
  obtain ⟨S, P, hP, hSn, hP0, hP1, hdom⟩ := exists_subalgebra_prime_height_le_one (K := K) hR
  haveI : IsNoetherianRing ↥S.toSubring := hSn
  haveI : FaithfulSMul (↥S.toSubring) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing (↥S.toSubring) K := by
    refine IsFractionRing.of_field (↥S.toSubring) K (fun z => ?_)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    exact ⟨⟨algebraMap R K a, S.algebraMap_mem a⟩, ⟨algebraMap R K b, S.algebraMap_mem b⟩, rfl⟩
  haveI : (show Ideal ↥S.toSubring from P).IsPrime := hP
  obtain ⟨V, hV, hSV, hPV⟩ := exists_dvr_of_height_le_one S.toSubring (show Ideal ↥S.toSubring from P) hP0 hP1
  refine ⟨V, hV, fun r => hSV (S.algebraMap_mem r), fun r => ?_⟩
  rw [hdom r]
  exact hPV ⟨algebraMap R K r, S.algebraMap_mem r⟩

end DvrDomination

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) :=
  DvrDomination.main hR K

end S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
end P2MW
export P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates (solution)
