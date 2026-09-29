-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/14dd7e25-7bee-583c-a0a8-8d0b9baeca7e

import Mathlib
import Theorems.Thm_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne

set_option autoImplicit false

open IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : CharZero L₀) (_ : Algebra ℚ L₀) (_ : IsCyclotomicExtension {q * ℓ} ℚ L₀)
      (i : L₀ →+* L) (ζ₀ ξ₀ : L₀) (_ : IsPrimitiveRoot ζ₀ q) (_ : IsPrimitiveRoot ξ₀ (q * ℓ))
      (_ : i ζ₀ = ζ) (_ : i ξ₀ = ξ)
      (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : Algebra A₀ L₀)
      (_ : IsFractionRing A₀ L₀) (_ : Algebra A₀ A) (_ : IsLocalHom (algebraMap A₀ A)),
      Function.Injective (algebraMap A₀ A) ∧
      (∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a)) ∧

      (∀ x : L₀, (∃ a : A₀, algebraMap A₀ L₀ a = x) ↔ ∃ a : A, algebraMap A L a = i x) ∧
      ((q : A₀) ∈ IsLocalRing.maximalIdeal A₀) ∧ (∃ x : A₀, algebraMap A₀ L₀ x = ζ₀) ∧

      (∀ ϖ₀ : A₀, IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀} →
        ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w) := by
  classical
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero hℓp.ne_zero⟩
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  haveI hcyc : IsCyclotomicExtension {q * ℓ} ℚ ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) := by
    change IsCyclotomicExtension {q * ℓ} ℚ ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hξ.isIntegral (NeZero.pos _)).tower_top (A := ℚ)).isAlgebraic]
    exact hξ.adjoin_isCyclotomicExtension ℚ
  haveI hNF : NumberField ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) :=
    IsCyclotomicExtension.numberField {q * ℓ} ℚ _

  let ξ₀ : ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) := ⟨ξ, IntermediateField.mem_adjoin_simple_self ℚ ξ⟩
  have hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ) := IsPrimitiveRoot.coe_submonoidClass_iff.mp hξ
  have hζmem : ζ ∈ IntermediateField.adjoin ℚ ({ξ} : Set L) := by
    obtain ⟨k, -, hk⟩ := (hξ.pow (NeZero.pos _) (mul_comm q ℓ)).eq_pow_of_pow_eq_one hζ.pow_eq_one
    rw [← hk, ← pow_mul]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ξ) _
  let ζ₀ : ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) := ⟨ζ, hζmem⟩
  have hζ₀L : algebraMap ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) L ζ₀ = ζ := rfl
  have hζ₀ : IsPrimitiveRoot ζ₀ q := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

  have hint : ∀ x : NumberField.RingOfIntegers ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)),
      ∃ y : A, algebraMap A L y = algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L (algebraMap _ _ x) := by
    intro x
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine IsIntegral.tower_top (R := ℤ) ?_
    exact (NumberField.RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L)
  choose f hf using hint
  have hAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  let f₀ : NumberField.RingOfIntegers ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) →+* A :=
    { toFun := f
      map_one' := hAL (by rw [hf, map_one, map_one, map_one])
      map_mul' := fun x y => hAL (by rw [hf, map_mul, map_mul, map_mul, hf, hf])
      map_zero' := hAL (by rw [hf, map_zero, map_zero, map_zero])
      map_add' := fun x y => hAL (by rw [hf, map_add, map_add, map_add, hf, hf]) }
  have hf₀ : ∀ x, algebraMap A L (f₀ x) = algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L (algebraMap _ _ x) := hf
  have hf₀inj : Function.Injective f₀ := by
    intro x y hxy
    have h := congrArg (algebraMap A L) hxy
    rw [hf₀, hf₀] at h
    exact IsFractionRing.injective _ _ ((algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L).injective h)

  set O := NumberField.RingOfIntegers ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) with hO
  let P : Ideal O := (maximalIdeal A).comap f₀
  haveI hP : P.IsPrime := Ideal.comap_isPrime f₀ (maximalIdeal A)
  have hqP : ((q : ℕ) : O) ∈ P := by
    show f₀ (q : O) ∈ maximalIdeal A
    rw [map_natCast]; exact hAq
  have hPne : P ≠ ⊥ := by
    intro h
    have : ((q : ℕ) : O) = 0 := by rw [← Ideal.mem_bot, ← h]; exact hqP
    exact (Nat.cast_ne_zero.mpr hqp.ne_zero) this
  haveI hPmax : P.IsMaximal := hP.isMaximal hPne

  let A₀ : Type := Localization.AtPrime P
  have hDVR : IsDiscreteValuationRing A₀ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hPne A₀
  have hunits : ∀ y : P.primeCompl, IsUnit (f₀ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
  let ι : A₀ →+* A := IsLocalization.lift (M := P.primeCompl) hunits
  have hιcomp : ι.comp (algebraMap O A₀) = f₀ := IsLocalization.lift_comp hunits
  letI iA : Algebra A₀ A := ι.toAlgebra
  have hKunits : ∀ y : P.primeCompl, IsUnit (algebraMap O (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective O _)).mpr ?_)
    intro hy
    exact y.2 (hy.symm ▸ P.zero_mem)
  let ιK : A₀ →+* ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) := IsLocalization.lift (M := P.primeCompl) hKunits
  have hιKcomp : ιK.comp (algebraMap O A₀) = algebraMap O _ := IsLocalization.lift_comp hKunits
  letI iK : Algebra A₀ ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) := ιK.toAlgebra
  haveI iOK : IsScalarTower O A₀ ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hKunits x).symm)
  have hcompat : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) =
      algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L (algebraMap A₀ (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) a) := by
    intro a
    show ((algebraMap A L).comp ι) a = ((algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L).comp ιK) a
    congr 1
    refine IsLocalization.ringHom_ext P.primeCompl ?_
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hιKcomp, hιcomp]
    ext x
    exact hf₀ x
  haveI hfrac : IsFractionRing A₀ ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A₀ _

  have hinj : Function.Injective (algebraMap A₀ A) := by
    show Function.Injective ι
    refine (IsLocalization.lift_injective_iff hunits).mpr (fun x y => ⟨fun h => ?_, fun h => ?_⟩)
    · exact congrArg f₀ (IsLocalization.injective A₀ P.primeCompl_le_nonZeroDivisors h)
    · exact congrArg _ (hf₀inj h)

  have hle : maximalIdeal A₀ ≤ (maximalIdeal A).comap ι := by
    show maximalIdeal (Localization.AtPrime P) ≤ (maximalIdeal A).comap ι
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
      hιcomp]
  have hloc : IsLocalHom (algebraMap A₀ A) := ((IsLocalRing.local_hom_TFAE ι).out 3 0).mp hle
  have hcomap : (maximalIdeal A).comap (algebraMap A₀ A) = maximalIdeal A₀ :=
    ((IsLocalRing.local_hom_TFAE ι).out 3 4).mp hle

  have hqA₀ : ((q : ℕ) : A₀) ∈ maximalIdeal A₀ := by
    show ((q : ℕ) : A₀) ∈ maximalIdeal (Localization.AtPrime P)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← map_natCast (algebraMap O A₀)]
    exact Ideal.mem_map_of_mem _ hqP

  have hζ₀A : ∃ x : A₀, algebraMap A₀ (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) x = ζ₀ := by
    refine ⟨algebraMap O A₀ hζ₀.toInteger, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    rfl

  have hcap : ∀ x : ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)), (∃ a : A₀, algebraMap A₀ (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) a = x) ↔
      ∃ a : A, algebraMap A L a = algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L x := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨algebraMap A₀ A a, hcompat a⟩
    · rintro ⟨a, ha⟩
      rcases ValuationRing.isInteger_or_isInteger A₀ x with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact ⟨b, hb⟩
      · by_cases hx0 : x = 0
        · exact ⟨0, by rw [hx0, map_zero]⟩
        have hbu : IsUnit b := by
          by_contra hbn
          have hbm : b ∈ maximalIdeal A₀ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hbn)
          rw [← hcomap, Ideal.mem_comap] at hbm
          have h1 : algebraMap A L (a * algebraMap A₀ A b) = 1 := by
            rw [map_mul, ha, hcompat, ← map_mul]
            change algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L (x * algebraMap A₀ (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) b) = 1
            rw [hb, mul_inv_cancel₀ hx0, map_one]
          have h2 : a * algebraMap A₀ A b = 1 := hAL (by rw [h1, map_one])
          exact (mem_maximalIdeal _).mp hbm (isUnit_iff_exists_inv'.mpr ⟨a, h2⟩)
        refine ⟨↑hbu.unit⁻¹, ?_⟩
        rw [map_units_inv, IsUnit.unit_spec, hb, inv_inv]

  have hunif : ∀ ϖ₀ : A₀, maximalIdeal A₀ = Ideal.span {ϖ₀} →
      ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w := by
    intro ϖ₀ hϖ₀
    obtain ⟨ε, hε, hpow⟩ :=
      IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing q ℓ
        hℓq.symm (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) A₀ hqA₀ ϖ₀ hϖ₀
    obtain ⟨w, hw, htw⟩ := ht
    have he : IsUnit (algebraMap A₀ A ε) := hε.map _
    have hx : (algebraMap A₀ A ϖ₀) ^ (q - 1) = algebraMap A₀ A ε * (q : A) := by
      rw [← map_pow, hpow, map_mul, map_natCast]
    have hq1 : q - 1 ≠ 0 := by
      have := hqp.two_le
      omega
    have h1 : (algebraMap A₀ A ϖ₀) ^ (q - 1) ∣ t ^ (q - 1) := by
      rw [hx, htw]; exact he.mul_left_dvd.mpr (dvd_mul_right _ _)
    have h2 : t ^ (q - 1) ∣ (algebraMap A₀ A ϖ₀) ^ (q - 1) := by
      rw [hx, htw]; exact hw.mul_right_dvd.mpr (dvd_mul_left _ _)
    rw [IsIntegrallyClosed.pow_dvd_pow_iff hq1] at h1 h2
    obtain ⟨u, hu⟩ := associated_of_dvd_dvd h2 h1
    exact ⟨u, u.isUnit, hu.symm⟩
  exact ⟨↥(IntermediateField.adjoin ℚ ({ξ} : Set L)), inferInstance, inferInstance, inferInstance, hcyc,
    algebraMap (↥(IntermediateField.adjoin ℚ ({ξ} : Set L))) L, ζ₀, ξ₀, hζ₀, hξ₀, rfl, rfl,
    A₀, inferInstance, inferInstance, hDVR, iK, hfrac, iA, hloc, hinj, hcompat, hcap, hqA₀, hζ₀A, hunif⟩

end S_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne (solution)
