-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/603d2d49-9d88-56b3-baa1-fd1a8ea758f8

import Mathlib
import Theorems.Thm_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot

set_option autoImplicit false

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' A) (_ : Algebra A' L) (_ : IsScalarTower A' A L)
      (_ : Algebra A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)))
      (_ : IsScalarTower A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) L)
      (_ : IsFractionRing A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L))),
      Function.Injective (algebraMap A' A) ∧
      (IsLocalRing.maximalIdeal A).comap (algebraMap A' A) = IsLocalRing.maximalIdeal A' ∧
      ((q : A') ∈ IsLocalRing.maximalIdeal A') ∧
      Finite (IsLocalRing.ResidueField A') ∧
      (∃ ϖ ε : A', IsLocalRing.maximalIdeal A' = Ideal.span {ϖ} ∧ IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A')) ∧
      (∃ r : A', algebraMap A' L r = ξ) := by
  classical
  have hqp : q.Prime := Fact.out
  have hlp : ℓ.Prime := Fact.out
  haveI hne : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero hlp.ne_zero⟩
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  set K₀ : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ξ} : Set L) with hK₀
  have hξint : IsIntegral ℚ ξ := (hξ.isIntegral (Nat.pos_of_ne_zero hne.ne)).tower_top
  haveI : FiniteDimensional ℚ K₀ := IntermediateField.adjoin.finiteDimensional hξint
  haveI : NumberField K₀ := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

  set ξ₀ : K₀ := ⟨ξ, IntermediateField.mem_adjoin_simple_self ℚ ξ⟩ with hξ₀
  have hξ₀L : (algebraMap K₀ L) ξ₀ = ξ := rfl
  have hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K₀ L) (by rw [hξ₀L]; exact hξ) (algebraMap K₀ L).injective
  haveI hcyc : IsCyclotomicExtension {q * ℓ} ℚ K₀ := by
    change IsCyclotomicExtension {q * ℓ} ℚ (IntermediateField.adjoin ℚ ({ξ} : Set L)).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hξint.isAlgebraic]
    exact hξ.adjoin_isCyclotomicExtension ℚ
  set O := NumberField.RingOfIntegers K₀ with hO

  have hmemA : ∀ x : O, ∃ a : A, algebraMap A L a = algebraMap K₀ L (x : K₀) := by
    intro x
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ?_
    have h1 : IsIntegral ℤ (algebraMap K₀ L (x : K₀)) := (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap
    exact h1.tower_top
  choose ιf hιf using hmemA
  let ι : O →+* A :=
    { toFun := ιf
      map_one' := hinjAL (by simp [hιf])
      map_mul' := fun x y => hinjAL (by simp [hιf])
      map_zero' := hinjAL (by simp [hιf])
      map_add' := fun x y => hinjAL (by simp [hιf]) }
  have hι : ∀ x : O, algebraMap A L (ι x) = algebraMap K₀ L (x : K₀) := hιf
  have hιinj : Function.Injective ι := by
    intro x y h
    have := congrArg (algebraMap A L) h
    rw [hι, hι] at this
    exact Subtype.ext ((algebraMap K₀ L).injective this)

  set 𝔭 : Ideal O := (IsLocalRing.maximalIdeal A).comap ι with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := Ideal.IsPrime.comap _
  have hq𝔭 : ((q : ℕ) : O) ∈ 𝔭 := by
    show ι (q : O) ∈ IsLocalRing.maximalIdeal A
    rw [map_natCast]; exact hAq
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    intro h
    have : ((q : ℕ) : O) = 0 := by rw [← Ideal.mem_bot, ← h]; exact hq𝔭
    exact hqp.ne_zero (by exact_mod_cast this)
  haveI h𝔭m : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal h𝔭p h𝔭0
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O h𝔭0 _
  set A' := Localization.AtPrime 𝔭 with hA'
  have hMle : 𝔭.primeCompl ≤ nonZeroDivisors O := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hs (h0 ▸ Ideal.zero_mem _)
  have hOA' : Function.Injective (algebraMap O A') := IsLocalization.injective A' hMle

  have hunitA : ∀ y : 𝔭.primeCompl, IsUnit (ι y) := by
    rintro ⟨y, hy⟩
    by_contra hnu
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  let ψA : A' →+* A := IsLocalization.lift (M := 𝔭.primeCompl) hunitA
  have hψA : ∀ x : O, ψA (algebraMap O A' x) = ι x := fun x => IsLocalization.lift_eq (M := 𝔭.primeCompl) hunitA x

  have hunitK : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap O K₀ y) := by
    rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr fun h0 => hy ?_
    have : y = 0 := (IsFractionRing.injective O K₀) (by rw [map_zero]; exact h0)
    rw [this]; exact Ideal.zero_mem _
  let ψK : A' →+* K₀ := IsLocalization.lift (M := 𝔭.primeCompl) hunitK
  have hψK : ∀ x : O, ψK (algebraMap O A' x) = algebraMap O K₀ x := fun x =>
    IsLocalization.lift_eq (M := 𝔭.primeCompl) hunitK x
  letI algA : Algebra A' A := ψA.toAlgebra
  letI algK : Algebra A' K₀ := ψK.toAlgebra
  letI algL : Algebra A' L := ((algebraMap K₀ L).comp ψK).toAlgebra
  haveI : IsScalarTower O A' K₀ := IsScalarTower.of_algebraMap_eq fun x => (hψK x).symm
  haveI : IsScalarTower A' K₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A' A L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show ((algebraMap K₀ L).comp ψK) x = ((algebraMap A L).comp ψA) x
    refine congrFun (congrArg DFunLike.coe
      (IsLocalization.ringHom_ext (M := 𝔭.primeCompl) (j := (algebraMap K₀ L).comp ψK)
        (k := (algebraMap A L).comp ψA) ?_)) x
    ext y
    simp only [RingHom.comp_apply, hψK, hψA, hι]
    rfl
  haveI : IsFractionRing A' K₀ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl A' K₀

  have hinj : Function.Injective (algebraMap A' A) := by
    show Function.Injective (IsLocalization.lift (M := 𝔭.primeCompl) hunitA)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [hOA'.eq_iff]
    exact ⟨fun h => by rw [h], fun h => hιinj h⟩
  have hm𝔭 : IsLocalRing.maximalIdeal A' = 𝔭.map (algebraMap O A') := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hloc : (IsLocalRing.maximalIdeal A).comap (algebraMap A' A) = IsLocalRing.maximalIdeal A' := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _))) ?_
    rw [hm𝔭, Ideal.map_le_iff_le_comap]
    intro x hx
    show ψA (algebraMap O A' x) ∈ IsLocalRing.maximalIdeal A
    rw [hψA]; exact hx
  have hqA' : ((q : ℕ) : A') ∈ IsLocalRing.maximalIdeal A' := by
    rw [hm𝔭, ← map_natCast (algebraMap O A')]; exact Ideal.mem_map_of_mem _ hq𝔭
  have hfin : Finite (IsLocalRing.ResidueField A') := by
    haveI : Finite (O ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭0
    exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝔭).surjective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A'
  have hϖ' : IsLocalRing.maximalIdeal A' = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  obtain ⟨ε, hε, hϖε⟩ :=
    IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing q ℓ hℓq.symm K₀ A' hqA' ϖ hϖ'
  have hξO : IsIntegral ℤ ξ₀ := hξ₀.isIntegral (Nat.pos_of_ne_zero hne.ne)
  refine ⟨A', inferInstance, inferInstance, inferInstance, algA, algL, inferInstance, algK, inferInstance, inferInstance,
    hinj, hloc, hqA', hfin, ⟨ϖ, ε, hϖ', hε, hϖε⟩, ⟨algebraMap O A' ⟨ξ₀, hξO⟩, ?_⟩⟩
  show (algebraMap K₀ L) (ψK (algebraMap O A' ⟨ξ₀, hξO⟩)) = ξ
  rw [hψK]
  rfl

end S_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot (solution)
