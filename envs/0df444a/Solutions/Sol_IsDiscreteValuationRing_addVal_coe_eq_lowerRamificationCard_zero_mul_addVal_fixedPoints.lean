-- Prove2me | solution 1 for IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f2edf044-ef2f-5362-b618-90001b3b66dd

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup
import Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints

set_option autoImplicit false

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace HerbrandPortG3

theorem module_finite_fixedPoints_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] [FaithfulSMul H R]
    [IsNoetherianRing (FixedPoints.subring R H)] [IsIntegrallyClosed (FixedPoints.subring R H)] :
    Module.Finite (FixedPoints.subring R H) R := by
  haveI : IsGaloisGroup H (FixedPoints.subring R H) R := FixedPoints.isGaloisGroup_subring
  letI := IsFractionRing.mulSemiringAction H R (FractionRing R)
  haveI hG : IsGaloisGroup H (FractionRing (FixedPoints.subring R H)) (FractionRing R) :=
    IsGaloisGroup.toFractionRing H (FixedPoints.subring R H) R
  haveI := IsGaloisGroup.finiteDimensional H (FractionRing (FixedPoints.subring R H)) (FractionRing R)
  haveI := IsGaloisGroup.isGalois H (FractionRing (FixedPoints.subring R H)) (FractionRing R)
  haveI : Algebra.IsIntegral (FixedPoints.subring R H) R :=
    Algebra.IsInvariant.isIntegral (FixedPoints.subring R H) R H
  exact IsIntegralClosure.finite (FixedPoints.subring R H)
    (FractionRing (FixedPoints.subring R H)) (FractionRing R) R

theorem addVal_algebraMap_irreducible_eq_ramificationIdx
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    (hf : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π) :
    IsDiscreteValuationRing.addVal S (algebraMap R S π) =
      ((IsLocalRing.maximalIdeal R).ramificationIdx' (IsLocalRing.maximalIdeal S) : ℕ∞) := by
  open IsDiscreteValuationRing in
  have hfπ : algebraMap R S π ≠ 0 := fun h => hπ.ne_zero (hf (h.trans (map_zero _).symm))
  obtain ⟨e, he⟩ :=
    WithTop.ne_top_iff_exists.mp (fun h => hfπ (addVal_eq_top_iff.mp h))
  have hmap :
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) = Ideal.span {algebraMap R S π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have key : ∀ n, (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      (IsLocalRing.maximalIdeal S) ^ n ↔ n ≤ e := fun n => by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
    rw [hmap, Ideal.span_singleton_le_iff_mem, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, ← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hϖ,
      nsmul_one, ← he]
    exact Nat.cast_le
  exact he.symm.trans (congrArg Nat.cast (Ideal.ramificationIdx_spec
    ((key e).mpr le_rfl) ((key (e + 1)).not.mpr e.not_succ_le_self)).symm)

theorem addVal_map_eq_mul_of_irreducible {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] [IsDiscreteValuationRing R]
    [IsDiscreteValuationRing S] (f : S →+* R) {π : S} (hπ : Irreducible π)
    {e : ℕ} (he : e ≠ 0) (hval : IsDiscreteValuationRing.addVal R (f π) = e) (y : S) :
    IsDiscreteValuationRing.addVal R (f y) = e * IsDiscreteValuationRing.addVal S y := by
  open IsDiscreteValuationRing in
  by_cases hy : y = 0
  · subst hy
    have : ((e : ℕ∞)) ≠ 0 := by exact_mod_cast he
    simp [ENat.mul_top this]
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hy hπ
    have hu : addVal R (f (u : S)) = 0 := by
      rw [← le_zero_iff, ← (addVal R).map_one, addVal_le_iff_dvd]
      exact (u.isUnit.map f).dvd
    have hu' : addVal S (u : S) = 0 := by
      rw [← le_zero_iff, ← (addVal S).map_one, addVal_le_iff_dvd]
      exact u.isUnit.dvd
    rw [map_mul, map_pow, addVal_mul, addVal_pow, hu, zero_add, addVal_mul, addVal_pow, hu',
      zero_add, addVal_uniformizer hπ, hval, nsmul_one, nsmul_eq_mul, mul_comm]

end HerbrandPortG3

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] [FaithfulSMul H R]
    [IsDiscreteValuationRing (FixedPoints.subring R H)]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R H))]
    [Algebra.IsSeparable
      (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (z : FixedPoints.subring R H) :
    IsDiscreteValuationRing.addVal R (z : R) =
      (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
        IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z := by
  haveI : Module.Finite (FixedPoints.subring R H) R :=
    HerbrandPortG3.module_finite_fixedPoints_subring
  haveI : IsGaloisGroup H (FixedPoints.subring R H) R := FixedPoints.isGaloisGroup_subring
  have hp : IsLocalRing.maximalIdeal (FixedPoints.subring R H) ≠ ⊥ := by
    simpa using (Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
      (IsDiscreteValuationRing.not_isField _))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (FixedPoints.subring R H)
  have hπval : IsDiscreteValuationRing.addVal R (algebraMap (FixedPoints.subring R H) R π) =
      (IsLocalRing.lowerRamificationCard R H 0 : ℕ) := by
    rw [HerbrandPortG3.addVal_algebraMap_irreducible_eq_ramificationIdx Subtype.coe_injective hπ,
      Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal (FixedPoints.subring R H))
        (IsLocalRing.maximalIdeal R) hp,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx
        (IsLocalRing.maximalIdeal (FixedPoints.subring R H)) (IsLocalRing.maximalIdeal R) H,
      ← card_lowerRamificationGroup_zero_eq_ramificationIdxIn (G := H) hp,
      IsLocalRing.lowerRamificationCard]
  have hne : IsLocalRing.lowerRamificationCard R H 0 ≠ 0 := by
    haveI : Finite (IsLocalRing.lowerRamificationGroup R H 0) := inferInstance
    exact Nat.card_pos.ne'
  exact HerbrandPortG3.addVal_map_eq_mul_of_irreducible
    (algebraMap (FixedPoints.subring R H) R) hπ hne hπval z

end S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
end P2MW
export P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints (solution)
