-- Prove2me | solution 1 for IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2398f0f6-6cc8-52e7-ba01-0661b2bd2025

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing

set_option autoImplicit false

open IsLocalRing

theorem solution
    {O' O F : Type*} [CommRing O'] [IsNoetherianRing O'] [IsLocalRing O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O' O] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F]
    [IsFractionRing O F] [IsFractionRing O' F]
    [IsLocalHom (algebraMap O' O)] [Module.Flat O' O]
    (hinj : Function.Injective (algebraMap O' O))
    (π : O') (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime) :
    Function.Bijective (algebraMap O' O) := by
  classical
  haveI : IsDomain O' := Function.Injective.isDomain (algebraMap O' O) hinj
  haveI := hπ

  have hπu : ¬ IsUnit π := by
    intro hu
    apply hπ.ne_top
    rw [Ideal.eq_top_iff_one]
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : v * π ∈ Ideal.span {π} := Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    rwa [hv] at this
  have hπm : π ∈ maximalIdeal O' := (mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπu)
  have hnf : ¬ IsField O' := fun hF => by
    have h := isField_iff_maximalIdeal_eq.mp hF
    rw [h, Ideal.mem_bot] at hπm
    exact hπ0 hπm

  have hunder : (maximalIdeal O).under O' = maximalIdeal O' := by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]
  haveI : (maximalIdeal O).LiesOver (maximalIdeal O') := ⟨hunder.symm⟩

  have hle : Ideal.span {π} ≤ maximalIdeal O' := (Ideal.span_singleton_le_iff_mem _).mpr hπm
  obtain ⟨P, hPle, hPprime, hPover⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal O) hle
  have hPne : P ≠ ⊥ := by
    intro hP
    have h1 : (P.under O') = Ideal.span {π} := hPover.over.symm
    rw [hP, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj] at h1
    exact hπ0 (Ideal.span_singleton_eq_bot.mp h1.symm)
  have hPmax : P = maximalIdeal O := by
    haveI := hPprime
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal hPprime hPne)
  have hmax : maximalIdeal O' = Ideal.span {π} := by
    rw [← hunder, ← hPmax]; exact hPover.over.symm

  have hprinc : (maximalIdeal O').IsPrincipal := ⟨⟨π, by rw [hmax]⟩⟩
  haveI : ValuationRing O' := ((IsDiscreteValuationRing.TFAE O' hnf).out 4 1).mp hprinc

  refine ⟨hinj, fun x => ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  have hinjO : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  rcases ValuationRing.isInteger_or_isInteger O' (algebraMap O F x) with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨a, hinjO ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; exact ha
  ·
    have hx' : algebraMap O F x ≠ 0 := fun h => hx (hinjO (by rw [h, map_zero]))
    have hmul : algebraMap O' O a * x = 1 := by
      apply hinjO
      rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply, ha, inv_mul_cancel₀ hx']
    have hau : IsUnit a := (isUnit_map_iff (algebraMap O' O) a).mp (IsUnit.of_mul_eq_one _ hmul)
    obtain ⟨u, rfl⟩ := hau
    refine ⟨(u⁻¹ : O'ˣ), ?_⟩
    have : algebraMap O' O (u : O') * algebraMap O' O (↑u⁻¹ : O') = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc algebraMap O' O (↑u⁻¹ : O') = algebraMap O' O (↑u⁻¹ : O') * (algebraMap O' O (u : O') * x) := by rw [hmul, mul_one]
      _ = (algebraMap O' O (u : O') * algebraMap O' O (↑u⁻¹ : O')) * x := by ring
      _ = x := by rw [this, one_mul]

end S_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
end P2MW
export P2MW.S_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing (solution)
