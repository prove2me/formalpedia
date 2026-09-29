-- Prove2me | solution 1 for IsDiscreteValuationRing.relIndex_principalUnits_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bd747dee-ab16-55ae-a56e-ab1416ee37c3

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_succ

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits R (k + 1)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπk : π ^ k ≠ 0 := pow_ne_zero k hπ0
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ n = Ideal.span {π ^ n} := fun n => by
    rw [hmax, Ideal.span_singleton_pow]

  have hdvd : ∀ u : principalUnits R k, ∃ r : R, ((u : Rˣ) : R) - 1 = π ^ k * r := fun u => by
    have h := u.2
    rw [mem_principalUnits_iff, hpow, Ideal.mem_span_singleton] at h
    exact h
  choose d hd using hdvd

  have hd_mul : ∀ u v : principalUnits R k, d (u * v) = d u + d v + π ^ k * (d u * d v) := by
    intro u v
    apply mul_left_cancel₀ hπk
    rw [← hd (u * v)]
    calc (((u * v : principalUnits R k) : Rˣ) : R) - 1
        = (((u : Rˣ) : R) - 1) + (((v : Rˣ) : R) - 1) + (((u : Rˣ) : R) - 1) * (((v : Rˣ) : R) - 1) := by
          push_cast; ring
      _ = π ^ k * (d u + d v + π ^ k * (d u * d v)) := by rw [hd u, hd v]; ring
  have hd_one : d 1 = 0 := by
    apply mul_left_cancel₀ hπk
    rw [← hd 1, mul_zero]; push_cast; ring

  let Φ : principalUnits R k →* Multiplicative (IsLocalRing.ResidueField R) :=
    { toFun := fun u => Multiplicative.ofAdd (IsLocalRing.residue R (d u))
      map_one' := by simp only [hd_one, map_zero, ofAdd_zero]
      map_mul' := by
        intro u v
        have hz : IsLocalRing.residue R (π ^ k * (d u * d v)) = 0 := by
          rw [IsLocalRing.residue_eq_zero_iff, hmax]
          exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) _ hk)
        simp only [hd_mul, map_add, hz, add_zero, ofAdd_add] }
  have hΦ : ∀ u, Φ u = Multiplicative.ofAdd (IsLocalRing.residue R (d u)) := fun u => rfl

  have hker : Φ.ker = (principalUnits R (k + 1)).subgroupOf (principalUnits R k) := by
    ext u
    rw [MonoidHom.mem_ker, hΦ, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq,
      IsLocalRing.residue_eq_zero_iff, Subgroup.mem_subgroupOf, mem_principalUnits_iff, hd u, hpow, hmax,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left hπk]

  have hsurj : Function.Surjective Φ := by
    intro m
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd m)
    have hx : π ^ k * r ∈ IsLocalRing.maximalIdeal R ^ k := by
      rw [hpow, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
    obtain ⟨u, hu, hux⟩ := IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq hk hx
    refine ⟨⟨u, hu⟩, ?_⟩
    have hdu : d ⟨u, hu⟩ = r := mul_left_cancel₀ hπk (by rw [← hd ⟨u, hu⟩]; exact hux)
    rw [hΦ, hdu, hr]; rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  rfl

end S_IsDiscreteValuationRing_relIndex_principalUnits_succ
end P2MW
export P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_succ (solution)
