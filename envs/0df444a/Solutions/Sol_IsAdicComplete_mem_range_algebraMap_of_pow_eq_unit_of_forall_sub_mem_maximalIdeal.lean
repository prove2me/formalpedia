-- Prove2me | solution 1 for IsAdicComplete.mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f8b4fc2b-1e41-59d0-a26e-7bc934e4cfac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing Polynomial

open IsLocalRing Polynomial

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) (w : Rˣ)
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (β : B) (hβ : β ^ e = algebraMap R B w) :
    β ∈ Set.range (algebraMap R B) := by
  classical

  obtain ⟨r₀, hr₀⟩ := hres β
  have hloc : ∀ x : R, algebraMap R B x ∈ maximalIdeal B → x ∈ maximalIdeal R := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  have hwB : IsUnit (algebraMap R B (w : R)) := (Units.isUnit w).map _

  have hβu : IsUnit β := by
    have : IsUnit (β ^ e) := by rw [hβ]; exact hwB
    exact (isUnit_pow_iff he.ne').mp this
  have hr₀B : IsUnit (algebraMap R B r₀) := by
    by_contra hnu
    have h1 : algebraMap R B r₀ ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : β ∈ maximalIdeal B := by
      have := Ideal.add_mem _ hr₀ h1; rwa [sub_add_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hβu
  have hr₀u : IsUnit r₀ := (isUnit_map_iff (algebraMap R B) r₀).mp hr₀B

  let f : R[X] := X ^ e - C (w : R)
  have hfm : f.Monic := monic_X_pow_sub_C (w : R) he.ne'
  have hfeval : ∀ a : R, f.eval a = a ^ e - w := fun a => by simp [f]
  have hfd : ∀ a : R, f.derivative.eval a = (e : R) * a ^ (e - 1) := fun a => by
    simp [f, derivative_X_pow]
  have h1 : f.eval r₀ ∈ maximalIdeal R := by
    apply hloc
    rw [hfeval, map_sub, map_pow, ← hβ]

    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (algebraMap R B r₀) β e
    rw [hc]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← neg_sub]; exact (maximalIdeal B).neg_mem hr₀
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval r₀)) := by
    refine IsUnit.map _ ?_
    rw [hfd]
    exact heR.mul (hr₀u.pow _)
  obtain ⟨r, hr, hrr₀⟩ := (IsAdicComplete.henselianRing R (maximalIdeal R)).is_henselian f hfm r₀ h1 h2
  have hre : r ^ e = w := by
    have := hr
    rw [Polynomial.IsRoot, hfeval, sub_eq_zero] at this
    exact this

  have hrB : IsUnit (algebraMap R B r) := by
    have : IsUnit (r ^ e) := by rw [hre]; exact Units.isUnit w
    exact ((isUnit_pow_iff he.ne').mp this).map _
  obtain ⟨ri, hri⟩ := hrB.exists_right_inv
  let ζ : B := β * ri
  have hζe : ζ ^ e = 1 := by
    show (β * ri) ^ e = 1
    rw [mul_pow, hβ, ← hre, map_pow, ← mul_pow, hri, one_pow]
  have hζ1 : ζ - 1 ∈ maximalIdeal B := by
    have e1 : ζ - 1 = (β - algebraMap R B r) * ri := by
      show β * ri - 1 = _
      rw [sub_mul, hri]
    rw [e1]
    refine Ideal.mul_mem_right _ _ ?_
    have : β - algebraMap R B r = (β - algebraMap R B r₀) - algebraMap R B (r - r₀) := by rw [map_sub]; ring
    rw [this]
    refine Ideal.sub_mem _ hr₀ ?_

    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hrr₀ ((isUnit_map_iff (algebraMap R B) _).mp hu)

  have hgeom : IsUnit (∑ i ∈ Finset.range e, ζ ^ i) := by
    by_contra hnu
    have hm : (∑ i ∈ Finset.range e, ζ ^ i) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hdiff : (∑ i ∈ Finset.range e, ζ ^ i) - (e : B) ∈ maximalIdeal B := by
      rw [show (e : B) = ∑ i ∈ Finset.range e, (1 : B) by simp, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ζ 1 i
      rw [one_pow] at hc
      rw [hc]; exact Ideal.mul_mem_right _ _ hζ1
    have heB : IsUnit ((e : ℕ) : B) := by
      have := heR.map (algebraMap R B); rwa [map_natCast] at this
    have : ((e : ℕ) : B) ∈ maximalIdeal B := by
      have := Ideal.sub_mem _ hm hdiff; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this heB
  have hζ : ζ = 1 := by
    have : (ζ - 1) * ∑ i ∈ Finset.range e, ζ ^ i = 0 := by rw [mul_geom_sum, hζe, sub_self]
    rw [← sub_eq_zero]
    exact (hgeom.mul_left_eq_zero).mp this
  refine ⟨r, ?_⟩

  calc algebraMap R B r = ζ * algebraMap R B r := by rw [hζ, one_mul]
    _ = β := by show β * ri * algebraMap R B r = β; rw [mul_assoc, mul_comm ri, hri, mul_one]

end S_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
end P2MW
export P2MW.S_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal (solution)
