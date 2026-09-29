-- Prove2me | solution 1 for MvPowerSeries.expand_sub_pow_mem_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2c7755ae-652d-5be7-b231-0548beb57e20

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_expand_sub_pow_mem_span_natCast

set_option autoImplicit false

namespace S17LC

open MvPowerSeries

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {σ : Type*}

omit hp in

theorem mem_span_natCast_of_forall_coeff_mem {g : MvPowerSeries σ 𝓞}
    (h : ∀ m, coeff m g ∈ Ideal.span {(p : 𝓞)}) : g ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} := by
  choose b hb using fun m => Ideal.mem_span_singleton'.1 (h m)
  refine Ideal.mem_span_singleton'.2 ⟨(fun m => b m : MvPowerSeries σ 𝓞), ?_⟩
  ext m
  rw [← map_natCast (C (σ := σ) (R := 𝓞)) p, coeff_mul_C, ← hb m]
  rfl

theorem expand_sub_pow_mem (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)}) (f : MvPowerSeries σ 𝓞) :
    expand p hp.out.ne_zero f - f ^ p ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} := by
  apply mem_span_natCast_of_forall_coeff_mem
  by_cases hu : IsUnit (p : 𝓞)
  · intro m
    rw [Ideal.span_singleton_eq_top.2 hu]
    exact Submodule.mem_top
  · haveI : CharP (𝓞 ⧸ Ideal.span {(p : 𝓞)}) p := CharP.quotient 𝓞 p (mem_nonunits_iff.2 hu)
    have hfr : frobenius (𝓞 ⧸ Ideal.span {(p : 𝓞)}) p = RingHom.id _ := by
      refine RingHom.ext fun x => ?_
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [frobenius_def, RingHom.id_apply, ← map_pow, Ideal.Quotient.eq]
      exact hfrob c
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, map_pow, map_expand,
      ← map_frobenius_expand p hp.out.ne_zero (f := map (Ideal.Quotient.mk _) f), hfr, map_id,
      RingHom.id_apply, sub_self, map_zero]

end S17LC

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {σ : Type v} (f : MvPowerSeries σ 𝓞) :
    MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero f - f ^ p ∈
      Ideal.span {(p : MvPowerSeries σ 𝓞)} :=
  S17LC.expand_sub_pow_mem hfrob f

end S_MvPowerSeries_expand_sub_pow_mem_span_natCast
end P2MW
export P2MW.S_MvPowerSeries_expand_sub_pow_mem_span_natCast (solution)
