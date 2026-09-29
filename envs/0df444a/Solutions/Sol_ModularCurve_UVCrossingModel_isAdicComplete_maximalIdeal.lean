-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8afbce7c-0cf6-5059-80ed-d9d24b96c0d6

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace LinCompl

theorem map_maximalIdeal_eq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  ·
    intro s hs
    by_contra hsu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hsu
    have htop : (IsLocalRing.maximalIdeal R).map f = ⊤ := Ideal.eq_top_of_isUnit_mem _ hs hsu
    have h1 : (1 : S) ∈ (IsLocalRing.maximalIdeal R).map f := htop ▸ Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective f hf] at h1
    obtain ⟨r, hr, hr1⟩ := h1
    have hu : IsUnit (1 - r) := by
      by_contra h
      have h2 : (1 : R) - r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have e : (1 : R) = (1 - r) + r := by ring
        rw [e]; exact Ideal.add_mem _ h2 hr
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
    have h0 : f (1 - r) = 0 := by rw [map_sub, map_one, hr1, sub_self]
    exact not_isUnit_zero (h0 ▸ hu.map f)
  · intro s hs
    obtain ⟨r, rfl⟩ := hf s
    have hr : r ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
      exact fun hu => hs (hu.map f)
    exact Ideal.mem_map_of_mem f hr

end LinCompl

theorem solution
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] [IsNoetherianRing Ô]
    [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô] (π : Ô)
    [IsLocalRing (UVCrossingModel Ô π)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) Ô) := MvPowerSeries.isNoetherianRing_fin Ô 2
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) Ô)) (MvPowerSeries (Fin 2) Ô) :=
    MvPowerSeries.isAdicComplete_maximalIdeal
  have h := IsLocalRing.isAdicComplete_map_maximalIdeal_quotient (R := MvPowerSeries (Fin 2) Ô) (uvCrossingIdeal Ô π)
  rw [LinCompl.map_maximalIdeal_eq (Ideal.Quotient.mk (uvCrossingIdeal Ô π)) Ideal.Quotient.mk_surjective] at h
  exact h

end S_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal (solution)
