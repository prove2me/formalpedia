-- Prove2me | solution 1 for HeckeCharacter.exists_isAdjuster
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/60fe3e73-18e1-5e5c-b2fb-eb4cf80cb7f2

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
import Theorems.Thm_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff
import Theorems.Thm_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff
import Theorems.Thm_HeckeCharacter_exists_forall_dvd_valued_mul_inv_eq_one_and_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_isAdjuster

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  have h𝔣0 : 𝔣 ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  set p : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) with hp

  obtain ⟨α₀, hα₀⟩ := HeckeCharacter.exists_forall_dvd_valued_mul_inv_eq_one_and_le K 𝔣 h𝔣 u
  set u₁ : (AdeleRing (𝓞 K) K)ˣ := u * (p α₀)⁻¹ with hu₁

  obtain ⟨β, hβ0, hβ1, hβsgn⟩ :=
    HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff K 𝔣 h𝔣 fun τ => archSign K τ u₁
  have hβK : (β : K) ≠ 0 := fun h => hβ0 (by exact_mod_cast h)
  set βu : Kˣ := Units.mk0 (β : K) hβK with hβu

  refine ⟨α₀ * βu⁻¹, ?_⟩
  have hprod : u * (p (α₀ * βu⁻¹))⁻¹ = p βu * u₁ := by
    rw [hu₁, map_mul, map_inv, mul_inv_rev, inv_inv]
    ac_rfl

  have hβloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((((p βu : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v ((((p βu : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
    intro v hv
    have hc := (HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔣 h𝔣 (β - 1)).mp hβ1 v hv
    have hcomp : (((p βu : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
        (algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v := by
      rw [hp, Units.coe_map, MonoidHom.coe_coe, hβu, Units.val_mk0]
      rfl
    have hsub : (algebraMap K (FiniteAdeleRing (𝓞 K) K) (((β - 1 : 𝓞 K)) : K)) v =
        (algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v - 1 := by
      rw [show (((β - 1 : 𝓞 K)) : K) = (β : K) - 1 by push_cast; ring, map_sub, map_one]
      rfl
    rw [hsub] at hc
    rw [hcomp]
    refine ⟨?_, hc⟩

    have hn : (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd h𝔣0 v.irreducible).mpr hv
    have hlt : Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v - 1) < 1 := by
      refine lt_of_le_of_lt hc ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [← (Valued.v : Valuation (v.adicCompletion K) _).map_one] at hlt ⊢
    exact Valuation.map_eq_of_sub_lt _ hlt
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · rw [hprod, Units.val_mul]
    change Valued.v ((((p βu : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
        (((u₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v ((((p βu : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
        (((u₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
    exact unit_cong_mul K (hβloc v hv).1 (hβloc v hv).2 (hα₀ v hv).1 (hα₀ v hv).2
  · rw [hprod, HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff]
    rw [hβu, Units.val_mk0]
    exact hβsgn τ

end S_HeckeCharacter_exists_isAdjuster
end P2MW
export P2MW.S_HeckeCharacter_exists_isAdjuster (solution)
