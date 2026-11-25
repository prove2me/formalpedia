-- Prove2me | solution 1 for GroundTheory.Global.eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:51.3188+00:00
-- url     : https://prove2.me/submissions/ecdf7d76-3362-4a5e-8cf9-f41f4336fcbb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration
import Theorems.Thm_GroundTheory_Global_exists_units_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
namespace GroundTheory.Global
theorem _root_.solution {u : 𝒪[K]ˣ} (hu : u ∈ unitFiltration K (d + 1)) (hun : u ^ n = 1) :
    u = 1 := by
  classical
  by_contra hu1
  have hex : ∃ k, u ∉ unitFiltration K k := by
    by_contra h
    push Not at h
    exact hu1 (filtrationSeparated_unitFiltration u h)
  have hJ := Nat.find_spec hex
  have hJmin : ∀ k < Nat.find hex, u ∈ unitFiltration K k := fun k hk ↦ by
    have := Nat.find_min hex hk
    simpa using this
  have hJd : d + 1 < Nat.find hex := by
    by_contra hle
    exact hJ (unitFiltration_antitone K (not_lt.mp hle) hu)
  obtain ⟨j, hjJ⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have huj : u ∈ unitFiltration K j := hJmin j (by omega)
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖ).mp huj
  have hnot : ¬ ϖ ∣ a := by
    rintro ⟨b, rfl⟩
    apply hJ
    rw [hjJ, mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, ha, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd (j := j) (by omega) ha
  rw [hun, Units.val_one, left_eq_add, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact pow_ne_zero _ hϖ.ne_zero hc
  · apply hnot
    refine ⟨-((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c, ?_⟩
    linear_combination ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * hc - a * (Units.inv_mul ε)
end GroundTheory.Global
