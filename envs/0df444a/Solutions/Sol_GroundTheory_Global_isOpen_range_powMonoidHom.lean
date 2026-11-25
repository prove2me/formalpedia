-- Prove2me | solution 1 for GroundTheory.Global.isOpen_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:58.791884+00:00
-- url     : https://prove2.me/submissions/0a6f04f8-ed07-41d3-a98d-477618b56b71

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_map_powMonoidHom_unitFiltration
import Theorems.Thm_GroundTheory_Global_exists_natCast_eq_unit_mul_pow
import Theorems.Thm_GroundTheory_Global_uniformizer_pow_succ_dvd_of_valuation_lt
import Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff


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
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, -⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  set B : Set K := {y | valuation K (y - 1) < valuation K ((ϖ : K) ^ (d + d))}
  have hB : B ∈ nhds (1 : K) := by
    refine (IsValuativeTopology.hasBasis_nhds' (1 : K)).mem_of_mem ?_
    rw [Ne, Valuation.zero_iff]
    exact pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have hB' : Units.val ⁻¹' B ∈ nhds (1 : Kˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hB)
  refine Filter.mem_of_superset hB' fun x hx ↦ ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, B] at hx
  have hlt1 : valuation K ((x : K) - 1) < 1 := by
    refine hx.trans_le ?_
    rw [map_pow]
    exact pow_le_one' ϖ.2 _
  have hy : (x : K) - 1 ∈ 𝒪[K] := hlt1.le
  have hv1 : valuation K (x : K) = 1 := by
    have := Valuation.map_add_eq_of_lt_right (valuation K) (x := (x : K) - 1) (y := 1)
      (by rwa [map_one])
    rwa [sub_add_cancel, map_one] at this
  have hnv : normalizedValuation K (x : K) = 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one, hv1]
  obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hnv
  have hu : u ∈ unitFiltration K (d + 1 + d) := by
    rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
    have e1 : d + 1 + d = d + d + 1 := by omega
    rw [e1]
    apply uniformizer_pow_succ_dvd_of_valuation_lt hϖ
    simpa using hx
  rw [← map_powMonoidHom_unitFiltration hϖ hnd] at hu
  obtain ⟨w, -, rfl⟩ := hu
  exact ⟨unitsIncl K w, by simp⟩
end GroundTheory.Global
