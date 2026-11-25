-- Prove2me | solution 1 for GroundTheory.ProfCoh.pow_mem_unitFiltration_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:04.135803+00:00
-- url     : https://prove2.me/submissions/f2979828-8d2b-4f6f-ada0-c8f7fb50706c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Theorems.Thm_GroundTheory_ProfCoh_one_add_pow_sub_one_eq
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe
namespace GroundTheory.ProfCoh
theorem _root_.solution {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) :
    u ^ p ∈ unitFiltration K (j + e + 1) ↔ u ∈ unitFiltration K (j + 1) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  have hu' : (u : 𝒪[K]) = 1 + ϖ ^ j * a := by simp only at ha; rw [← ha]; ring
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val, hu', hw,
    mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, hu', add_sub_cancel_left, pow_succ,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero),
    mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero), dvd_add_left (dvd_mul_right ϖ w),
    Units.dvd_mul_left]
end GroundTheory.ProfCoh
