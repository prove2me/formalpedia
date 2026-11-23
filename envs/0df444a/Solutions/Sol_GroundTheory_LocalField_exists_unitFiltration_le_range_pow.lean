-- Prove2me | solution 1 for GroundTheory.LocalField.exists_unitFiltration_le_range_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:51.752202+00:00
-- url     : https://prove2.me/submissions/9f46d5e6-3e02-4b94-b105-124920f21b9c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_of_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℕ} (hm : (m : K) ≠ 0) :
    ∃ N, unitFiltration K N ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm' : (m : 𝒪[K]) ≠ 0 := fun h ↦ hm (by have := congrArg Subtype.val h; simpa using this)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k, ε, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm' hϖ
  refine ⟨2 * k + 1, fun w hw ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (ε := ε) (by rw [hk, mul_comm]) hw
  exact ⟨x, hx⟩
end GroundTheory.LocalField
