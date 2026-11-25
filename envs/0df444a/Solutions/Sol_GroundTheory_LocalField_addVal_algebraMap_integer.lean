-- Prove2me | solution 1 for GroundTheory.LocalField.addVal_algebraMap_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:50.844056+00:00
-- url     : https://prove2.me/submissions/8ada7082-bece-4ce7-87c3-0592ed63e48c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (x : 𝒪[K]) :
    addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) = ramificationIndex K L * addVal 𝒪[K] x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]
  have key : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] ϖ) = ramificationIndex K L := by
    have h := map_maximalIdeal K L
    rw [hϖ.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    rw [(addVal_eq_iff_associated _ _).mpr h, hϖL.addVal_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top]
    exact_mod_cast (ramificationIndex_pos K L).ne'
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [map_mul, map_pow, addVal_mul, addVal_pow, key, addVal_def' u hϖ k]
  have hu : IsUnit (algebraMap 𝒪[K] 𝒪[L] u) := u.isUnit.map _
  rw [addVal_eq_zero_iff.mpr hu, zero_add, nsmul_eq_mul, mul_comm]
end GroundTheory.LocalField
