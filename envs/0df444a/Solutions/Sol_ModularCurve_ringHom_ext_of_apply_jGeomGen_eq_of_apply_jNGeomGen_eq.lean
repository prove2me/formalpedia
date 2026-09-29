-- Prove2me | solution 1 for ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b6cbaff6-2aec-5d89-8f8d-a784abb1c027

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq

set_option autoImplicit false

open ModularCurve

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] {S : Type*} [DivisionRing S]
    (φ ψ : ↥(modularFunctionFieldC K N) →+* S)
    (hK : ∀ a : K, φ (algebraMap K ↥(modularFunctionFieldC K N) a) = ψ (algebraMap K ↥(modularFunctionFieldC K N) a))
    (hj : φ (jGeomGen K N) = ψ (jGeomGen K N)) (hjN : φ (jNGeomGen K N) = ψ (jNGeomGen K N)) :
    φ = ψ := by

  let E : IntermediateField K ↥(modularFunctionFieldC K N) :=
    { toSubalgebra :=
        { carrier := {x | φ x = ψ x}
          mul_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
          one_mem' := by simp only [Set.mem_setOf_eq, map_one]
          add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
          zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
          algebraMap_mem' := hK }
      inv_mem' := fun x hx => by
        change φ x = ψ x at hx
        show φ x⁻¹ = ψ x⁻¹
        rw [map_inv₀, map_inv₀, hx] }

  have hgens : ({⟨jqModC K, jqModC_mem K N⟩, ⟨jqNModC K N, jqNModC_mem K N⟩} : Set ↥(modularFunctionFieldC K N)) ⊆ E := by
    rintro y (rfl | rfl)
    · exact hj
    · exact hjN
  have hle : modularFunctionFieldC K N ≤
      IntermediateField.lift (F := modularFunctionFieldC K N) (IntermediateField.adjoin K
        ({⟨jqModC K, jqModC_mem K N⟩, ⟨jqNModC K N, jqNModC_mem K N⟩} : Set ↥(modularFunctionFieldC K N))) := by
    change IntermediateField.adjoin K {jqModC K, jqNModC K N} ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact ⟨⟨jqModC K, jqModC_mem K N⟩, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _), rfl⟩
    · exact ⟨⟨jqNModC K N, jqNModC_mem K N⟩, IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl), rfl⟩
  have htop : IntermediateField.adjoin K
      ({⟨jqModC K, jqModC_mem K N⟩, ⟨jqNModC K N, jqNModC_mem K N⟩} : Set ↥(modularFunctionFieldC K N)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [← Subtype.ext hyx]
  have hE : E = ⊤ := eq_top_iff.mpr (htop ▸ IntermediateField.adjoin_le_iff.mpr hgens)
  refine RingHom.ext fun x => ?_
  have hx : x ∈ E := hE ▸ IntermediateField.mem_top
  exact hx

end S_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
end P2MW
export P2MW.S_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq (solution)
