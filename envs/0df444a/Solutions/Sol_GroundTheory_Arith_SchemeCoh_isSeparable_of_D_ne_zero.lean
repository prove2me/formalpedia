-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isSeparable_of_D_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:14.462001+00:00
-- url     : https://prove2.me/submissions/ccaf80bc-0596-462c-95a2-12fc4dd60f0b

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_span_D_eq_top_of_ne_zero
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {z : K} (hz : D k K z ≠ 0) : Algebra.IsSeparable k⟮z⟯ K := by
  have hsub : Subsingleton Ω[K⁄k⟮z⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective k k⟮z⟯ K ω'
    have hω : ω ∈ Submodule.span K {D k K z} := by rw [span_D_eq_top_of_ne_zero hz]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    have h0 : D k⟮z⟯ K z = 0 := (D k⟮z⟯ K).map_algebraMap ⟨z, mem_adjoin_simple_self k z⟩
    simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h0, smul_zero]
  have : Algebra.FormallyUnramified k⟮z⟯ K := ⟨hsub⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Algebra.EssFiniteType k⟮z⟯ K := .of_comp k k⟮z⟯ K
  exact Algebra.FormallyUnramified.isSeparable k⟮z⟯ K
end GroundTheory.Arith.SchemeCoh
