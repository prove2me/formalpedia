-- Prove2me | solution 1 for GroundTheory.LocalField.inertiaSubgroup_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:44.037288+00:00
-- url     : https://prove2.me/submissions/32d18b2f-e87b-449e-bb37-6d996ab63f8d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue



set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by
  set γσ := integerAlgEquiv K L σ γ
  have h0 : aeval γσ P = 0 := by
    have := aeval_algHom_apply (integerAlgEquiv K L σ : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) γ P
    rw [hγ, map_zero] at this
    exact this
  have hres : residue 𝒪[L] γσ = residue 𝒪[L] γ := by
    have h1 : residueAlgEquiv K L σ = 1 := hσ
    rw [← residueAlgEquiv_residue, h1]
    rfl
  have heq : γ = γσ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact h0) ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [← coe_integerAlgEquiv_apply]
  exact congrArg Subtype.val heq.symm
end GroundTheory.LocalField
