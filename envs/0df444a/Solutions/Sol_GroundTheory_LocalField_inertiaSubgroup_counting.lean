-- Prove2me | solution 1 for GroundTheory.LocalField.inertiaSubgroup_counting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:34.36991+00:00
-- url     : https://prove2.me/submissions/43a06272-c21a-4e3b-9f19-ceb3c99712a9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_finrank_maximalUnramified
import Theorems.Thm_GroundTheory_LocalField_maximalUnramified_le_fixedField
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos


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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.card (inertiaSubgroup K L) = ramificationIndex K L ∧
      Nat.card (residueAlgEquiv K L).range = residueDegree K L ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = residueDegree K L := by
  set I := inertiaSubgroup K L
  set F := IntermediateField.fixedField I
  have hn := ramificationIndex_mul_residueDegree K L
  have hf := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hFL : Module.finrank F L = Nat.card I := IntermediateField.finrank_fixedField_eq_card I
  have hG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hIdx : Nat.card I * I.index = Nat.card (L ≃ₐ[K] L) := Subgroup.card_mul_index I
  have hind : I.index = Nat.card (residueAlgEquiv K L).range := Subgroup.index_ker _
  have hrange : Nat.card (residueAlgEquiv K L).range ≤ residueDegree K L := by
    calc Nat.card (residueAlgEquiv K L).range ≤ Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
          Subgroup.card_le_card_group _
      _ = Module.finrank 𝓀[K] 𝓀[L] := IsGalois.card_aut_eq_finrank _ _
      _ = residueDegree K L := (residueDegree_eq_finrank K L).symm
  have hFK : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank K F L
  have hTF : residueDegree K L ≤ Module.finrank K F := by
    rw [← finrank_maximalUnramified K L]
    exact IntermediateField.finrank_le_of_le_right (maximalUnramified_le_fixedField K L)
  set a := Nat.card I
  set r := Nat.card (residueAlgEquiv K L).range
  set e := ramificationIndex K L
  set f := residueDegree K L
  set d := Module.finrank K F
  rw [hind, hG, ← hn] at hIdx
  rw [hFL, ← hn] at hFK
  have h1 : a ≤ e := by
    refine Nat.le_of_mul_le_mul_left ?_ hf
    calc f * a ≤ d * a := Nat.mul_le_mul_right _ hTF
      _ = e * f := hFK
      _ = f * e := mul_comm _ _
  have h2 : e ≤ a := by
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc e * f = a * r := hIdx.symm
      _ ≤ a * f := Nat.mul_le_mul_left _ hrange
  have hae : a = e := le_antisymm h1 h2
  refine ⟨hae, ?_, ?_⟩
  · rw [hae] at hIdx
    exact (Nat.eq_of_mul_eq_mul_left he hIdx)
  · rw [hae, mul_comm e f] at hFK
    exact Nat.eq_of_mul_eq_mul_right he hFK
end GroundTheory.LocalField
