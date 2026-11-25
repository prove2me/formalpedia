-- Prove2me | solution 1 for GroundTheory.LocalField.frobenius_apply_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:08:59.969253+00:00
-- url     : https://prove2.me/submissions/8da67aa2-26fb-434b-ade3-6bebfecad9a6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_residue_frobenius_apply
import Theorems.Thm_GroundTheory_LocalField_eq_of_pow_eq_one_of_residue_eq
import Theorems.Thm_GroundTheory_LocalField_mem_integer_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution (h : ramificationIndex K L = 1) {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) {ξ : L} (hξ : ξ ^ m = 1) :
    frobenius K L h ξ = ξ ^ Nat.card 𝓀[K] := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set z : 𝒪[L] := ⟨ξ, mem_integer_of_pow_eq_one hm0 hξ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hξ)
  have key : integerAlgEquiv K L (frobenius K L h) z = z ^ Nat.card 𝓀[K] := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
    · rw [residue_frobenius_apply, map_pow]
  simpa [z] using congrArg Subtype.val key
end GroundTheory.LocalField
