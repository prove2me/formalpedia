-- Prove2me | solution 1 for GroundTheory.LocalField.eq_of_pow_eq_one_of_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:12.697799+00:00
-- url     : https://prove2.me/submissions/d0a17bf2-af12-494a-aa13-85ded6d8255c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
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



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm
end GroundTheory.LocalField
