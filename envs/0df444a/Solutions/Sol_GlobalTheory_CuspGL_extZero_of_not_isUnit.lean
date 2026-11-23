-- Prove2me | solution 1 for GlobalTheory.CuspGL.extZero_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:14.785996+00:00
-- url     : https://prove2.me/submissions/3556895b-a41a-4e17-aaea-805886dffac5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Theorems.Thm_GlobalTheory_CuspGL_extZero_isUnit_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {d : ℕ}
namespace GlobalTheory.CuspGL
theorem _root_.solution (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by
  unfold extZero
  have hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)
  rw [hs, finsum_mem_empty]
end GlobalTheory.CuspGL
