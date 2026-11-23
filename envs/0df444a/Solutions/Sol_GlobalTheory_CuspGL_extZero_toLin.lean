-- Prove2me | solution 1 for GlobalTheory.CuspGL.extZero_toLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.94693+00:00
-- url     : https://prove2.me/submissions/bfcc0454-7b1b-436c-89d4-6218f4869f80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Theorems.Thm_GlobalTheory_CuspGL_extZero_toLin_injective

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
theorem _root_.solution (χ : GL (Fin d) F → ℂ) (x : GL (Fin d) F) :
    extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x := by
  unfold extZero
  have hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact extZero_toLin_injective.eq_iff
  rw [hs, finsum_mem_singleton]
end GlobalTheory.CuspGL
