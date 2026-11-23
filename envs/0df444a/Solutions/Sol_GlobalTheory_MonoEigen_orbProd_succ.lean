-- Prove2me | solution 1 for GlobalTheory.MonoEigen.orbProd_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:33.71081+00:00
-- url     : https://prove2.me/submissions/cef404fc-5a27-4de4-acae-3f08bcafa148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoEigen
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
namespace GlobalTheory.MonoEigen
theorem _root_.solution (m : ℕ) (j : Fin n) :
    orbProd σ a (m + 1) j = orbProd σ a m j * a ((σ ^ m) j) := by
  simp [orbProd, Finset.prod_range_succ]
end GlobalTheory.MonoEigen
