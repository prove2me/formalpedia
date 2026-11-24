-- Prove2me | solution 1 for GlobalTheory.MonoEigen.orbProd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:58:18.850355+00:00
-- url     : https://prove2.me/submissions/c8cf9069-c698-42bb-9264-eba385781adc

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
theorem _root_.solution (d m : ℕ) (j : Fin n) :
    orbProd σ a (d + m) j = orbProd σ a d j * orbProd σ a m ((σ ^ d) j) := by
  unfold orbProd
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]
end GlobalTheory.MonoEigen
