-- Prove2me | solution 1 for GlobalTheory.MonoEigen.exists_back
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:33.79438+00:00
-- url     : https://prove2.me/submissions/df1869e3-89c1-41fb-8e0b-f3fe180c4fad

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
theorem _root_.solution (m : ℕ) (j : Fin n) : ∃ m' : ℕ, (σ ^ m') ((σ ^ m) j) = j := by
  have h : σ.SameCycle ((σ ^ m) j) j := by
    rw [Equiv.Perm.sameCycle_pow_left]
  exact h.exists_nat_pow_eq
end GlobalTheory.MonoEigen
