-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.trAlg_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:46.680298+00:00
-- url     : https://prove2.me/submissions/ba2e90c4-5a17-4c8d-b12f-d1611d5efd5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_Mem_Capelli_trace_pow_mem
import Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by
  have key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M := by
    intro k
    induction k with
    | zero => intro j; simpa using trace_pow_mem M j
    | succ k ih =>
      intro j
      rw [pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]
      exact add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)
  exact trAlg_le fun k => by simpa using key (k + 1) 0
end GlobalTheory.Mem.Capelli
