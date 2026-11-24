-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.trAlg_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:22.348128+00:00
-- url     : https://prove2.me/submissions/653ac456-4b9a-4f82-bf50-59f470e96119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_Mem_Capelli_trace_pow_mem
import Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_le
import Theorems.Thm_GlobalTheory_Mem_Capelli_trace_rec

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
variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)
include hdd hdx
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution : trAlg (X * D) = trAlg (D * X) := by
  apply le_antisymm
  · have key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X) := fun p => by
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        cases p with
        | zero => simpa using natCast_mem (trAlg (D * X)) n
        | succ p =>
          have h := trace_rec X D hdd hdx p
          rw [add_assoc, ← sub_eq_iff_eq_add] at h
          rw [← h]
          refine sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega)))
            (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))
          have := Finset.mem_range.1 hr
          omega
    exact trAlg_le fun k => key _
  · refine trAlg_le fun p => ?_
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rw [trace_rec X D hdd hdx p]
      refine add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _)))
        (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))
      have := Finset.mem_range.1 hr
      omega
end GlobalTheory.Mem.Capelli
