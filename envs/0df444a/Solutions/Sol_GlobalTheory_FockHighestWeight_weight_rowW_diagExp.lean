-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.weight_rowW_diagExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:37.743746+00:00
-- url     : https://prove2.me/submissions/cb531ca8-3ef0-4f6f-b309-5b05d5235adb

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_diagExp_apply
import Theorems.Thm_GlobalTheory_FockHighestWeight_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution (ν : Fin n → ℕ) :
    Finsupp.weight (rowW r n) (diagExp r ν) = rowNu (r := r) ν := by
  funext a
  rw [weight_rowW]
  simp only [diagExp_apply, rowNu]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    have := s.2
    omega
end GlobalTheory.FockHighestWeight
