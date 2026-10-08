-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence3_integer_scaled_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:47:59.397129+00:00
-- url     : https://prove2.me/submissions/484e4f17-8e5d-446e-9d73-51ba92640118

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Int.Basic
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_0
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_1
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_2
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_3
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_4
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_5
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_6
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_7
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_8
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_9
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_10
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_11
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_12
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_13
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_14
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_15
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_tail


namespace MazurTransfer.Order49Recurrence3Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/




section

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate
namespace IntegerDenseCertificate











/-- Compare dense lists in bounded chunks. -/
def chunkedEq (chunk : ℕ) : ℕ → List ℤ → List ℤ → Bool
  | 0, xs, ys => xs.isEmpty && ys.isEmpty
  | fuel + 1, xs, ys =>
      (xs.take chunk == ys.take chunk) &&
        chunkedEq chunk fuel (xs.drop chunk) (ys.drop chunk)

/-- A successful bounded chunk comparison proves ordinary list equality. -/
theorem eq_of_chunkedEq {chunk fuel : ℕ} {xs ys : List ℤ}
    (h : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.chunkedEq chunk fuel xs ys = true) : xs = ys := by
  induction fuel generalizing xs ys with
  | zero =>
      cases xs <;> cases ys <;> simp_all [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.chunkedEq]
  | succ fuel ih =>
      simp only [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.chunkedEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [← List.take_append_drop chunk xs, ← List.take_append_drop chunk ys,
        h.1, ih h.2]












































































/-- The cleared cubic scalar residual vanishes. -/
theorem scalar3_scaled_checked : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight := by
  have h0 := MazurTransfer.order49_recurrence3_scaled3_block_0
  have h1 := MazurTransfer.order49_recurrence3_scaled3_block_1
  have h2 := MazurTransfer.order49_recurrence3_scaled3_block_2
  have h3 := MazurTransfer.order49_recurrence3_scaled3_block_3
  have h4 := MazurTransfer.order49_recurrence3_scaled3_block_4
  have h5 := MazurTransfer.order49_recurrence3_scaled3_block_5
  have h6 := MazurTransfer.order49_recurrence3_scaled3_block_6
  have h7 := MazurTransfer.order49_recurrence3_scaled3_block_7
  have h8 := MazurTransfer.order49_recurrence3_scaled3_block_8
  have h9 := MazurTransfer.order49_recurrence3_scaled3_block_9
  have h10 := MazurTransfer.order49_recurrence3_scaled3_block_10
  have h11 := MazurTransfer.order49_recurrence3_scaled3_block_11
  have h12 := MazurTransfer.order49_recurrence3_scaled3_block_12
  have h13 := MazurTransfer.order49_recurrence3_scaled3_block_13
  have h14 := MazurTransfer.order49_recurrence3_scaled3_block_14
  have h15 := MazurTransfer.order49_recurrence3_scaled3_block_15
  have htail := MazurTransfer.order49_recurrence3_scaled3_tail
  have htail_empty : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 512).isEmpty = true ∧ (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 512).isEmpty = true := by
    rw [htail.1, htail.2]
    exact ⟨rfl, rfl⟩
  apply MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.eq_of_chunkedEq (chunk :=32) (fuel :=16)
  simp only [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.chunkedEq, Bool.and_eq_true, beq_iff_eq, List.drop_drop]
  exact ⟨h0, ⟨h1, ⟨h2, ⟨h3, ⟨h4, ⟨h5, ⟨h6, ⟨h7, ⟨h8, ⟨h9, ⟨h10, ⟨h11, ⟨h12, ⟨h13, ⟨h14, ⟨h15, htail_empty⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

theorem solution : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3_scaled_checked
#print axioms solution
