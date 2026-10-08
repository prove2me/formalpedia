-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence3_integer_scaled_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:57:56.315223+00:00
-- url     : https://prove2.me/submissions/c17507f7-4574-459a-bbf1-b5705c53c0c6

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Int.Basic

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






































































/-- The cleared constant scalar residual vanishes. -/
theorem scalar0_scaled_checked : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar0ScaledLeft = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar0ScaledRight :=
  MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.eq_of_chunkedEq (chunk := 32) (fuel := 16) (by decide +kernel)







end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

theorem solution : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar0ScaledLeft = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar0ScaledRight := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar0_scaled_checked
#print axioms solution
