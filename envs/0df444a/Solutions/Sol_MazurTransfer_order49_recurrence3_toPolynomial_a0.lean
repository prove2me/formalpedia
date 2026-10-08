-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_toPolynomial_a0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:25:34.842438+00:00
-- url     : https://prove2.me/submissions/9e3e80f4-e9a2-4953-b2d1-57ef72b16ecc

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range9
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range8
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range7
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range6
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range5
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range4
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range3
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range2
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range1
import Theorems.Thm_MazurTransfer_order49_recurrence3_a0_range0
import Theorems.Thm_MazurTransfer_order49_recurrence3_recurrence2B0_natDegree_le

namespace MazurTransfer.Order49Recurrence3Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/




section

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate
namespace IntegerDenseCertificate

noncomputable section













/-- Coefficient lookup commutes with dense-list interpretation. -/
theorem coeff_toPolynomial (xs : List ℤ) (n : ℕ) :
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial xs).coeff n = (xs.getD n 0 : ℤ) := by
  induction xs generalizing n with
  | nil => simp [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial]
  | cons x xs ih =>
      cases n with
      | zero => simp [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial]
      | succ n =>
          rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, Polynomial.coeff_add,
            Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, ih]
          simp





















private theorem a0_prefix9_length :
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk0 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk1
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk2 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk3
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk4 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk5
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk6 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk7
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk8 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0Chunk9).length = 155 := by
  rfl

private theorem a0_length : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0.length = 155 := by
  unfold MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0
  exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0_prefix9_length





















private theorem a0_coeff (n : ℕ) (h : n < 155) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0.coeff n := by
  by_cases h0 : n < 16
  · exact MazurTransfer.order49_recurrence3_a0_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact MazurTransfer.order49_recurrence3_a0_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact MazurTransfer.order49_recurrence3_a0_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact MazurTransfer.order49_recurrence3_a0_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact MazurTransfer.order49_recurrence3_a0_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact MazurTransfer.order49_recurrence3_a0_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact MazurTransfer.order49_recurrence3_a0_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact MazurTransfer.order49_recurrence3_a0_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact MazurTransfer.order49_recurrence3_a0_range8 n (by omega) h8
  exact MazurTransfer.order49_recurrence3_a0_range9 n (by omega) (by omega)

/-- The dense table for the first third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 := by
  ext n
  rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.coeff_toPolynomial]
  unfold MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0
  by_cases hn : n < 155
  · exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0_coeff n hn
  · rw [List.getD_eq_default (l := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a0) (d := (0 : ℤ)) (by
      rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp MazurTransfer.order49_recurrence3_recurrence2B0_natDegree_le)
      n (by omega)).symm

















































































































































































































































































































































































































































































































































































































































































































































end
end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

theorem solution : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 := by
  exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial_a0
#print axioms solution
