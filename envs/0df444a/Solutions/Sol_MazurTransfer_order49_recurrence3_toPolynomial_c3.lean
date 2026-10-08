-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_toPolynomial_c3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:44:48.25753+00:00
-- url     : https://prove2.me/submissions/3c5c34af-127a-43ef-817d-9b098155b912

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData3
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range10
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range9
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range8
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range7
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range6
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range5
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range4
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range3
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range2
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range1
import Theorems.Thm_MazurTransfer_order49_recurrence3_c3_range0
import Theorems.Thm_MazurTransfer_order49_recurrence3_recurrence4B3_natDegree_le

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











































































































































































































































































































































































































































































































































































































































































































































private theorem c3_prefix10_length :
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk0 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk1
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk2 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk3
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk4 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk5
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk6 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk7
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk8 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk9
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3Chunk10).length = 165 := by
  rfl

private theorem c3_length : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3.length = 165 := by
  unfold MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3
  exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3_prefix10_length























private theorem c3_coeff (n : ℕ) (h : n < 165) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3.coeff n := by
  by_cases h0 : n < 16
  · exact MazurTransfer.order49_recurrence3_c3_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact MazurTransfer.order49_recurrence3_c3_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact MazurTransfer.order49_recurrence3_c3_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact MazurTransfer.order49_recurrence3_c3_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact MazurTransfer.order49_recurrence3_c3_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact MazurTransfer.order49_recurrence3_c3_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact MazurTransfer.order49_recurrence3_c3_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact MazurTransfer.order49_recurrence3_c3_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact MazurTransfer.order49_recurrence3_c3_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact MazurTransfer.order49_recurrence3_c3_range9 n (by omega) h9
  exact MazurTransfer.order49_recurrence3_c3_range10 n (by omega) (by omega)

/-- The dense table for the fourth fifth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_c3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  ext n
  rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.coeff_toPolynomial]
  unfold MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3
  by_cases hn : n < 165
  · exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3_coeff n hn
  · rw [List.getD_eq_default (l := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c3) (d := (0 : ℤ)) (by
      rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp MazurTransfer.order49_recurrence3_recurrence4B3_natDegree_le)
      n (by omega)).symm

























end
end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

theorem solution : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  exact MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial_c3
#print axioms solution
