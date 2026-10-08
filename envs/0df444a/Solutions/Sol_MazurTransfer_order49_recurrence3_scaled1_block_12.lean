-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:42:16.63044+00:00
-- url     : https://prove2.me/submissions/526e3c2e-51dc-44af-abbe-fe73d7f18fa2

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled1_block12_half0
import Theorems.Thm_MazurTransfer_order49_recurrence3_scaled1_block12_half1
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 384).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 384).take 32 := by
  change (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 384).take (16 + 16) = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 384).take (16 + 16)
  rw [List.take_add, List.take_add]
  apply congrArg₂ List.append
  · exact MazurTransfer.order49_recurrence3_scaled1_block12_half0
  · simpa only [List.drop_drop] using MazurTransfer.order49_recurrence3_scaled1_block12_half1
#print axioms solution
