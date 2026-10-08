-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:55:14.064508+00:00
-- url     : https://prove2.me/submissions/c91fc8d1-1f0f-4013-83a3-dc14a9125e71

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 160).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 160).take 32 := by decide +kernel
#print axioms solution
