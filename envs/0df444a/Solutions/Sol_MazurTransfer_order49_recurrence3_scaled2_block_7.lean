-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:59:29.77599+00:00
-- url     : https://prove2.me/submissions/327ceaf0-54e6-40e9-bc6a-f95cc1626fb2

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 224).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 224).take 32 := by decide +kernel
#print axioms solution
