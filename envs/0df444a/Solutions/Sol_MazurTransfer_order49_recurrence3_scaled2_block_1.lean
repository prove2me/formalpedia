-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:50:03.116037+00:00
-- url     : https://prove2.me/submissions/21cbe211-8d8e-4c75-ac3d-bbc878b74f8f

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 32).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 32).take 32 := by decide +kernel
#print axioms solution
