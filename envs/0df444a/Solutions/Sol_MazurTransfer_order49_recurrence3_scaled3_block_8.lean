-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:06:36.004992+00:00
-- url     : https://prove2.me/submissions/4377e840-7e20-4c75-a16d-08d928b82f99

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 256).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 256).take 32 := by decide +kernel
#print axioms solution
