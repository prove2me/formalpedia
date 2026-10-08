-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:51:15.129451+00:00
-- url     : https://prove2.me/submissions/9436513c-6eee-4d7d-894d-0ec95b8b28be

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 64).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 64).take 32 := by decide +kernel
#print axioms solution
