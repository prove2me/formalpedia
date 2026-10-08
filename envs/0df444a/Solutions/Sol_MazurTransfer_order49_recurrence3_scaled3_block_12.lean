-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:35:29.868917+00:00
-- url     : https://prove2.me/submissions/fa385de5-cad0-47d0-b6cc-d877cf80f887

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 384).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 384).take 32 := by decide +kernel
#print axioms solution
