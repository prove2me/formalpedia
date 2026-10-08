-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:53:38.86198+00:00
-- url     : https://prove2.me/submissions/e0155884-ca08-43e1-97d1-4e2c37bcbebb

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 128).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 128).take 32 := by decide +kernel
#print axioms solution
