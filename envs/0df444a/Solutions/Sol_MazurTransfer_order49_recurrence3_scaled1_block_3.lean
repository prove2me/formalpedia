-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:34:46.725906+00:00
-- url     : https://prove2.me/submissions/71f460a8-06a9-4d0a-abe6-13cbcddef195

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 96).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 96).take 32 := by decide +kernel
#print axioms solution
