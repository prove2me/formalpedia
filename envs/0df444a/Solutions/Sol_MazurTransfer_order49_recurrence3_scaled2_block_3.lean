-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:52:46.425978+00:00
-- url     : https://prove2.me/submissions/c9a16a06-f213-4737-8edb-66075ef1e2f0

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 96).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 96).take 32 := by decide +kernel
#print axioms solution
