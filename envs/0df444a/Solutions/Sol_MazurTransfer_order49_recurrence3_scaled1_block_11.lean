-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:06:20.080556+00:00
-- url     : https://prove2.me/submissions/a9cb226f-555f-43f6-ad42-7c3e743765e2

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 352).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 352).take 32 := by decide +kernel
#print axioms solution
