-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:33:42.942975+00:00
-- url     : https://prove2.me/submissions/e1ae6753-adf7-46a0-b53c-d8cf77004c58

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 480).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 480).take 32 := by decide +kernel
#print axioms solution
