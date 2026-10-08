-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:55:01.559094+00:00
-- url     : https://prove2.me/submissions/0424dbfc-0844-45ce-bd25-815c4d6e4790

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 256).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 256).take 32 := by decide +kernel
#print axioms solution
