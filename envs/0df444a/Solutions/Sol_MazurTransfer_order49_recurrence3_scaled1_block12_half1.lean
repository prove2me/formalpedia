-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block12_half1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:40:30.403794+00:00
-- url     : https://prove2.me/submissions/a8cfec8e-8678-42aa-a93b-e3892890becb

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 400).take 16 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 400).take 16 := by decide +kernel
#print axioms solution
