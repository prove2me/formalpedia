-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:30:33.680183+00:00
-- url     : https://prove2.me/submissions/cffc750c-3e4d-4d68-8751-7acc3fcf1465

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 64).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 64).take 32 := by decide +kernel
#print axioms solution
