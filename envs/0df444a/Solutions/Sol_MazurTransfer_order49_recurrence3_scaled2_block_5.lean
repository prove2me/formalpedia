-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:55:54.26676+00:00
-- url     : https://prove2.me/submissions/b6d77c7e-be1c-4db3-ae0c-454f333f90ff

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 160).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 160).take 32 := by decide +kernel
#print axioms solution
