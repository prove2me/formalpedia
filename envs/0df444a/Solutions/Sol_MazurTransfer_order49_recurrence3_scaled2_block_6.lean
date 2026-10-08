-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:57:31.545021+00:00
-- url     : https://prove2.me/submissions/53eb28fc-4c34-4de1-9876-1bc4aa7c0ae0

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 192).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 192).take 32 := by decide +kernel
#print axioms solution
