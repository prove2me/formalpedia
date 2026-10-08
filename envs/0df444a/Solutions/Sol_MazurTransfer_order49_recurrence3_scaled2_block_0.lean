-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:48:54.528767+00:00
-- url     : https://prove2.me/submissions/26daace8-64c9-44d7-8135-35fc9936d8e9

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 0).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 0).take 32 := by decide +kernel
#print axioms solution
