-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:48:54.51698+00:00
-- url     : https://prove2.me/submissions/f86edde8-16e3-44f0-8b99-2508b5b72492

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 0).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 0).take 32 := by decide +kernel
#print axioms solution
