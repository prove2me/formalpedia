-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:14:25.630679+00:00
-- url     : https://prove2.me/submissions/67239c0c-37f9-4cb4-aece-f70456f6e8f0

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 352).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 352).take 32 := by decide +kernel
#print axioms solution
