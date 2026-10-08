-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:03:51.481902+00:00
-- url     : https://prove2.me/submissions/433d5035-0011-4ec4-8e2f-eb5c82b0eb72

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 320).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 320).take 32 := by decide +kernel
#print axioms solution
