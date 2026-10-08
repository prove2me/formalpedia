-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block12_half0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:37:44.635752+00:00
-- url     : https://prove2.me/submissions/4a7f0bf5-32b0-4cf7-9a6f-23580311368e

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 384).take 16 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 384).take 16 := by decide +kernel
#print axioms solution
