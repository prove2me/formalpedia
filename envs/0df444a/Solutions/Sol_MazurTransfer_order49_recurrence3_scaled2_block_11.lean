-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:08:49.350982+00:00
-- url     : https://prove2.me/submissions/b06533e7-a4c3-49ab-95aa-62214f5f0ae4

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 352).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 352).take 32 := by decide +kernel
#print axioms solution
