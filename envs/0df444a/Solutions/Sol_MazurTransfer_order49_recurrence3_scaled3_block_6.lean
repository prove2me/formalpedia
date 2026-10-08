-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:56:51.081227+00:00
-- url     : https://prove2.me/submissions/21462ce9-ccce-42d8-8a52-3b9bdaef283d

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 192).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 192).take 32 := by decide +kernel
#print axioms solution
