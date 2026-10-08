-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:13:51.371115+00:00
-- url     : https://prove2.me/submissions/1c87109c-d2b7-46a8-8b5a-9d71ca550fae

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 384).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 384).take 32 := by decide +kernel
#print axioms solution
