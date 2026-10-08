-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:54:19.398642+00:00
-- url     : https://prove2.me/submissions/a49b9797-8bc7-419a-b315-790b33b78564

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 128).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 128).take 32 := by decide +kernel
#print axioms solution
