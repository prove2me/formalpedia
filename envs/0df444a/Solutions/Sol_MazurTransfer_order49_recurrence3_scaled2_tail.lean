-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_tail
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:43:36.646807+00:00
-- url     : https://prove2.me/submissions/fffea89d-0c7b-46c9-8f72-6a4ec374e105

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 512 = [] ∧ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 512 = [] := by decide +kernel
#print axioms solution
