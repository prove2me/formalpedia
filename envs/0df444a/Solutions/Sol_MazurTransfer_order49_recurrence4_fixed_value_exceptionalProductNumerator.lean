-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_fixed_value_exceptionalProductNumerator
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:54:04.922528+00:00
-- url     : https://prove2.me/submissions/a9bbcf53-2cbe-43a2-a95f-762475170929

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart3
theorem solution : MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.exceptionalProductNumerator := by
  decide +kernel
#print axioms solution
