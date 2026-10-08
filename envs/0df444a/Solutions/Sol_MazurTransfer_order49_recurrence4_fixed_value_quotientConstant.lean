-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_fixed_value_quotientConstant
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:51:35.408647+00:00
-- url     : https://prove2.me/submissions/aa5a3d10-cc38-4f7f-a480-6955a733be0a

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart2
theorem solution : MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.quotientConstant := by
  decide +kernel
#print axioms solution
