-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_fixed_value_leadingSquare
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:47:58.30278+00:00
-- url     : https://prove2.me/submissions/3f069ea8-71bf-4d6f-9810-bed15bd243fd

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart0
theorem solution : MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.leadingSquare := by
  decide +kernel
#print axioms solution
