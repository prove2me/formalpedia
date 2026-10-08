-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_fixed_value_a4Square
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:49:46.15342+00:00
-- url     : https://prove2.me/submissions/e5e5a105-d44a-4c63-a1a5-ef6a22233039

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart1
theorem solution : MazurTransfer.Order49Recurrence4DenseCandidate.a4Square = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.a4Square := by
  decide +kernel
#print axioms solution
