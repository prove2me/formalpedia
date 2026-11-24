-- Prove2me | solution 1 for GlobalTheory.DI.Dtot_sub
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T22:51:31.088829+00:00
-- url     : https://prove2.me/submissions/489f3a48-66e3-4829-bfcb-7ca8e9605a94

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem solution (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c - c') = Dtot d c - Dtot d c' := by
  funext s
  simp [Dtot, delta, smul_sub, Finset.sum_sub_distrib, add_sub_add_comm]
