-- Prove2me | solution 2 for GlobalTheory.DI.delta_sub
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T22:51:23.303795+00:00
-- url     : https://prove2.me/submissions/283412da-a8ae-4a0c-ae24-7e8edd751733

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

theorem solution (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by
  funext s
  simp [delta, smul_sub, Finset.sum_sub_distrib]
