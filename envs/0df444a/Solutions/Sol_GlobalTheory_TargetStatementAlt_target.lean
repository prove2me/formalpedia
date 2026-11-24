-- Prove2me | solution 1 for GlobalTheory.TargetStatementAlt.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:12.435056+00:00
-- url     : https://prove2.me/submissions/5140d547-021a-421f-a88b-e2f3587e66d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsAlt
import Theorems.Thm_GlobalTheory_TargetStatementAlt_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetStatementAlt
open Polynomial
namespace GlobalTheory.TargetStatementAlt
theorem _root_.solution : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h
end GlobalTheory.TargetStatementAlt
