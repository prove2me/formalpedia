-- Prove2me | solution 1 for GlobalTheory.linearIndependent_int_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:07.655442+00:00
-- url     : https://prove2.me/submissions/df863aa5-6631-40d8-9487-ad44162562e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) {ι : Type*} {v : ι → L}
    (hv : LinearIndependent ℝ fun i => (v i : E)) : LinearIndependent ℤ v :=
  LinearIndependent.of_comp L.subtype (hv.restrict_scalars' ℤ)
end GlobalTheory
