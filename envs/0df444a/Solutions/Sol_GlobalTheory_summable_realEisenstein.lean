-- Prove2me | solution 1 for GlobalTheory.summable_realEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:56.795924+00:00
-- url     : https://prove2.me/submissions/88429a36-85b9-4b5b-a913-ee5959e48928

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_eisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory
open KroneckerLimit
namespace GlobalTheory
theorem _root_.solution (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    Summable fun p : {p : ℤ × ℤ // p ≠ 0} => τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s) :=
  (hasSum_eisenstein τ hs).summable
end GlobalTheory
