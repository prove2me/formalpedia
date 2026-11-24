-- Prove2me | solution 1 for GlobalTheory.div_mem_of_mul_pow_div_mem_of_regularPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:03.201217+00:00
-- url     : https://prove2.me/submissions/ca4e5b73-b72f-4ab3-9c5b-0ba71c34fe3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivMemOfMulPowDivMemOfRegularPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]
end GlobalTheory
