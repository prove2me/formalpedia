-- Prove2me | solution 1 for GlobalTheory.PolyOfDeriv.foldr_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:14.301793+00:00
-- url     : https://prove2.me/submissions/57d9953c-1127-42d8-badf-9021a495c4f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish
import Theorems.Thm_GlobalTheory_PolyOfDeriv_hasDerivAt_iter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.PolyOfDeriv
theorem _root_.solution {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this
end GlobalTheory.PolyOfDeriv
