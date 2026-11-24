-- Prove2me | solution 1 for GlobalTheory.multiDiff_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:37.367719+00:00
-- url     : https://prove2.me/submissions/2929be2d-0446-4019-9fa9-baea8313a65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (a : G) (φ : G → M) :
    multiDiff (fun _ : Fin d ↦ a) φ = (bwdDiff a)^[d] φ := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← ih, ← multiDiff_cons]
    congr 1
    ext i; cases i using Fin.cases <;> simp
end GlobalTheory
