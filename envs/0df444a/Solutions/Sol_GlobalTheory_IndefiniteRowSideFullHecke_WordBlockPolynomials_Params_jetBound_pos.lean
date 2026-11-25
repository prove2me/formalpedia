-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params.jetBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:56.978046+00:00
-- url     : https://prove2.me/submissions/952c9c92-4914-4739-bbda-68f30c54c044

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params
variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params
theorem _root_.solution (la : Set.Ioi (0 : ℝ)) : 0 < P.jetBound la := by
  have hf : 1 ≤ f := le_trans (Nat.one_le_pow _ _ P.one_le_m) P.m_pow_le
  have hd : (0 : ℝ) < dStar f P.m := by
    have := P.one_le_m
    exact_mod_cast (show 0 < 2 * f * P.m by positivity)
  unfold Params.jetBound WordBlockPolynomials.jetBound
  positivity
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params
