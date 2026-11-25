-- Prove2me | solution 1 for GlobalTheory.BadShare.rootsAvoid_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:35.810574+00:00
-- url     : https://prove2.me/submissions/a94aecc6-ff64-4301-b199-3d859c7f1d8a

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Theorems.Thm_GlobalTheory_BadShare_root_ne_zero
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {c : (ZMod g)ˣ} {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    _root_.GlobalTheory.BadShare.RootsAvoid g c f ↔ ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)), ∀ a : ℕ,
      x ^ (l ^ a) ≠ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g)) ^ (l ^ a) := by
  have hc : algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) ≠ 0 :=
    (_root_.map_ne_zero _).mpr c.ne_zero
  unfold _root_.GlobalTheory.BadShare.RootsAvoid
  refine forall_congr' fun l => forall_congr' fun hl => forall_congr' fun _ => forall_congr' fun x =>
    forall_congr' fun hx => ?_
  rw [_root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero hl (_root_.GlobalTheory.BadShare.root_ne_zero h0 hx) hc, not_exists]
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
