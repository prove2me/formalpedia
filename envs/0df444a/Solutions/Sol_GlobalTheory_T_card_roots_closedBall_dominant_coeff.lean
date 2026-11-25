-- Prove2me | solution 1 for GlobalTheory.T.card_roots_closedBall_dominant_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:09.911326+00:00
-- url     : https://prove2.me/submissions/d6af5d06-15e7-4421-912d-0b2aac852c25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndexStatement
import Theorems.Thm_GlobalTheory_card_roots_closedBall_eq_dominantIndex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  first | exact @GlobalTheory.card_roots_closedBall_eq_dominantIndex | exact GlobalTheory.card_roots_closedBall_eq_dominantIndex | (intros; apply GlobalTheory.card_roots_closedBall_eq_dominantIndex <;> assumption)
end _root_.GlobalTheory.T
