-- Prove2me | solution 1 for GlobalTheory.T.card_roots_closedBall_bounds_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:22.195599+00:00
-- url     : https://prove2.me/submissions/c4145696-c77e-48b9-9d42-3945b724f026

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Theorems.Thm_GlobalTheory_card_roots_le_radius_bounds


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
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  first | exact @GlobalTheory.card_roots_le_radius_bounds | exact GlobalTheory.card_roots_le_radius_bounds | (intros; apply GlobalTheory.card_roots_le_radius_bounds <;> assumption)
end _root_.GlobalTheory.T
