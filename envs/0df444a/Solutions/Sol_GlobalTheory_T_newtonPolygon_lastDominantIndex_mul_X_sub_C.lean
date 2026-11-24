-- Prove2me | solution 1 for GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:33.947502+00:00
-- url     : https://prove2.me/submissions/3a843652-1373-442b-9096-c909f4b82d7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubC
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubCStatement
import Theorems.Thm_GlobalTheory_newton_step_root_in_disc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧ ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  first | exact @GlobalTheory.newton_step_root_in_disc | exact GlobalTheory.newton_step_root_in_disc | (intros; apply GlobalTheory.newton_step_root_in_disc <;> assumption)
end _root_.GlobalTheory.T
