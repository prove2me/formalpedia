-- Prove2me | solution 2 for MasulloGRH.nuclear_quasinuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:53.593175+00:00
-- url     : https://prove2.me/submissions/85281d64-ffb1-4a92-b3d1-0c04ba0398eb

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_isHLCS_ulift_lp_one
import Theorems.Thm_MasulloGRH_abs_summing_of_l1_tensor_topologies_eq
import Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ :=
  quasinuclear_domination_of_abs_summing E hE.1
    (abs_summing_of_l1_tensor_topologies_eq E hE.1
      (hE.2 (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) isHLCS_ulift_lp_one)) p hp
