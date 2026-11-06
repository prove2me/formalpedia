-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.Qval_eq_max_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:51:43.938526+00:00
-- url     : https://prove2.me/submissions/fb5cbcc6-7bde-40b0-ab84-83e0fd55c5b0

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model
import Theorems.Thm_MinimaxSLP_RhsExtremal_disutility_Qval_eq_max_pairs

open MeasureTheory Matrix

theorem solution {r d n N : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (h : Fin r → ℝ) :
    IsGreatest (Set.range fun i : Fin N => (h - T *ᵥ x) ⬝ᵥ ps i) (MinimaxSLP.RhsSDP.Qval W T q h x) :=
  (MinimaxSLP.RhsExtremal.disutility_Qval_eq_max_pairs (K := 1) W T q (fun _ => 0) (fun _ => 0) ps
    (fun _ => le_refl _) hA2 hA3 hA5 x h).1
