-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_threshold_grid_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:21:27.393808+00:00
-- url     : https://prove2.me/submissions/d3f96fd1-6c40-4d7f-a865-802ef32d1aa3

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_threshold_single_cell_error
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_crossing_card
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (b t T : NNReal) (ht : t ≤ T) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hX : ∀ s ≤ T, |X s| ≤ R)
    (hp : ∀ k < n, b ≤ t → u k < b → b < u (k+1) → |X (min t (u (k+1)))-X b| ≤ δ) :
    let Q : NNReal → ℝ := fun r => ∑ k ∈ Finset.range n,
      (X (min r (u (k+1)))-X (min r (u k)))^2/2
    |Q t-Q (min t b) - ∑ k ∈ Finset.range n,
      (if b ≤ u k then (1:ℝ) else 0)*(X (min t (u (k+1)))-X (min t (u k)))^2/2| ≤ 2*R*δ := by
  intro Q
  classical
  dsimp [Q]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb : (∑ k ∈ Finset.range n, |(X (min t (u (k+1)))-X (min t (u k)))^2/2 -
      (X (min (min t b) (u (k+1)))-X (min (min t b) (u k)))^2/2 -
      (if b ≤ u k then (1:ℝ) else 0)*(X (min t (u (k+1)))-X (min t (u k)))^2/2|) ≤
      ∑ k ∈ Finset.range n, if u k < b ∧ b < u (k+1) then 2*R*δ else 0 :=
    Finset.sum_le_sum fun k hk => ito43_threshold_single_cell_error X (u k) (u (k+1)) b t T
      (hu (Nat.le_succ k)) ht R δ hR hδ hX (hp k (Finset.mem_range.mp hk))
  refine hb.trans ?_
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hc := ito43_stopped_grid_crossing_card u hu n b
  have hc' : (((Finset.range n).filter (fun k => u k < b ∧ b < u (k+1))).card:ℝ) ≤ 1 := by exact_mod_cast hc
  simpa using mul_le_mul_of_nonneg_right hc' (show 0 ≤ 2*R*δ by positivity)
