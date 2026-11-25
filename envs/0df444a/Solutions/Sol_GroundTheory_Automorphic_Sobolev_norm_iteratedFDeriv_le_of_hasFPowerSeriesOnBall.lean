-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:26.856496+00:00
-- url     : https://prove2.me/submissions/bc0fd923-0335-404a-96d2-67af35e9b1a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {f : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f q y R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f y‖ ≤ k.factorial * ‖q k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Equiv.Perm (Fin k), q k (fun i ↦ v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖q k (fun i ↦ v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖q k‖ * ∏ i, ‖v i‖ := by
        gcongr with σ
        refine ((q k).le_opNorm _).trans (le_of_eq ?_)
        congr 1
        exact Equiv.prod_comp σ (fun i ↦ ‖v i‖)
    _ = k.factorial * ‖q k‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring
end GroundTheory.Automorphic.Sobolev
