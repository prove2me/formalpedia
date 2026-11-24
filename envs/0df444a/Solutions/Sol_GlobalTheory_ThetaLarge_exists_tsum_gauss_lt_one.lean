-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.exists_tsum_gauss_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:17.644821+00:00
-- url     : https://prove2.me/submissions/ba597814-6a54-4c23-8868-ee1bcf2b9ff6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {E : Type*} [NormedAddCommGroup E]
namespace GlobalTheory.ThetaLarge
theorem _root_.solution [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [DecidableEq L] :
    ∃ a : ℝ, 0 < a ∧ ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1 := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (a : ℝ) (l : L) => if l = 0 then (0 : ℝ) else Real.exp (-a * ‖(l : E)‖ ^ 2))
    (g := fun _ => 0) (summable_lattice_exp_neg_mul_norm_sq L one_pos) (fun l => ?_) ?_
  · rw [tsum_zero] at h
    obtain ⟨a, h1, h2⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and (h.eventually (gt_mem_nhds one_pos))).exists
    exact ⟨a, h1, h2⟩
  · by_cases hl : l = 0
    · simp [hl]
    · simp only [hl, if_false]
      have hn : 0 < ‖(l : E)‖ ^ 2 := pow_pos (norm_pos_iff.2 (by simpa using hl)) 2
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_mul_const hn)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha l
    split_ifs
    · simpa using (Real.exp_pos _).le
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
      nlinarith [sq_nonneg ‖(l : E)‖]
end GlobalTheory.ThetaLarge
