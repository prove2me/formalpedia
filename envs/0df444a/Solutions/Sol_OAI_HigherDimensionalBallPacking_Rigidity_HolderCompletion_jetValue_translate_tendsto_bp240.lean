-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:52:57.47034+00:00
-- url     : https://prove2.me/submissions/025717ab-3eeb-480c-b146-115489a87d1a

import Mathlib
import Definitions.Def_OAIQ240Bp012

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_small_third_scale {A : ℝ} (hA : 0 < A) (L : ℝ) :
    ∃ s > 0, L*s^((2:ℝ)/3) < A := by
  have ht : Tendsto (fun s : ℝ => L*s^((2:ℝ)/3)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0:ℝ) ((2:ℝ)/3) (Or.inr (by norm_num))).const_mul L
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, L*s^((2:ℝ)/3) < A := ht.eventually (gt_mem_nhds hA)
  have hh : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ L*s^((2:ℝ)/3) < A := by
    filter_upwards [self_mem_nhdsWithin,he] with s hs h
    exact ⟨hs,h⟩
  exact hh.exists

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCompInst1
local instance holderCompInst2_rbc563b_1 : NormedSpace ℝ (HMap X E) := inferInstance
lemma holder_small_of_small_value {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HMap X E,
      (∀ x, ‖valueCLM _ u x‖ ≤ δ) →
      (∀ x y, ‖valueCLM _ u x-valueCLM _ u y‖ ≤ L*dist x y) → ‖u‖ < ε := by
  obtain ⟨s,hs,hscale⟩ := exists_small_third_scale (half_pos hε) L
  let δ : ℝ := min (ε/2) (ε/4*s^((1:ℝ)/3))
  have hδ : 0 < δ := lt_min (half_pos hε) (by positivity)
  refine ⟨δ,hδ,fun u hb hl => ?_⟩
  have hlarge : 2*δ ≤ ε/2*s^((1:ℝ)/3) := by
    have hh : δ ≤ ε/4*s^((1:ℝ)/3) := min_le_right _ _
    linarith
  have hh := third_interpolation hδ.le hL (half_pos hε).le hs hb hl hscale.le hlarge
  have hn : ‖u‖ ≤ ε/2 := (norm_le_of_bounds u hδ.le (half_pos hε).le hb hh).trans
    (max_le (min_le_left _ _) le_rfl)
  exact hn.trans_lt (half_lt_self hε)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1
local instance transInst2_rbc563b_1 : NormedSpace ℝ (HMap D E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst3
local instance transInst4_rbc563b_1 : NormedSpace ℝ (COne D E) := inferInstance
lemma cValue_norm_diff_le (u : COne D E) (x y : D) :
    ‖cValue u x-cValue u y‖ ≤ ‖u‖*dist x y := by
  rw [dist_eq_norm]
  exact norm_sub_le_of_deriv_bound (c_differentiable u)
    (fun z => by rw [c_fderiv]; exact c_deriv_bound u z) x y

lemma translate_value_norm (u : COne D E) (t z : D) :
    ‖valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) z‖ ≤ ‖u‖*‖t‖ := by
  change ‖cValue u (z+t)-cValue u z‖ ≤ _
  simpa only [dist_eq_norm,add_sub_cancel_left] using cValue_norm_diff_le u (z+t) z

lemma translate_value_lipschitz (u : COne D E) (t x y : D) :
    ‖valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) x-
      valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) y‖ ≤ 2*‖u‖*dist x y := by
  change ‖(cValue u (x+t)-cValue u x)-(cValue u (y+t)-cValue u y)‖ ≤ _
  rw [show (cValue u (x+t)-cValue u x)-(cValue u (y+t)-cValue u y) =
    (cValue u (x+t)-cValue u (y+t))-(cValue u x-cValue u y) by abel]
  have h₁ := cValue_norm_diff_le u (x+t) (y+t)
  rw [dist_add_right] at h₁
  exact (norm_sub_le _ _).trans (by linarith [cValue_norm_diff_le u x y])

lemma jetValue_translate_tendsto_bp240_oai (u : COne D E) :
    Tendsto (fun t => holderTranslate t (jetValueCLM _ u)) (𝓝 0) (𝓝 (jetValueCLM _ u)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := D) (E := E)
    (show 0 ≤ 2*‖u‖ by positivity) hε
  have ht : Tendsto (fun t : D => ‖u‖*‖t‖) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun t : D => ‖u‖*‖t‖) := continuous_const.mul continuous_norm
    simpa only [norm_zero,mul_zero] using h.tendsto (0:D)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with t ht
  rw [dist_eq_norm]
  exact hd _ (fun z => (translate_value_norm u t z).trans ht.le) (translate_value_lipschitz u t)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto_bp240_oai.{u_1, u_2}
