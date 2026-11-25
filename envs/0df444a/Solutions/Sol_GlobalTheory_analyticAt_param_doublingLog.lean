-- Prove2me | solution 1 for GlobalTheory.analyticAt_param_doublingLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:56.31945+00:00
-- url     : https://prove2.me/submissions/717c6ed4-fe09-45c1-878d-7279d9efd9ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_tendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_sub_sub_fderiv_le_of_ball
import Theorems.Thm_GlobalTheory_dist_doublingLog_le_of_contraction
import Theorems.Thm_GlobalTheory_hasFDerivAt_of_isBigO_sq
import Theorems.Thm_GlobalTheory_iterate_mem_ball_of_contraction
import Theorems.Thm_GlobalTheory_map_zero_of_isBigO_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Asymptotics
open scoped Topology
variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution {ε : B × V → V} {b₀ : B} (ha : AnalyticAt ℂ ε (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, (fun x => ε (b, x) - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) (b₀, 0) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set K : ℝ := ‖ε (b₀, 0)‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp
    (ha.eventually_analyticAt.and ((ha.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one _))).and ((continuous_fst.tendsto' (b₀, (0 : V)) b₀ rfl).eventually h)))
  rw [← ball_prod_same] at hsa
  set C : ℝ := 4 * K / s ^ 2 with hCdef
  have hC0 : 0 < C := by positivity
  have hCs : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) s, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 := by
    intro b hb x hx
    have hO := (hsa (b, 0) ⟨hb, mem_ball_self hs⟩).2.2
    have hd : DifferentiableOn ℂ (fun x => ε (b, x)) (ball 0 s) := fun y hy =>
      (DifferentiableAt.comp (f := fun x : V => (b, x)) y (hsa (b, y) ⟨hb, hy⟩).1.differentiableAt
        (by fun_prop)).differentiableWithinAt
    have h1 := SCV.norm_sub_sub_fderiv_le_of_ball hd
      (fun y hy => (hsa (b, y) ⟨hb, hy⟩).2.1.le) hx
    have h2 : ε (b, 0) = 0 := map_zero_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO
    have h3 := (hasFDerivAt_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO).fderiv
    rw [h3, h2, sub_zero, sub_zero] at h1
    refine le_of_le_of_eq h1 ?_
    rw [hCdef, div_pow]
    ring
  set r : ℝ := min s (1 / (8 * C)) with hr
  have hr0 : 0 < r := lt_min hs (by positivity)
  have hrs : r ≤ s := min_le_left _ _
  have hC : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 :=
    fun b hb x hx => hCs b hb x (ball_subset_ball hrs hx)
  have hc : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x)‖ ≤ 5 / 8 * ‖x‖ := by
    intro b hb x hx
    have h1 := hC b hb x hx
    have h2 : ‖x‖ ≤ 1 / (8 * C) := (mem_ball_zero_iff.mp hx).le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    have h3 : ‖(2 : ℂ)⁻¹ • x‖ = 1 / 2 * ‖x‖ := by simp [norm_smul]
    have h4 := norm_le_norm_sub_add (ε (b, x)) ((2 : ℂ)⁻¹ • x)
    nlinarith [norm_nonneg x]
  have hd : ∀ j : ℕ, DifferentiableOn ℂ (fun q : B × V => (fun x => ε (q.1, x))^[j] q.2)
      (ball b₀ s ×ˢ ball 0 r) := by
    intro j
    induction j with
    | zero => exact differentiableOn_snd
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      intro q hq
      exact DifferentiableAt.comp_differentiableWithinAt
        (f := fun q : B × V => (q.1, (fun x => ε (q.1, x))^[j] q.2)) q
        (hsa (q.1, (fun x => ε (q.1, x))^[j] q.2) ⟨hq.1, ball_subset_ball hrs
          (iterate_mem_ball_of_contraction (hc q.1 hq.1) hq.2 j)⟩).1.differentiableAt
        (differentiableWithinAt_fst.prodMk (ih q hq))
  have hu : TendstoUniformlyOn
      (fun (j : ℕ) (q : B × V) => (2 : ℂ) ^ j • (fun x => ε (q.1, x))^[j] q.2)
      (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) atTop (ball b₀ s ×ˢ ball 0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have h0 : Tendsto (fun j : ℕ => 64 / 7 * C * r ^ 2 * (25 / 32 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (64 / 7 * C * r ^ 2)
    filter_upwards [h0.eventually (gt_mem_nhds hη)] with j hj q hq
    rw [dist_comm]
    refine ((dist_doublingLog_le_of_contraction (hc q.1 hq.1) hC0.le (hC q.1 hq.1) hq.2 j).trans
      ?_).trans_lt hj
    have := (mem_ball_zero_iff.mp hq.2).le
    gcongr
  exact SCV.analyticAt_of_differentiableOn
    (SCV.differentiableOn_of_tendstoLocallyUniformlyOn (isOpen_ball.prod isOpen_ball)
      hu.tendstoLocallyUniformlyOn (Eventually.of_forall fun j => (hd j).const_smul _))
    (prod_mem_nhds (ball_mem_nhds b₀ hs) (ball_mem_nhds 0 hr0))
end GlobalTheory
