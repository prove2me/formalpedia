-- Prove2me | solution 1 for GlobalTheory.fderiv_integral_mul_kernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:02.864274+00:00
-- url     : https://prove2.me/submissions/698e3a63-38d3-4a39-aeb4-7597efeb60f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
      [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U →
      ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U →
      ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V,
      fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v =
        ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  intro V _ _ _ _ _ ν _ U hU α hα hαc hαU K hK x hx v
  have hUU : IsOpen (U ×ˢ U) := hU.prod hU
  have hα0 : ∀ y, y ∉ U → α y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hαU h))

  have hKd : ∀ p ∈ U ×ˢ U, HasFDerivAt K (fderiv ℝ K p) p := fun p hp =>
    ((hK.differentiableOn (by simp)) p hp).differentiableAt
      (hUU.mem_nhds hp) |>.hasFDerivAt
  have hKp : ∀ x' ∈ U, ∀ y ∈ U,
      HasFDerivAt (fun x'' => K (x'', y)) ((fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)) x' :=
    fun x' hx' y hy => (hKd (x', y) ⟨hx', hy⟩).comp x' (hasFDerivAt_prodMk_left x' y)
  have hcf : ContinuousOn (fderiv ℝ K) (U ×ˢ U) :=
    hK.continuousOn_fderiv_of_isOpen hUU (by exact_mod_cast le_top)
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU x hx
  set r := ε / 2 with hr
  have rpos : 0 < r := half_pos εpos
  have hcb : closedBall x r ⊆ U := (closedBall_subset_ball (half_lt_self εpos)).trans hε
  have hcomp : IsCompact (closedBall x r ×ˢ tsupport α) :=
    (isCompact_closedBall x r).prod hαc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hcf.mono (Set.prod_mono hcb hαU))
  set F' : V → V → V →L[ℝ] ℂ :=
    fun x' y => α y • (fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V) with hF'
  have hcontF : ∀ x' ∈ U, Continuous (fun y => α y * K (x', y)) := by
    intro x' hx'
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_mul_subset_left).trans hαU)
    refine hα.continuousOn.mul ?_
    exact hK.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      (fun y hy => ⟨hx', hy⟩)
  have hcontF' : Continuous (F' x) := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_smul_subset_left _ _).trans hαU)
    refine hα.continuousOn.smul ?_
    have h1 : ContinuousOn (fun y => fderiv ℝ K (x, y)) U :=
      hcf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ⟨hx, hy⟩)
    exact h1.clm_comp continuousOn_const
  have hbound : ∀ y, ∀ x' ∈ ball x r, ‖F' x' y‖ ≤ ‖α y‖ * C := by
    intro y x' hx'
    by_cases hy : y ∈ tsupport α
    · rw [hF', norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖(fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)‖
          ≤ ‖fderiv ℝ K (x', y)‖ * ‖ContinuousLinearMap.inl ℝ V V‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ K (x', y)‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ V V) (norm_nonneg _)
        _ ≤ C := by rw [mul_one]; exact hC _ ⟨ball_subset_closedBall hx', hy⟩
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hF', this]
  have hαi : Integrable α ν := hα.integrable_of_hasCompactSupport hαc
  have hF'i : Integrable (F' x) ν :=
    Integrable.mono' (hαi.norm.mul_const C) hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y x (mem_ball_self rpos))
  have hmain : HasFDerivAt (fun x' => ∫ y, α y * K (x', y) ∂ν) (∫ y, F' x y ∂ν) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x r) (bound := fun y => ‖α y‖ * C)
      (ball_mem_nhds x rpos) ?_ ?_ hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y) (hαi.norm.mul_const C) ?_
    · filter_upwards [hU.mem_nhds hx] with x' hx'
      exact (hcontF x' hx').aestronglyMeasurable
    · exact (hcontF x hx).integrable_of_hasCompactSupport (hαc.mul_right)
    · refine Eventually.of_forall fun y x' hx' => ?_
      by_cases hy : y ∈ U
      · exact (hKp x' (hcb (ball_subset_closedBall hx')) y hy).const_mul (α y)
      · have : α y = 0 := hα0 y hy
        simp only [hF', this, zero_mul, zero_smul]
        exact hasFDerivAt_const _ _
  rw [hmain.fderiv, ContinuousLinearMap.integral_apply hF'i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ U
  · simp only [hF', ContinuousLinearMap.smul_apply, smul_eq_mul, (hKp x hx y hy).fderiv]
  · simp [hF', hα0 y hy]
end GlobalTheory
