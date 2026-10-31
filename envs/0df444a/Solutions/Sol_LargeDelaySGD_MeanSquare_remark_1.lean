-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:51:52.832007+00:00
-- url     : https://prove2.me/submissions/ce08e362-3ab6-43da-be89-af26c27fb300

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

open MeasureTheory ProbabilityTheory LargeDelaySGD.MeanSquare

namespace LDSRemark1

variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

lemma int_norm_le (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (x : EuclideanSpace ℝ (Fin d)) : ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ (1 + B) / 2 := by
  have h2 : Integrable (fun ξ => ‖stochGrad F x ξ‖ ^ 2) μ :=
    (hA1.memLp x).integrable_norm_pow (by norm_num)
  have h1 : Integrable (fun ξ => ‖stochGrad F x ξ‖) μ :=
    ((hA1.memLp x).integrable (by norm_num)).norm
  have hle : ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ ∫ ξ, (1 + ‖stochGrad F x ξ‖ ^ 2) / 2 ∂μ := by
    apply integral_mono h1 ((integrable_const 1).add h2 |>.div_const 2)
    intro ξ
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖stochGrad F x ξ‖ - 1)]
  have heq : ∫ ξ, (1 + ‖stochGrad F x ξ‖ ^ 2) / 2 ∂μ
      = (1 + ∫ ξ, ‖stochGrad F x ξ‖ ^ 2 ∂μ) / 2 := by
    rw [integral_div, integral_add (integrable_const 1) h2]
    simp
  linarith [hA1.second_moment x]

lemma ftc_identity (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (x v : EuclideanSpace ℝ (Fin d)) :
    objective F μ (x + v) - objective F μ x =
      ∫ t in (0:ℝ)..1, inner ℝ (∫ ξ, stochGrad F (x + t • v) ξ ∂μ) v := by
  set H : Ξ × ℝ → ℝ := fun p => inner ℝ (stochGrad F (x + p.2 • v) p.1) v with hH
  have hHm : Measurable H := by
    have h1 : Measurable (fun p : Ξ × ℝ => (x + p.2 • v, p.1)) := by
      apply Measurable.prodMk
      · exact measurable_const.add (measurable_snd.smul_const v)
      · exact measurable_fst
    have h2 := hA1.measurable_grad.comp h1
    exact h2.inner measurable_const
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp)
  have hint_t : ∀ t : ℝ, Integrable (fun ξ => H (ξ, t)) μ := by
    intro t
    have hg : Integrable (stochGrad F (x + t • v)) μ := (hA1.memLp _).integrable (by norm_num)
    have h3 := (innerSL ℝ v).integrable_comp hg
    refine h3.congr (ae_of_all _ (fun ξ => ?_))
    simp [hH, real_inner_comm]
  have hbound : ∀ t : ℝ, ∫ ξ, ‖H (ξ, t)‖ ∂μ ≤ ‖v‖ * ((1 + B) / 2) := by
    intro t
    have hg : Integrable (stochGrad F (x + t • v)) μ := (hA1.memLp _).integrable (by norm_num)
    calc ∫ ξ, ‖H (ξ, t)‖ ∂μ ≤ ∫ ξ, ‖v‖ * ‖stochGrad F (x + t • v) ξ‖ ∂μ := by
          apply integral_mono (hint_t t).norm (hg.norm.const_mul _)
          intro ξ
          simp only [hH]
          rw [mul_comm]
          exact norm_inner_le_norm _ _
      _ = ‖v‖ * ∫ ξ, ‖stochGrad F (x + t • v) ξ‖ ∂μ := integral_const_mul _ _
      _ ≤ ‖v‖ * ((1 + B) / 2) := by
          gcongr
          exact int_norm_le μ F B L hA1 _
  have hHint : Integrable H (μ.prod ν) := by
    rw [integrable_prod_iff' hHm.aestronglyMeasurable]
    refine ⟨ae_of_all _ hint_t, ?_⟩
    refine (integrable_const (‖v‖ * ((1 + B) / 2))).mono' ?_ (ae_of_all _ ?_)
    · exact (hHm.norm.stronglyMeasurable.integral_prod_left' (μ := μ)).aestronglyMeasurable
    · intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hbound t
  have hae := hHint.prod_right_ae
  have hpt : ∀ᵐ ξ ∂μ, F (x + v) ξ - F x ξ = ∫ t, H (ξ, t) ∂ν := by
    filter_upwards [hae, hA1.differentiable] with ξ hξi hξd
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => F (x + t • v) ξ) (H (ξ, t)) t := by
      intro t _
      have hg : HasGradientAt (fun y => F y ξ) (stochGrad F (x + t • v) ξ) (x + t • v) :=
        (hξd (x + t • v)).hasGradientAt
      have hl : HasDerivAt (fun t : ℝ => x + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      have := hg.hasFDerivAt.comp_hasDerivAt t hl
      exact this
    have hII : IntervalIntegrable (fun t => H (ξ, t)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hξi
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII
    rw [intervalIntegral.integral_of_le zero_le_one] at this
    simpa using this.symm
  have hFx : ∀ y, Integrable (F y) μ := hA1.integrable
  calc objective F μ (x + v) - objective F μ x
      = ∫ ξ, (F (x + v) ξ - F x ξ) ∂μ := by
        unfold objective
        rw [integral_sub (hFx _) (hFx _)]
    _ = ∫ ξ, ∫ t, H (ξ, t) ∂ν ∂μ := integral_congr_ae hpt
    _ = ∫ t, ∫ ξ, H (ξ, t) ∂μ ∂ν := integral_integral_swap (f := fun ξ t => H (ξ, t)) hHint
    _ = ∫ t, inner ℝ (∫ ξ, stochGrad F (x + t • v) ξ ∂μ) v ∂ν := by
        congr 1
        funext t
        have hg : Integrable (stochGrad F (x + t • v)) μ := (hA1.memLp _).integrable (by norm_num)
        have := integral_inner (𝕜 := ℝ) hg v
        simp only [hH]
        rw [real_inner_comm, ← this]
        congr 1
        funext ξ
        exact real_inner_comm _ _
    _ = ∫ t in (0:ℝ)..1, inner ℝ (∫ ξ, stochGrad F (x + t • v) ξ ∂μ) v := by
        rw [intervalIntegral.integral_of_le zero_le_one]


lemma remainder_bound (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (x h : EuclideanSpace ℝ (Fin d)) :
    ‖objective F μ (x + h) - objective F μ x - inner ℝ (∫ ξ, stochGrad F x ξ ∂μ) h‖
      ≤ L * ‖h‖ ^ 2 := by
  set G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun y => ∫ ξ, stochGrad F y ξ ∂μ with hG
  have hGL : LipschitzWith L G := hA1.lipschitz
  have hcont : Continuous (fun t : ℝ => inner ℝ (G (x + t • h)) h) := by
    have : Continuous (fun t : ℝ => G (x + t • h)) :=
      hGL.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact this.inner continuous_const
  rw [ftc_identity μ F B L hA1 x h]
  have hconst : inner ℝ (G x) h = ∫ t in (0:ℝ)..1, inner ℝ (G x) h := by simp
  rw [hconst, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
    intervalIntegrable_const]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := L * ‖h‖ ^ 2) (f := fun t => inner ℝ (G (x + t • h)) h - inner ℝ (G x) h) ?_
  · simpa using this
  intro t ht
  simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
  rw [← inner_sub_left]
  calc ‖inner ℝ (G (x + t • h) - G x) h‖ ≤ ‖G (x + t • h) - G x‖ * ‖h‖ := norm_inner_le_norm _ _
    _ ≤ (L * ‖(x + t • h) - x‖) * ‖h‖ := by
        gcongr
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hGL.dist_le_mul _ _
    _ = L * (|t| * ‖h‖) * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    _ ≤ L * (1 * ‖h‖) * ‖h‖ := by
        have : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2
        have hL : (0:ℝ) ≤ L := L.2
        gcongr
    _ = L * ‖h‖ ^ 2 := by ring

end LDSRemark1

open LDSRemark1 in
theorem solution {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L) :
    (∀ x, Integrable (stochGrad F x) μ) ∧
      (∀ x, HasGradientAt (objective F μ) (∫ ξ, stochGrad F x ξ ∂μ) x) ∧
      LipschitzWith L (gradient (objective F μ)) := by
  have hgrad : ∀ x, HasGradientAt (objective F μ) (∫ ξ, stochGrad F x ξ ∂μ) x := by
    intro x
    rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun h => objective F μ (x + h) - objective F μ x -
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (∫ ξ, stochGrad F x ξ ∂μ)) h)
        =O[nhds 0] (fun h : EuclideanSpace ℝ (Fin d) => ‖h‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound (L : ℝ)
      filter_upwards with h
      rw [InnerProductSpace.toDual_apply_apply]
      have := remainder_bound μ F B L hA1 x h
      simpa using this
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  refine ⟨fun x => (hA1.memLp x).integrable (by norm_num), hgrad, ?_⟩
  have : gradient (objective F μ) = fun x => ∫ ξ, stochGrad F x ξ ∂μ :=
    funext (fun x => (hgrad x).gradient)
  rw [this]
  exact hA1.lipschitz
