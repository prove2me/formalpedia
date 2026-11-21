-- Prove2me | solution 1 for MasulloGRH.mellin_gamma_progression_tail_and_real_logarithmic_residue
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:46:16.347505+00:00
-- url     : https://prove2.me/submissions/d3835b33-c30b-4e6a-be86-ff9da1f75e22

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

private theorem mellin_support_upper (f : ℝ → ℂ) {A b : ℝ} (hA : 1 < A)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hsupp : ∀ᵐ x ∂volume.restrict (Ioi 0), x < A → f x = 0)
    (hint : IntegrableOn (fun x : ℝ => x^(b-1) * ‖f x‖) (Ioi 0))
    (s : ℂ) (hs : s.re ≤ b) :
    MellinConvergent f s ∧ ‖mellin f s‖ ≤ A^(s.re-b) *
      (∫ x : ℝ in Ioi 0, x^(b-1) * ‖f x‖) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F := fun x : ℝ => (x : ℂ) ^ (s - 1) • f x
  have h0 : ∀ᵐ x ∂μ, 0 < x := ae_restrict_mem measurableSet_Ioi
  have hF : AEStronglyMeasurable F μ := by
    have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s-1)) (Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).smul hm
  have bound : ∀ᵐ x ∂μ, ‖F x‖ ≤ A^(s.re-b) * (x^(b-1) * ‖f x‖) := by
    filter_upwards [h0,hsupp] with x hx ht
    rw [show ‖F x‖ = x^(s.re-1) * ‖f x‖ by
      simp only [F, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]]
    by_cases hAx : A ≤ x
    · have hr := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hA) hAx (sub_nonpos.mpr hs)
      have he := Real.rpow_add hx (s.re-b) (b-1)
      rw [show s.re - 1 = (s.re-b)+(b-1) by ring, he, mul_assoc]
      exact mul_le_mul_of_nonneg_right hr (mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _))
    · simp [ht (lt_of_not_ge hAx)]
  have hi : Integrable (fun x : ℝ => A^(s.re-b) * (x^(b-1) * ‖f x‖)) μ :=
    hint.const_mul _
  have hFi : Integrable F μ := hi.mono' hF bound
  refine ⟨hFi, ?_⟩
  calc
    ‖mellin f s‖ ≤ ∫ x, ‖F x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, A^(s.re-b)*(x^(b-1)*‖f x‖) ∂μ := integral_mono_ae hFi.norm hi bound
    _ = _ := integral_const_mul _ _


private theorem mellin_support_continuous_zero (f : ℝ → ℂ) {A b : ℝ} (hA : 1 < A) (hb : 0 < b)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hsupp : ∀ᵐ x ∂volume.restrict (Ioi 0), x < A → f x = 0)
    (hint : IntegrableOn (fun x : ℝ => x^(b-1) * ‖f x‖) (Ioi 0)) :
    ContinuousAt (mellin f) 0 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have h0 : ∀ᵐ x ∂μ, 0 < x := ae_restrict_mem measurableSet_Ioi
  apply continuousAt_of_dominated (F := fun (s : ℂ) (x : ℝ) => (x : ℂ) ^ (s-1) • f x)
      (μ := μ) (bound := fun x : ℝ => x^(b-1)*‖f x‖) _ _ hint
  · filter_upwards [h0] with x hx
    have H : ContinuousAt (fun s : ℂ => (x : ℂ)^(s-1)) 0 :=
      (continuousAt_id.sub continuousAt_const).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    simpa only [smul_eq_mul] using H.mul_const (f x)
  · apply Eventually.of_forall
    intro s
    have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s-1)) (Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).smul hm
  · have hr : ∀ᶠ s in 𝓝 (0:ℂ), s.re < b :=
      Complex.continuous_re.continuousAt.tendsto.eventually_lt_const (by simpa using hb)
    filter_upwards [hr] with s hs
    filter_upwards [h0,hsupp] with x hx hsx
    simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
    by_cases hAx : A ≤ x
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (hA.le.trans hAx) (by linarith)) (norm_nonneg _)
    · simp [hsx (lt_of_not_ge hAx)]

open Complex

private theorem gamma_residue (Φ : ℂ → ℂ) (hΦ : ContinuousAt Φ 0) :
    Tendsto (fun z : ℂ => z * (Φ z * logDeriv Complex.Gammaℝ z))
      (𝓝[≠] 0) (𝓝 (-Φ 0)) := by
  let g : ℂ → ℂ := fun z => (Gammaℝ z)⁻¹
  have hg : Differentiable ℂ g := differentiable_Gammaℝ_inv
  have h0 : g 0 = 0 := by simp [g, Gammaℝ_def]
  have hd : HasDerivAt g (2:ℂ)⁻¹ 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have h := Gammaℝ_residue_zero.inv₀ (by norm_num : (2:ℂ) ≠ 0)
    simpa only [slope_fun_def_field, h0, sub_zero, g, div_eq_mul_inv, mul_inv, mul_comm] using h
  have H := (hg.analyticAt 0).tendsto_mul_logDeriv_simple_zero h0
    (by rw [hd.deriv]; exact inv_ne_zero (by norm_num))
  have hchange (s : ℂ) : logDeriv Gammaℝ s = -logDeriv g s := by
    by_cases hs : g s = 0
    · have hG : Gammaℝ s = 0 := by simpa [g] using hs
      simp [logDeriv_apply,hs,hG]
    · have hfun : Gammaℝ = fun z => (g z)⁻¹ := by ext z; simp [g]
      rw [hfun, logDeriv_apply]
      change deriv (g⁻¹) s / (g s)⁻¹ = -logDeriv g s
      rw [((hg s).hasDerivAt.inv hs).deriv, logDeriv_apply]
      field_simp
  have h := (hΦ.tendsto.mono_left nhdsWithin_le_nhds).mul H.neg
  simpa only [sub_zero, mul_neg, mul_one, hchange, mul_assoc, mul_left_comm, mul_comm] using h


theorem solution (f : ℝ → ℂ) (A b : ℝ) (hA : 1 < A)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hsupp : ∀ᵐ x ∂volume.restrict (Ioi 0), x < A → f x = 0)
    (hint : IntegrableOn (fun x : ℝ => x^(b-1) * ‖f x‖) (Ioi 0)) :
    let M := ∫ x : ℝ in Ioi 0, x^(b-1) * ‖f x‖
    (0 < b → Tendsto (fun z : ℂ => z * (mellin f z * logDeriv Complex.Gammaℝ z))
      (𝓝[≠] 0) (𝓝 (-mellin f 0))) ∧
    (∀ s : ℂ, s.re ≤ b → MellinConvergent f s ∧ ‖mellin f s‖ ≤ A^(s.re-b) * M) ∧
      ∀ (d : ℝ), 0 < d → ∀ z : ℕ → ℂ, (∀ n : ℕ, (z n).re ≤ b-d*n) →
        Summable (fun n => ‖mellin f (z n)‖) ∧
          ∀ N : ℕ, (∑' n : ℕ, ‖mellin f (z (N+n))‖) ≤
            M * (A^(-d))^N / (1-A^(-d)) := by
  intro M
  have hpoint := mellin_support_upper f hA hm hsupp hint
  refine ⟨fun hb => gamma_residue _ (mellin_support_continuous_zero f hA hb hm hsupp hint), hpoint, ?_⟩
  intro d hd z hz
  let q := A^(-d)
  have hq : 0 < q := Real.rpow_pos_of_pos (zero_lt_one.trans hA) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hA (neg_lt_zero.mpr hd)
  have hM : 0 ≤ M := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (norm_nonneg _))
  have hbound (n : ℕ) : ‖mellin f (z n)‖ ≤ M * q^n := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hp := hpoint (z n) (by linarith [hz n, mul_nonneg hd.le hn])
    have hqpow : q^n = A^((-d)*(n:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hA).le]
    rw [hqpow, mul_comm M]
    exact hp.2.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hA.le (by linarith [hz n])) hM)
  have geom := hasSum_geometric_of_lt_one hq.le hq1
  have H (N n : ℕ) : ‖mellin f (z (N+n))‖ ≤ (M*q^N)*q^n := by
    simpa only [pow_add, mul_assoc] using hbound (N+n)
  have summ (N : ℕ) := ((geom.mul_left (M*q^N)).summable).of_nonneg_of_le
    (fun n => norm_nonneg _) (H N)
  refine ⟨by simpa using summ 0, ?_⟩
  intro N
  have hh := (summ N).tsum_le_tsum (H N) (geom.mul_left (M*q^N)).summable
  rwa [(geom.mul_left (M*q^N)).tsum_eq] at hh
