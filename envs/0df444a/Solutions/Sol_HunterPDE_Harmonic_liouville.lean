-- Prove2me | solution 1 for HunterPDE.Harmonic.liouville
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:50:33.848438+00:00
-- url     : https://prove2.me/submissions/83b4929c-aabe-41fd-bbd6-39625e054423

import Mathlib

open MeasureTheory Metric Set Filter
open scoped Topology InnerProductSpace Laplacian Pointwise

/-!
Ball mean value property for `C²` functions harmonic on a ball in a finite-dimensional real inner
product space, proved without a divergence theorem or polar coordinates:
`green` (integration by parts against a compactly supported `C²` function), `kernel_green`
(`∫ ϑ(|z-x|²/t²) ∇w(z)·(z-x) dz = 0`), `Phi_const` (the scaling flow
`t ↦ ∫ w(x+t y) ϑ(|y|²) dy` is constant), and `ball_average_eq`.
-/

namespace HarmAux


/-- Green's identity against a compactly supported `C²` function, in coordinates of an
orthonormal basis. -/
lemma green {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {f Ψ : E → ℝ} (hf : ContDiff ℝ 2 f) (hΨ : ContDiff ℝ 2 Ψ) (hc : HasCompactSupport Ψ) :
    ∫ y, ∑ i, fderiv ℝ f y (b i) * fderiv ℝ Ψ y (b i) =
      - ∫ y, (Δ f) y * Ψ y := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hΨ1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  have hfd : Continuous (fderiv ℝ f) := hf1.continuous
  have hfdd : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv (by norm_num)
  have hΨc : Continuous Ψ := hΨ.continuous
  have hΨd : Continuous (fderiv ℝ Ψ) := hΨ1.continuous
  have hcd : HasCompactSupport (fderiv ℝ Ψ) := hc.fderiv ℝ
  have key : ∀ i, ∫ y, fderiv ℝ f y (b i) * fderiv ℝ Ψ y (b i) =
      - ∫ y, iteratedFDeriv ℝ 2 f y ![b i, b i] * Ψ y := by
    intro i
    set f₁ : E → ℝ := fun y => fderiv ℝ f y (b i) with hf₁
    have hf₁d : ∀ y, HasFDerivAt f₁ ((fderiv ℝ (fderiv ℝ f) y).flip (b i)) y := by
      intro y
      have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
        (hf1.differentiable (by norm_num) y).hasFDerivAt
      have h2 := h1.clm_apply (hasFDerivAt_const (b i) y)
      refine h2.congr_fderiv ?_
      ext v
      simp
    have hder : ∀ y, fderiv ℝ f₁ y (b i) = iteratedFDeriv ℝ 2 f y ![b i, b i] := by
      intro y
      rw [(hf₁d y).fderiv, iteratedFDeriv_two_apply]
      simp
    have hf₁c : Continuous f₁ := hfd.clm_apply continuous_const
    have hf₁dc : Continuous (fun y => fderiv ℝ f₁ y (b i)) := by
      simp_rw [hder, iteratedFDeriv_two_apply]
      simpa using (hfdd.clm_apply continuous_const).clm_apply continuous_const
    have hI1 : Integrable (fun y => fderiv ℝ f₁ y (b i) * Ψ y) volume := by
      apply Continuous.integrable_of_hasCompactSupport (hf₁dc.mul hΨc)
      exact hc.mul_left
    have hI2 : Integrable (fun y => f₁ y * fderiv ℝ Ψ y (b i)) volume := by
      apply Continuous.integrable_of_hasCompactSupport
        (hf₁c.mul (hΨd.clm_apply continuous_const))
      exact (hcd.comp_left (g := fun L : E →L[ℝ] ℝ => L (b i)) (by simp)).mul_left
    have hI3 : Integrable (fun y => f₁ y * Ψ y) volume := by
      apply Continuous.integrable_of_hasCompactSupport (hf₁c.mul hΨc)
      exact hc.mul_left
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := b i)
      (f := f₁) (g := Ψ) hI1 hI2 hI3
      (fun y _ => (hf₁d y).differentiableAt) (fun y _ => (hΨ.differentiable (by norm_num) y))
    simpa [hder] using this
  have hlap := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b
  have hint : ∀ i, Integrable (fun y => fderiv ℝ f y (b i) * fderiv ℝ Ψ y (b i)) volume := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
      ((hfd.clm_apply continuous_const).mul (hΨd.clm_apply continuous_const))
    exact (hcd.comp_left (g := fun L : E →L[ℝ] ℝ => L (b i)) (by simp)).mul_left
  have hint2 : ∀ i, Integrable (fun y => iteratedFDeriv ℝ 2 f y ![b i, b i] * Ψ y) volume := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · simp_rw [iteratedFDeriv_two_apply]
      exact Continuous.mul ((hfdd.clm_apply continuous_const).clm_apply continuous_const) hΨc
    · exact hc.mul_left
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [key]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hint2 i)]
  congr 2
  ext y
  rw [hlap]
  simp [Finset.sum_mul]



/-- The primitive `Ξ s = ∫_s^1 ϑ`. -/
noncomputable def Xi (ϑ : ℝ → ℝ) (s : ℝ) : ℝ := ∫ τ in s..1, ϑ τ

lemma hasDerivAt_Xi {ϑ : ℝ → ℝ} (hϑ : Continuous ϑ) (s : ℝ) : HasDerivAt (Xi ϑ) (-ϑ s) s :=
  intervalIntegral.integral_hasDerivAt_left (hϑ.intervalIntegrable _ _)
    (hϑ.stronglyMeasurableAtFilter _ _) hϑ.continuousAt

lemma contDiff_Xi {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 1 ϑ) : ContDiff ℝ 2 (Xi ϑ) := by
  have hd : ∀ s, HasDerivAt (Xi ϑ) (-ϑ s) s := hasDerivAt_Xi hϑ.continuous
  have hderiv : deriv (Xi ϑ) = fun s => -ϑ s := funext fun s => (hd s).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun s => (hd s).differentiableAt, by simp, ?_⟩
  rw [hderiv]
  exact hϑ.neg

lemma Xi_eq_zero {ϑ : ℝ → ℝ} (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) {s : ℝ} (hs : 1 ≤ s) :
    Xi ϑ s = 0 := by
  unfold Xi
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  have : ∫ τ in (1 : ℝ)..s, ϑ τ = ∫ τ in (1 : ℝ)..s, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le hs] at hτ
    exact h1 τ hτ.1
  rw [this]; simp

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial potential `Ψ_t(z) = -(t²/2) Ξ(|z - x|² / t²)`, with `∇Ψ_t(z) = ϑ(|z-x|²/t²)(z-x)`. -/
noncomputable def Psi (ϑ : ℝ → ℝ) (x : E) (t : ℝ) (z : E) : ℝ :=
  -(t ^ 2 / 2) * Xi ϑ (‖z - x‖ ^ 2 / t ^ 2)

lemma hasFDerivAt_Psi {ϑ : ℝ → ℝ} (hϑ : Continuous ϑ) {t : ℝ} (ht : t ≠ 0) (x z : E) :
    HasFDerivAt (Psi ϑ x t) (ϑ (‖z - x‖ ^ 2 / t ^ 2) • innerSL ℝ (z - x)) z := by
  have hN : HasFDerivAt (fun z : E => ‖z - x‖ ^ 2) (2 • innerSL ℝ (z - x)) z := by
    have h2 := (hasStrictFDerivAt_norm_sq (z - x)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const x)
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hh : HasDerivAt (fun s : ℝ => -(t ^ 2 / 2) * Xi ϑ (s / t ^ 2))
      (ϑ (‖z - x‖ ^ 2 / t ^ 2) / 2) (‖z - x‖ ^ 2) := by
    have h1 := (hasDerivAt_Xi hϑ (‖z - x‖ ^ 2 / t ^ 2)).comp (‖z - x‖ ^ 2)
      ((hasDerivAt_id (‖z - x‖ ^ 2)).div_const (t ^ 2))
    have h2 := h1.const_mul (-(t ^ 2 / 2))
    have e : -(t ^ 2 / 2) * (-ϑ (‖z - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) =
        ϑ (‖z - x‖ ^ 2 / t ^ 2) / 2 := by
      field_simp
    rw [← e]
    exact h2
  have h3 := hh.comp_hasFDerivAt z hN
  have e2 : (ϑ (‖z - x‖ ^ 2 / t ^ 2) / 2) • (2 • innerSL ℝ (z - x)) =
      ϑ (‖z - x‖ ^ 2 / t ^ 2) • innerSL ℝ (z - x) := by
    ext v
    simp
    ring
  rw [← e2]
  exact h3

lemma contDiff_Psi {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 1 ϑ) (t : ℝ) (x : E) :
    ContDiff ℝ 2 (Psi ϑ x t) := by
  unfold Psi
  have h1 : ContDiff ℝ 2 (fun z : E => ‖z - x‖ ^ 2 / t ^ 2) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const (t ^ 2)
  exact contDiff_const.mul ((contDiff_Xi hϑ).comp h1)

lemma Psi_eq_zero {ϑ : ℝ → ℝ} (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) {t : ℝ} (ht : 0 < t) {x z : E}
    (hz : t ≤ ‖z - x‖) : Psi ϑ x t z = 0 := by
  unfold Psi
  have : 1 ≤ ‖z - x‖ ^ 2 / t ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (z - x)]
  rw [Xi_eq_zero h1 this, mul_zero]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma hasCompactSupport_Psi {ϑ : ℝ → ℝ} (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) {t : ℝ} (ht : 0 < t)
    (x : E) : HasCompactSupport (Psi ϑ x t) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x t) ?_
  intro z hz
  by_contra hzb
  rw [mem_closedBall, dist_eq_norm, not_le] at hzb
  exact hz (Psi_eq_zero h1 ht hzb.le)

/-- The key identity: `∫ ϑ(|z-x|²/t²) ∇w(z)·(z - x) dz = 0` for `w` harmonic on the ball `B(x,R)`,
`0 < t < R`. -/
lemma kernel_green {w : E → ℝ} (hw : ContDiff ℝ 2 w) {x : E} {R : ℝ}
    (hΔ : ∀ z ∈ ball x R, (Δ w) z = 0) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 1 ϑ)
    (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) {t : ℝ} (ht : 0 < t) (htR : t < R) :
    ∫ z, ϑ (‖z - x‖ ^ 2 / t ^ 2) * fderiv ℝ w z (z - x) = 0 := by
  let b := stdOrthonormalBasis ℝ E
  have hg := green b hw (contDiff_Psi hϑ t x) (hasCompactSupport_Psi h1 ht x)
  have hR : ∫ z, (Δ w) z * Psi ϑ x t z = 0 := by
    have : ∀ z, (Δ w) z * Psi ϑ x t z = 0 := by
      intro z
      by_cases hz : ‖z - x‖ < t
      · have : z ∈ ball x R := by
          rw [mem_ball, dist_eq_norm]; linarith
        rw [hΔ z this, zero_mul]
      · rw [Psi_eq_zero h1 ht (not_lt.mp hz), mul_zero]
    simp [this]
  rw [hR, neg_zero] at hg
  rw [← hg]
  congr 1
  ext z
  have hd : ∀ v, fderiv ℝ (Psi ϑ x t) z v = ϑ (‖z - x‖ ^ 2 / t ^ 2) * inner ℝ (z - x) v := by
    intro v
    rw [(hasFDerivAt_Psi hϑ.continuous ht.ne' x z).fderiv]
    simp [inner_sub_left]
  simp_rw [hd]
  have hs : ∑ i, inner ℝ (z - x) (b i) • b i = z - x := by
    have := b.sum_repr' (z - x)
    simpa [real_inner_comm] using this
  calc ϑ (‖z - x‖ ^ 2 / t ^ 2) * fderiv ℝ w z (z - x)
      = ϑ (‖z - x‖ ^ 2 / t ^ 2) * fderiv ℝ w z (∑ i, inner ℝ (z - x) (b i) • b i) := by rw [hs]
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring

end



section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Scaling flow for the kernel `ϑ(|y|²)`. -/
noncomputable def Phi (w : E → ℝ) (x : E) (ϑ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y : E, w (x + t • y) * ϑ (‖y‖ ^ 2)

/-- The derivative of the flow vanishes (change of variables `z = x + t y`). -/
lemma integral_dflow_eq_zero {w : E → ℝ} (hw : ContDiff ℝ 2 w) {x : E} {R : ℝ}
    (hΔ : ∀ z ∈ ball x R, (Δ w) z = 0) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 1 ϑ)
    (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) {t : ℝ} (ht : 0 < t) (htR : t < R) :
    ∫ y : E, fderiv ℝ w (x + t • y) y * ϑ (‖y‖ ^ 2) = 0 := by
  have hk := kernel_green hw hΔ hϑ h1 ht htR
  set G : E → ℝ := fun z => ϑ (‖z - x‖ ^ 2 / t ^ 2) * fderiv ℝ w z (z - x) with hG
  have h1' : ∫ z, G z = ∫ y, G (x + y) := (integral_add_left_eq_self (fun z => G z) x).symm
  have hscale := Measure.integral_comp_smul (μ := (volume : Measure E)) (fun y => G (x + y)) t
  have h3 : ∫ y : E, G (x + t • y) = 0 := by
    rw [hscale, ← h1', hk]; simp
  have h4 : ∀ y : E, G (x + t • y) = t * (fderiv ℝ w (x + t • y) y * ϑ (‖y‖ ^ 2)) := by
    intro y
    simp only [hG, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, map_smul, smul_eq_mul]
    have ht0 : t ≠ 0 := ht.ne'
    have : (|t| * ‖y‖) ^ 2 / t ^ 2 = ‖y‖ ^ 2 := by
      rw [mul_pow, sq_abs]; field_simp
    rw [this]; ring
  simp_rw [h4] at h3
  rw [integral_const_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h ht.ne'
  · exact h

lemma continuous_Phi_integrand {w : E → ℝ} (hw : Continuous w) {x : E} {ϑ : ℝ → ℝ}
    (hϑc : Continuous ϑ) (t : ℝ) : Continuous (fun y : E => w (x + t • y) * ϑ (‖y‖ ^ 2)) :=
  (hw.comp (continuous_const.add (continuous_const.smul continuous_id))).mul
    (hϑc.comp (continuous_norm.pow 2))

lemma hasCompactSupport_integrand {f : E → ℝ} {ϑ : ℝ → ℝ} (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) :
    HasCompactSupport (fun y : E => f y * ϑ (‖y‖ ^ 2)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) 1) ?_
  intro y hy
  by_contra hyb
  rw [mem_closedBall, dist_zero_right, not_le] at hyb
  apply hy
  have : 1 ≤ ‖y‖ ^ 2 := by nlinarith
  simp [h1 _ this]

lemma hasDerivAt_Phi {w : E → ℝ} (hw : ContDiff ℝ 1 w) {x : E} {R : ℝ} {ϑ : ℝ → ℝ}
    (hϑc : Continuous ϑ) (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) (hϑ01 : ∀ τ, 0 ≤ ϑ τ ∧ ϑ τ ≤ 1)
    {t : ℝ} (ht : 0 < t) (htR : t < R) :
    HasDerivAt (Phi w x ϑ) (∫ y : E, fderiv ℝ w (x + t • y) y * ϑ (‖y‖ ^ 2)) t := by
  have hwc : Continuous w := hw.continuous
  have hfd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hfd.continuousOn
  set C' : ℝ := max C 0 with hC'
  set ε : ℝ := min t (R - t) with hε
  have hεpos : 0 < ε := lt_min ht (by linarith)
  set bound : E → ℝ := (closedBall (0 : E) 1).indicator (fun _ => C') with hbound
  have hbint : Integrable bound volume :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have hF'c : ∀ s : ℝ, Continuous (fun y : E => fderiv ℝ w (x + s • y) y * ϑ (‖y‖ ^ 2)) := by
    intro s
    refine (Continuous.clm_apply (hfd.comp (continuous_const.add (continuous_const.smul
      continuous_id))) continuous_id).mul (hϑc.comp (continuous_norm.pow 2))
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (F := fun s y => w (x + s • y) * ϑ (‖y‖ ^ 2))
    (F' := fun s y => fderiv ℝ w (x + s • y) y * ϑ (‖y‖ ^ 2)) (x₀ := t) (bound := bound)
    (ball_mem_nhds t hεpos)
    (Eventually.of_forall fun s => (continuous_Phi_integrand hwc hϑc s).aestronglyMeasurable)
    ((continuous_Phi_integrand hwc hϑc t).integrable_of_hasCompactSupport
      (hasCompactSupport_integrand h1))
    (hF'c t).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => ?_) hbint
    (Eventually.of_forall fun y s hs => ?_)
  · exact this.2
  · -- bound
    by_cases hy : ‖y‖ ≤ 1
    · have hs' : |s| ≤ R := by
        rw [mem_ball, Real.dist_eq] at hs
        have := le_trans (abs_le.mp (le_of_lt hs) |>.2) (by linarith [min_le_right t (R - t)] : ε ≤ R - t)
        have h2 := abs_sub_abs_le_abs_sub s t
        have h3 : ε ≤ t := min_le_left _ _
        have h4 : ε ≤ R - t := min_le_right _ _
        rw [abs_of_pos ht] at h2
        linarith
      have hmem : x + s • y ∈ closedBall x R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        calc |s| * ‖y‖ ≤ R * 1 := mul_le_mul hs' hy (norm_nonneg _) (by linarith [abs_nonneg s])
          _ = R := mul_one R
      have hb1 : ‖fderiv ℝ w (x + s • y)‖ ≤ C' := (hC _ hmem).trans (le_max_left _ _)
      have hbd : ‖fderiv ℝ w (x + s • y) y‖ ≤ C' := by
        calc ‖fderiv ℝ w (x + s • y) y‖ ≤ ‖fderiv ℝ w (x + s • y)‖ * ‖y‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ C' * 1 := mul_le_mul hb1 hy (norm_nonneg _) (le_max_right _ _)
          _ = C' := mul_one _
      have hy' : y ∈ closedBall (0 : E) 1 := by simpa using hy
      simp only [hbound, indicator_of_mem hy', Real.norm_eq_abs, abs_mul]
      have := hϑ01 (‖y‖ ^ 2)
      calc |fderiv ℝ w (x + s • y) y| * |ϑ (‖y‖ ^ 2)| ≤ C' * 1 := by
            apply mul_le_mul
            · exact (Real.norm_eq_abs _ ▸ hbd)
            · rw [abs_of_nonneg this.1]; exact this.2
            · exact abs_nonneg _
            · exact le_max_right _ _
        _ = C' := mul_one _
    · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_le.mp hy]
      have hy' : y ∉ closedBall (0 : E) 1 := by simpa using hy
      simp [hbound, indicator_of_notMem hy', h1 _ h2]
  · -- derivative of the integrand
    have h1' : HasDerivAt (fun r : ℝ => x + r • y) y s := by
      simpa using ((hasDerivAt_id s).smul_const y).const_add x
    have h2 : HasDerivAt (fun r : ℝ => w (x + r • y)) (fderiv ℝ w (x + s • y) y) s :=
      ((hw.differentiable (by norm_num) (x + s • y)).hasFDerivAt).comp_hasDerivAt s h1'
    exact h2.mul_const _

lemma tendsto_Phi_zero {w : E → ℝ} (hw : Continuous w) {x : E} {R : ℝ} (hR : 0 < R)
    {ϑ : ℝ → ℝ} (hϑc : Continuous ϑ) (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0)
    (hϑ01 : ∀ τ, 0 ≤ ϑ τ ∧ ϑ τ ≤ 1) :
    Tendsto (Phi w x ϑ) (𝓝[>] 0) (𝓝 (w x * ∫ y : E, ϑ (‖y‖ ^ 2))) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hw.continuousOn
  set M' : ℝ := max M 0 with hM'
  set bound : E → ℝ := (closedBall (0 : E) 1).indicator (fun _ => M') with hbound
  have hbint : Integrable bound volume :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure E))
    (l := 𝓝[>] (0 : ℝ)) (F := fun s y => w (x + s • y) * ϑ (‖y‖ ^ 2))
    (f := fun y => w x * ϑ (‖y‖ ^ 2)) bound
    (Eventually.of_forall fun s => (continuous_Phi_integrand hw hϑc s).aestronglyMeasurable)
    ?_ hbint ?_
  · simp only [integral_const_mul] at this
    exact this
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 R := Ioo_mem_nhdsGT hR
    filter_upwards [hev] with s hs
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ 1
    · have hmem : x + s • y ∈ closedBall x R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs.1]
        calc s * ‖y‖ ≤ R * 1 := mul_le_mul hs.2.le hy (norm_nonneg _) hR.le
          _ = R := mul_one R
      have hb : ‖w (x + s • y)‖ ≤ M' := (hM _ hmem).trans (le_max_left _ _)
      have hy' : y ∈ closedBall (0 : E) 1 := by simpa using hy
      simp only [hbound, indicator_of_mem hy', Real.norm_eq_abs, abs_mul]
      have := hϑ01 (‖y‖ ^ 2)
      calc |w (x + s • y)| * |ϑ (‖y‖ ^ 2)| ≤ M' * 1 := by
            apply mul_le_mul
            · exact (Real.norm_eq_abs _ ▸ hb)
            · rw [abs_of_nonneg this.1]; exact this.2
            · exact abs_nonneg _
            · exact le_max_right _ _
        _ = M' := mul_one _
    · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_le.mp hy]
      have hy' : y ∉ closedBall (0 : E) 1 := by simpa using hy
      simp [hbound, indicator_of_notMem hy', h1 _ h2]
  · refine Eventually.of_forall fun y => ?_
    have hc : Tendsto (fun s : ℝ => x + s • y) (𝓝[>] 0) (𝓝 (x + (0 : ℝ) • y)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simp only [zero_smul, add_zero] at hc
    exact ((hw.tendsto x).comp hc).mul_const _

/-- The flow is constant: `Φ(t) = w(x) ∫ ϑ(|y|²) dy` for `0 < t < R`. -/
lemma Phi_const {w : E → ℝ} (hw : ContDiff ℝ 2 w) {x : E} {R : ℝ} (hR : 0 < R)
    (hΔ : ∀ z ∈ ball x R, (Δ w) z = 0) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 1 ϑ)
    (h1 : ∀ τ, 1 ≤ τ → ϑ τ = 0) (hϑ01 : ∀ τ, 0 ≤ ϑ τ ∧ ϑ τ ≤ 1) {t : ℝ} (ht : 0 < t)
    (htR : t < R) :
    Phi w x ϑ t = w x * ∫ y : E, ϑ (‖y‖ ^ 2) := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hd : ∀ s ∈ Ioo (0 : ℝ) R, HasDerivAt (Phi w x ϑ) 0 s := by
    intro s hs
    have := hasDerivAt_Phi hw1 (x := x) hϑ.continuous h1 hϑ01 hs.1 hs.2
    rwa [integral_dflow_eq_zero hw hΔ hϑ h1 hs.1 hs.2] at this
  have hconst : ∀ s ∈ Ioc (0 : ℝ) t, Phi w x ϑ s = Phi w x ϑ t := by
    intro s hs
    have hcont : ContinuousOn (Phi w x ϑ) (Icc s t) := fun r hr =>
      (hd r ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 htR⟩).continuousAt.continuousWithinAt
    have := constant_of_has_deriv_right_zero hcont (fun r hr =>
      (hd r ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_lt_of_le hr.2 htR.le⟩).hasDerivWithinAt) t
      ⟨hs.2, le_rfl⟩
    exact this.symm
  have hlim := tendsto_Phi_zero hw.continuous (x := x) hR hϑ.continuous h1 hϑ01
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), Phi w x ϑ s = Phi w x ϑ t := by
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs using hconst s ⟨hs.1, hs.2.le⟩
  have hlim2 : Tendsto (Phi w x ϑ) (𝓝[>] 0) (𝓝 (Phi w x ϑ t)) :=
    tendsto_const_nhds.congr' (hev.mono fun s hs => hs.symm)
  exact tendsto_nhds_unique hlim2 hlim

end



section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The smooth cut-offs `ϑ_k(τ) = smoothTransition (k (1 - τ))`. -/
noncomputable def vth (k : ℕ) (τ : ℝ) : ℝ := Real.smoothTransition ((k : ℝ) * (1 - τ))

lemma contDiff_vth (k : ℕ) : ContDiff ℝ 1 (vth k) := by
  unfold vth
  exact (Real.smoothTransition.contDiff (n := 1)).comp
    (contDiff_const.mul (contDiff_const.sub contDiff_id))

lemma vth_zero (k : ℕ) {τ : ℝ} (hτ : 1 ≤ τ) : vth k τ = 0 := by
  unfold vth
  apply Real.smoothTransition.zero_of_nonpos
  have : (k : ℝ) * (1 - τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) (by linarith)
  exact this

lemma vth_01 (k : ℕ) (τ : ℝ) : 0 ≤ vth k τ ∧ vth k τ ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma tendsto_vth {τ : ℝ} (hτ : τ < 1) : Tendsto (fun k : ℕ => vth k τ) atTop (𝓝 1) := by
  have : ∀ᶠ k : ℕ in atTop, vth k τ = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (1 - τ))
    filter_upwards [eventually_ge_atTop N] with k hk
    unfold vth
    apply Real.smoothTransition.one_of_one_le
    have h1 : 0 < 1 - τ := by linarith
    have : 1 / (1 - τ) ≤ (k : ℝ) := hN.trans (by exact_mod_cast hk)
    rw [div_le_iff₀ h1] at this
    nlinarith
  exact tendsto_const_nhds.congr' (this.mono fun k hk => hk.symm)

/-- Ball mean value property, rescaled to the unit ball. -/
lemma setIntegral_unitBall_eq {w : E → ℝ} (hw : ContDiff ℝ 2 w) {x : E} {R : ℝ} (hR : 0 < R)
    (hΔ : ∀ z ∈ ball x R, (Δ w) z = 0) {t : ℝ} (ht : 0 < t) (htR : t < R) :
    ∫ y in ball (0 : E) 1, w (x + t • y) = w x * volume.real (ball (0 : E) 1) := by
  have hwc : Continuous w := hw.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hwc.continuousOn
  set M' : ℝ := max M 0 with hM'
  set bound : E → ℝ := (closedBall (0 : E) 1).indicator (fun _ => M') with hbound
  have hbint : Integrable bound volume :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have hk : ∀ k : ℕ, ∫ y : E, w (x + t • y) * vth k (‖y‖ ^ 2) =
      w x * ∫ y : E, vth k (‖y‖ ^ 2) := fun k =>
    Phi_const hw hR hΔ (contDiff_vth k) (fun τ hτ => vth_zero k hτ) (vth_01 k) ht htR
  have hcont : ∀ k : ℕ, Continuous (fun y : E => vth k (‖y‖ ^ 2)) := fun k =>
    (contDiff_vth k).continuous.comp (continuous_norm.pow 2)
  have hmeasF : ∀ k : ℕ, AEStronglyMeasurable (fun y : E => w (x + t • y) * vth k (‖y‖ ^ 2)) volume :=
    fun k => ((hwc.comp (continuous_const.add (continuous_const.smul continuous_id))).mul
      (hcont k)).aestronglyMeasurable
  -- pointwise bound
  have hFb : ∀ k : ℕ, ∀ y : E, ‖w (x + t • y) * vth k (‖y‖ ^ 2)‖ ≤ bound y := by
    intro k y
    by_cases hy : ‖y‖ ≤ 1
    · have hmem : x + t • y ∈ closedBall x R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht]
        calc t * ‖y‖ ≤ R * 1 := mul_le_mul htR.le hy (norm_nonneg _) hR.le
          _ = R := mul_one R
      have hb : ‖w (x + t • y)‖ ≤ M' := (hM _ hmem).trans (le_max_left _ _)
      have hy' : y ∈ closedBall (0 : E) 1 := by simpa using hy
      simp only [hbound, indicator_of_mem hy', norm_mul]
      have := vth_01 k (‖y‖ ^ 2)
      calc ‖w (x + t • y)‖ * ‖vth k (‖y‖ ^ 2)‖ ≤ M' * 1 := by
            apply mul_le_mul hb
            · rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
            · exact norm_nonneg _
            · exact le_max_right _ _
        _ = M' := mul_one _
    · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_le.mp hy]
      have hy' : y ∉ closedBall (0 : E) 1 := by simpa using hy
      simp [hbound, indicator_of_notMem hy', vth_zero k h2]
  have hGb : ∀ k : ℕ, ∀ y : E, ‖vth k (‖y‖ ^ 2)‖ ≤ (closedBall (0 : E) 1).indicator (fun _ => (1 : ℝ)) y := by
    intro k y
    by_cases hy : ‖y‖ ≤ 1
    · have hy' : y ∈ closedBall (0 : E) 1 := by simpa using hy
      simp only [indicator_of_mem hy']
      have := vth_01 k (‖y‖ ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
    · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_le.mp hy]
      have hy' : y ∉ closedBall (0 : E) 1 := by simpa using hy
      simp [indicator_of_notMem hy', vth_zero k h2]
  have hGint : Integrable ((closedBall (0 : E) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  -- limits
  have hlimF := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E)) bound hmeasF
    hbint (fun k => Eventually.of_forall (hFb k))
    (f := (ball (0 : E) 1).indicator (fun y => w (x + t • y)))
    (Eventually.of_forall fun y => by
      by_cases hy : ‖y‖ < 1
      · have hy' : y ∈ ball (0 : E) 1 := by simpa using hy
        simp only [indicator_of_mem hy']
        have := (tendsto_vth (τ := ‖y‖ ^ 2) (by nlinarith [norm_nonneg y])).const_mul (w (x + t • y))
        simpa using this
      · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_lt.mp hy, norm_nonneg y]
        have hy' : y ∉ ball (0 : E) 1 := by simpa using hy
        simp only [indicator_of_notMem hy']
        simp [vth_zero _ h2])
  have hlimG := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
    ((closedBall (0 : E) 1).indicator (fun _ => (1 : ℝ)))
    (fun k => (hcont k).aestronglyMeasurable) hGint (fun k => Eventually.of_forall (hGb k))
    (f := (ball (0 : E) 1).indicator (fun _ => (1 : ℝ)))
    (Eventually.of_forall fun y => by
      by_cases hy : ‖y‖ < 1
      · have hy' : y ∈ ball (0 : E) 1 := by simpa using hy
        simp only [indicator_of_mem hy']
        exact tendsto_vth (by nlinarith [norm_nonneg y])
      · have h2 : 1 ≤ ‖y‖ ^ 2 := by nlinarith [not_lt.mp hy, norm_nonneg y]
        have hy' : y ∉ ball (0 : E) 1 := by simpa using hy
        simp only [indicator_of_notMem hy']
        simp [vth_zero _ h2])
  have hlimG' := hlimG.const_mul (w x)
  have heq : (fun k : ℕ => ∫ y : E, w (x + t • y) * vth k (‖y‖ ^ 2)) =
      fun k : ℕ => w x * ∫ y : E, vth k (‖y‖ ^ 2) := funext hk
  rw [heq] at hlimF
  have := tendsto_nhds_unique hlimF hlimG'
  rw [integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at this
  simpa [setIntegral_const] using this

lemma setIntegral_translate (w : E → ℝ) (x : E) (t : ℝ) :
    ∫ z in ball (0 : E) t, w (x + z) = ∫ z in ball x t, w z := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  rw [← integral_add_left_eq_self (fun z => (ball x t).indicator w z) x]
  congr 1
  ext z
  by_cases hz : z ∈ ball (0 : E) t
  · have : x + z ∈ ball x t := by simpa [mem_ball, dist_eq_norm] using hz
    simp [indicator_of_mem hz, indicator_of_mem this]
  · have : x + z ∉ ball x t := by simpa [mem_ball, dist_eq_norm] using hz
    simp [indicator_of_notMem hz, indicator_of_notMem this]

/-- **Mean value property over balls** for a `C²` function harmonic on `B(x, R)`. -/
lemma ball_average_eq [Nontrivial E] {w : E → ℝ} (hw : ContDiff ℝ 2 w) {x : E} {R : ℝ}
    (hR : 0 < R) (hΔ : ∀ z ∈ ball x R, (Δ w) z = 0) {t : ℝ} (ht : 0 < t) (htR : t < R) :
    ⨍ y in ball x t, w y = w x := by
  have h1 := setIntegral_unitBall_eq hw hR hΔ ht htR
  have h2 := Measure.setIntegral_comp_smul_of_pos (volume : Measure E) (fun z => w (x + z))
    (ball (0 : E) 1) ht
  have hb : t • ball (0 : E) 1 = ball (0 : E) t := by
    rw [_root_.smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  simp only [hb, setIntegral_translate] at h2
  have hpow : 0 < t ^ Module.finrank ℝ E := pow_pos ht _
  have h3 : ∫ z in ball x t, w z = t ^ Module.finrank ℝ E * ∫ y in ball (0 : E) 1, w (x + t • y) := by
    rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul]
  have hvol : volume.real (ball x t) = t ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) := by
    rw [Measure.real, Measure.real, Measure.addHaar_ball (volume : Measure E) x ht.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hpow.le]
  have hvpos : 0 < volume.real (ball (0 : E) 1) := by
    rw [Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  rw [setAverage_eq, h3, h1, hvol, smul_eq_mul]
  field_simp

end



section Liouville
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma real_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = r ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) := by
  rw [Measure.real, Measure.real, Measure.addHaar_ball (volume : Measure E) x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]

/-- The part of one ball outside a second ball of the same radius lies in an annulus. -/
lemma volume_diff_le [Nontrivial E] (x y : E) {t : ℝ} (ht : ‖x - y‖ ≤ t) :
    volume.real (ball x t \ ball y t) ≤
      (t ^ Module.finrank ℝ E - (t - ‖x - y‖) ^ Module.finrank ℝ E) *
        volume.real (ball (0 : E) 1) := by
  set d := ‖x - y‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsub : ball x t \ ball y t ⊆ ball x t \ ball x (t - d) := by
    intro z hz
    refine ⟨hz.1, fun hz' => hz.2 ?_⟩
    rw [mem_ball, dist_eq_norm] at hz' ⊢
    have : ‖z - y‖ ≤ ‖z - x‖ + ‖x - y‖ := by
      calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  calc volume.real (ball x t \ ball y t) ≤ volume.real (ball x t \ ball x (t - d)) :=
        measureReal_mono hsub ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
    _ = volume.real (ball x t) - volume.real (ball x (t - d)) :=
        measureReal_sdiff (ball_subset_ball (by linarith)) measurableSet_ball
          measure_ball_lt_top.ne
    _ = _ := by
        rw [real_ball x (by linarith), real_ball x (by linarith)]; ring

/-- Two ball integrals of a bounded continuous function at nearby centres are close. -/
lemma abs_setIntegral_ball_sub_le [Nontrivial E] {u : E → ℝ} (hc : Continuous u) {M : ℝ}
    (hM : ∀ z, |u z| ≤ M) (x y : E) {t : ℝ} (ht : ‖x - y‖ ≤ t) :
    |(∫ z in ball x t, u z) - ∫ z in ball y t, u z| ≤
      M * (2 * ((t ^ Module.finrank ℝ E - (t - ‖x - y‖) ^ Module.finrank ℝ E) *
        volume.real (ball (0 : E) 1))) := by
  have hint : ∀ c : E, IntegrableOn u (ball c t) volume := fun c =>
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall c t)).mono_set
      ball_subset_closedBall
  have h1 := integral_inter_add_sdiff (μ := volume) (measurableSet_ball (x := y) (ε := t))
    (hint x)
  have h2 := integral_inter_add_sdiff (μ := volume) (measurableSet_ball (x := x) (ε := t))
    (hint y)
  rw [inter_comm] at h2
  have hb : ∀ S : Set E, S ⊆ ball x t ∨ S ⊆ ball y t → |∫ z in S, u z| ≤ M * volume.real S := by
    intro S hS
    have hfin : volume S < ⊤ := by
      rcases hS with h | h
      · exact (measure_mono h).trans_lt measure_ball_lt_top
      · exact (measure_mono h).trans_lt measure_ball_lt_top
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := u) hfin
      (fun z _ => by simpa using hM z)
    simpa using this
  have hxy := hb (ball x t \ ball y t) (Or.inl sdiff_subset)
  have hyx := hb (ball y t \ ball x t) (Or.inr sdiff_subset)
  have e : (∫ z in ball x t, u z) - ∫ z in ball y t, u z =
      (∫ z in ball x t \ ball y t, u z) - ∫ z in ball y t \ ball x t, u z := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have v1 := volume_diff_le x y ht
  have v2 := volume_diff_le y x ((norm_sub_rev y x).le.trans ht)
  rw [norm_sub_rev y x] at v2
  rw [e]
  calc |(∫ z in ball x t \ ball y t, u z) - ∫ z in ball y t \ ball x t, u z|
      ≤ |∫ z in ball x t \ ball y t, u z| + |∫ z in ball y t \ ball x t, u z| := abs_sub _ _
    _ ≤ M * volume.real (ball x t \ ball y t) + M * volume.real (ball y t \ ball x t) :=
        add_le_add hxy hyx
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left v1 hM0, mul_le_mul_of_nonneg_left v2 hM0]


/-- Liouville's theorem for a bounded `C²` function with vanishing Laplacian. -/
lemma liouville_core [Nontrivial E] {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ z, (Δ u) z = 0) {M : ℝ} (hM : ∀ z, |u z| ≤ M) (x y : E) : u x = u y := by
  set d := ‖x - y‖ with hd
  set n := Module.finrank ℝ E with hn
  set V1 := volume.real (ball (0 : E) 1) with hV1
  have hV1pos : 0 < V1 := by
    rw [hV1, Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hd0 : 0 ≤ d := norm_nonneg _
  have hc : Continuous u := hu.continuous
  have key : ∀ t : ℝ, 0 < t → d ≤ t → |u x - u y| ≤ 2 * M * (n * d) / t := by
    intro t ht hdt
    have hax := ball_average_eq hu (x := x) (R := t + 1) (by linarith)
      (fun z _ => hΔ z) ht (by linarith)
    have hay := ball_average_eq hu (x := y) (R := t + 1) (by linarith)
      (fun z _ => hΔ z) ht (by linarith)
    set P := t ^ n with hP
    have hPpos : 0 < P := pow_pos ht n
    have hvol : ∀ c : E, volume.real (ball c t) = P * V1 := fun c => real_ball c ht.le
    rw [setAverage_eq, hvol, smul_eq_mul] at hax hay
    have hVpos : 0 < P * V1 := mul_pos hPpos hV1pos
    set D := (∫ z in ball x t, u z) - ∫ z in ball y t, u z with hD
    have hDb := abs_setIntegral_ball_sub_le hc hM x y hdt
    have e : u x - u y = D / (P * V1) := by
      rw [← hax, ← hay, hD]; field_simp
    have hbern : (t - d) ^ n ≥ P * (1 - n * (d / t)) := by
      have hq : d / t ≤ 1 := (div_le_one ht).2 hdt
      have := one_add_mul_le_pow (a := -(d / t)) (by linarith [div_nonneg hd0 ht.le]) n
      have e2 : t - d = t * (1 + -(d / t)) := by field_simp; ring
      rw [e2, mul_pow]
      have := mul_le_mul_of_nonneg_left this hPpos.le
      nlinarith
    rw [e, abs_div, abs_of_pos hVpos, div_le_iff₀ hVpos]
    have h3 : P - (t - d) ^ n ≤ P * (n * (d / t)) := by linarith
    have h4 : M * (2 * ((P - (t - d) ^ n) * V1)) ≤ M * (2 * (P * (n * (d / t)) * V1)) := by
      apply mul_le_mul_of_nonneg_left _ hM0
      have := mul_le_mul_of_nonneg_right h3 hV1pos.le
      linarith
    calc |D| ≤ M * (2 * ((P - (t - d) ^ n) * V1)) := hDb
      _ ≤ M * (2 * (P * (n * (d / t)) * V1)) := h4
      _ = 2 * M * (n * d) / t * (P * V1) := by field_simp
  by_contra hne
  have hc0 : 0 < |u x - u y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set A := 2 * M * (n * d) with hA
  have hA0 : 0 ≤ A := by positivity
  set t := max (d + 1) (A / |u x - u y| + 1) with ht
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have htd : d ≤ t := by have := le_max_left (d + 1) (A / |u x - u y| + 1); linarith
  have h1 := key t ht0 htd
  have h2 : A / |u x - u y| < t := by
    have := le_max_right (d + 1) (A / |u x - u y| + 1); linarith
  rw [div_lt_iff₀ hc0] at h2
  rw [le_div_iff₀ ht0] at h1
  linarith

end Liouville

end HarmAux

theorem solution {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u Set.univ) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) :
    ∃ c : ℝ, ∀ x, u x = c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨u 0, fun x => ?_⟩
    congr 1
    exact Subsingleton.elim _ _
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
    obtain ⟨M, hM⟩ := hb
    have hc : ContDiff ℝ 2 u := contDiffOn_univ.mp hu.contDiffOn
    have hΔ : ∀ z, (Δ u) z = 0 := fun z => (hu z (mem_univ z)).2.self_of_nhds
    exact ⟨u 0, fun x => HarmAux.liouville_core hc hΔ hM x 0⟩
