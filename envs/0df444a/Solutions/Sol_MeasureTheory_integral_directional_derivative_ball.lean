-- Prove2me | solution 1 for MeasureTheory.integral_directional_derivative_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:29:07.543667+00:00
-- url     : https://prove2.me/submissions/84fc46bf-e4a2-43cf-affd-81d5fdae03ff

import Theorems.Thm_MeasureTheory_integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball
import Theorems.Thm_MeasureTheory_integral_polar_sphere_centered
import Theorems.Thm_MeasureTheory_tendsto_integral_smooth_ball_cutoff
import Theorems.Thm_MeasureTheory_tendsto_integral_smooth_radial_boundary_cutoff
import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
namespace DirectionalBallWork

theorem integral_volumeIoiPow (k : ℕ) (F : ℝ → ℝ) :
    (∫ t : Ioi (0 : ℝ), F t.1 ∂Measure.volumeIoiPow k) =
      ∫ t in Ioi (0 : ℝ), t ^ k * F t := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun t : ℝ => Real.toNNReal (t ^ k) • F t)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change Real.toNNReal (t ^ k) • F t = t ^ k * F t
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg ht.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const k).real_toNNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

def cutoff (x : E) (r ε : ℝ) (y : E) : ℝ :=
  Real.smoothTransition ((r ^ 2 - ‖y - x‖ ^ 2) / ε)

theorem cutoff_contDiff (x : E) (r ε : ℝ) : ContDiff ℝ 1 (cutoff x r ε) := by
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const ε

theorem cutoff_nonneg (x : E) (r ε : ℝ) (y : E) : 0 ≤ cutoff x r ε y :=
  Real.smoothTransition.nonneg _

theorem cutoff_le_one (x : E) (r ε : ℝ) (y : E) : cutoff x r ε y ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cutoff_eq_zero {x : E} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    {y : E} (hy : r ≤ ‖y - x‖) : cutoff x r ε y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hε.le
  nlinarith [norm_nonneg (y - x)]

theorem cutoff_tsupport_subset {x : E} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (cutoff x r ε) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra h
  simp only [mem_closedBall, dist_eq_norm] at h
  have hy' : r ≤ ‖y - x‖ := by
    exact (not_le.mp h).le
  exact hy (cutoff_eq_zero hr hε hy')

theorem cutoff_fderiv (x : E) (r ε : ℝ) (y v : E) :
    fderiv ℝ (cutoff x r ε) y v =
      -(2 / ε) * deriv Real.smoothTransition ((r ^ 2 - ‖y - x‖ ^ 2) / ε) *
        inner ℝ (y - x) v := by
  have h1 := ((hasFDerivAt_id y).sub_const x).norm_sq
  have h2 := (h1.const_sub (r ^ 2)).const_smul ε⁻¹
  have hs : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hd := (hs (ε⁻¹ • (r ^ 2 - ‖id y - x‖ ^ 2))).hasDerivAt
  have h3 := hd.comp_hasFDerivAt y h2
  have heq : cutoff x r ε = fun z =>
      Real.smoothTransition (ε⁻¹ • (r ^ 2 - ‖id z - x‖ ^ 2)) := by
    ext z
    simp [cutoff, div_eq_mul_inv, mul_comm]
  rw [heq]
  change (fderiv ℝ (Real.smoothTransition ∘
    (ε⁻¹ • fun z => r ^ 2 - ‖id z - x‖ ^ 2)) y) v = _
  rw [h3.fderiv]
  simp [div_eq_mul_inv, mul_comm, inner_sub_left]
  ring

theorem transition_deriv_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact .of_forall fun s => by
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg s

def radialCutoff (r ε t : ℝ) : ℝ :=
  Real.smoothTransition ((r ^ 2 - t ^ 2) / ε)

theorem radialCutoff_contDiff (r ε : ℝ) : ContDiff ℝ 1 (radialCutoff r ε) := by
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.sub (contDiff_id.pow 2)).div_const ε

theorem radialCutoff_deriv (r ε t : ℝ) :
    deriv (radialCutoff r ε) t =
      -(2 / ε) * deriv Real.smoothTransition ((r ^ 2 - t ^ 2) / ε) * t := by
  have hs : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hi := ((hasDerivAt_id t).pow 2).const_sub (r ^ 2)
  have hd := (hs _).hasDerivAt.comp t (hi.div_const ε)
  change deriv (Real.smoothTransition ∘ fun z => (r ^ 2 - (id ^ 2) z) / ε) t = _
  rw [hd.deriv]
  simp
  ring

theorem radialCutoff_deriv_zero_of_outer {r ε t : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε) (ht : r ≤ t) :
    deriv (radialCutoff r ε) t = 0 := by
  rw [radialCutoff_deriv, transition_deriv_zero_of_nonpos, mul_zero, zero_mul]
  apply div_nonpos_of_nonpos_of_nonneg _ hε.le
  nlinarith

def sphereFlux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    f (x + t • ω.1) * inner ℝ v ω.1 ∂volume.toSphere

theorem sphereFlux_continuousOn {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hf : ContinuousOn f (closedBall x r)) (v : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (sphereFlux f x v) (Icc 0 r) := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let F : Icc 0 r → S → ℝ := fun t ω => f (x + t.1 • ω.1) * inner ℝ v ω.1
  have hm : ∀ t : Icc 0 r, ∀ ω : S, x + t.1 • ω.1 ∈ closedBall x r := by
    intro t ω
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg t.2.1,
      mem_sphere_zero_iff_norm.mp ω.2, mul_one]
    exact t.2.2
  have hc : Continuous F.uncurry := by
    apply Continuous.mul
    · apply hf.comp_continuous
      · fun_prop
      · intro p
        exact hm p.1 p.2
    · fun_prop
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Icc 0 r => ∫ ω : S, F t ω
    ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
  simpa using continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) hc
    (isCompact_univ : IsCompact (univ : Set S))

theorem cutoff_shell_polar {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hf : ContinuousOn f (closedBall x r)) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y, f y * fderiv ℝ (cutoff x r ε) y v) =
      ∫ t in 0..r, deriv (radialCutoff r ε) t *
        (t ^ (n - 1) * sphereFlux f x v t) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  let j : E → ℝ := fun y => f y * fderiv ℝ (cutoff x r ε) y v
  have hgd : Continuous (fun y => fderiv ℝ (cutoff x r ε) y v) :=
    ((cutoff_contDiff x r ε).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hds : support (fun y => fderiv ℝ (cutoff x r ε) y v) ⊆ closedBall x r :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ v).trans
      (cutoff_tsupport_subset hr.le hε))
  have hjs : support j ⊆ closedBall x r := (support_mul_subset_right _ _).trans hds
  have hj : Integrable j := by
    rw [← integrableOn_iff_integrable_of_support_subset hjs]
    exact (hf.mul hgd.continuousOn).integrableOn_compact (isCompact_closedBall x r)
  have hinner : ∀ t : Ioi (0 : ℝ),
      (∫ ω : S, j (x + t.1 • ω.1) ∂volume.toSphere) =
        deriv (radialCutoff r ε) t.1 * sphereFlux f x v t.1 := by
    intro t
    rw [sphereFlux, ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    have hω : ‖ω.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have ht : 0 < t.1 := t.2
    simp only [j, cutoff_fderiv, radialCutoff_deriv, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht, hω, mul_one,
      inner_smul_right, real_inner_comm]
    ring
  change (∫ y, j y) = _
  rw [MeasureTheory.integral_polar_sphere_centered hn x j hj]
  change (∫ t : Ioi (0 : ℝ), (∫ ω : S, j (x + t.1 • ω.1)
    ∂(volume : Measure E).toSphere) ∂Measure.volumeIoiPow (n - 1)) = _
  simp_rw [hinner]
  rw [integral_volumeIoiPow (n - 1)
    (fun t => deriv (radialCutoff r ε) t * sphereFlux f x v t)]
  have heq : (∫ t in Ioi (0 : ℝ), t ^ (n - 1) *
      (deriv (radialCutoff r ε) t * sphereFlux f x v t)) =
      ∫ t in Ioc (0 : ℝ) r, t ^ (n - 1) *
        (deriv (radialCutoff r ε) t * sphereFlux f x v t) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ ht => ht.1)
    intro t ht
    have htr : r ≤ t := by
      have := ht.2
      simp only [mem_Ioc, not_and, not_le] at this
      exact (this ht.1).le
    simp [radialCutoff_deriv_zero_of_outer hr.le hε htr]
  rw [heq, ← intervalIntegral.integral_of_le hr.le]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

end DirectionalBallWork

theorem solution {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in Metric.ball x r, fderiv ℝ f y v) =
      r ^ (n - 1) *
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere) := by
  let ε : ℕ → ℝ := fun k => r ^ 2 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by dsimp [ε]; positivity
  have hεr : ∀ k, ε k ≤ r ^ 2 := by
    intro k
    dsimp [ε]
    exact div_le_self (sq_nonneg r) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r ^ 2)
    simpa [ε, div_eq_mul_inv] using h
  have hfc : ContinuousOn f (closedBall x r) := fun y hy =>
    (hf y hy).continuousAt.continuousWithinAt
  have hfd : ContinuousOn (fun y => fderiv ℝ f y v) (closedBall x r) := by
    have h : ContinuousOn (fderiv ℝ f) (closedBall x r) := fun y hy =>
      ((hf y hy).continuousAt_fderiv (by norm_num)).continuousWithinAt
    exact h.clm_apply continuousOn_const
  let H : ℝ → ℝ := fun t => t ^ (n - 1) * DirectionalBallWork.sphereFlux f x v t
  have hH : ContinuousOn H (Icc 0 r) :=
    (continuous_pow _).continuousOn.mul (DirectionalBallWork.sphereFlux_continuousOn hfc v)
  have hleft := MeasureTheory.tendsto_integral_smooth_ball_cutoff (μ := volume) hr hfd ε hε hεlim
  have hright := MeasureTheory.tendsto_integral_smooth_radial_boundary_cutoff hr hH ε hε hεr hεlim
  have heq : ∀ k, (∫ y, DirectionalBallWork.cutoff x r (ε k) y * fderiv ℝ f y v) =
      ∫ t in 0..r, -deriv (DirectionalBallWork.radialCutoff r (ε k)) t * H t := by
    intro k
    rw [MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball hf
      (DirectionalBallWork.cutoff_contDiff x r (ε k))
      (DirectionalBallWork.cutoff_tsupport_subset hr.le (hε k)),
      DirectionalBallWork.cutoff_shell_polar hn hr (hε k) hfc v]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [H]
    ring
  have he := tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun k => (heq k).symm))
  exact he
