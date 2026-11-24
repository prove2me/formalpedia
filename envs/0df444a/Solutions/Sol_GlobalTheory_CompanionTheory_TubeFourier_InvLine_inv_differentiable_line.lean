-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:40.856259+00:00
-- url     : https://prove2.me/submissions/c8325cf4-0c3a-4fb2-9670-84050943426a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_integrable_exp_neg_abs_plane
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_dot_add_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_norm_cexp_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_norm_dot_le
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_le_two_div_mul_exp
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_and_norm_integral_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.InvLine
namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  intro X _ _ _ T _ φ hφ hc g p v τ₀
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g
  have hgU : g ∈ U := mem_of_mem_nhds hU
  have hA : 0 < ‖v.1‖ + ‖v.2‖ + 1 := by positivity
  have hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1) := div_pos hε hA
  have hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 →
      ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε := by
    intro τ hτ w hw q
    have h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) := by
      have := Metric.mem_ball.1 hτ
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖τ - τ₀‖ * ‖w‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) * (‖v.1‖ + ‖v.2‖ + 1) := by gcongr
      _ = ε := by field_simp
  have key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
        * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    refine hM _ ?_ ?_ g hgU t
    · exact hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1
    · exact hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2
  have hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    rw [norm_smul, norm_cexp_dot]
    have h1 := key τ hτ t
    have h2 := Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
    calc _ ≤ Real.exp (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) *
          (M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
            * Real.exp (-ε * (|t.1| + |t.2|))) := by gcongr
      _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr; exact le_abs_self M
  have hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g := by
    intro τ
    refine Continuous.smul ?_ (hc g)
    simp only [dot]
    fun_prop
  have hdotc : Continuous fun t : ℝ × ℝ => dot v t := by
    unfold dot
    fun_prop
  have hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g) :=
    (integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g)
      (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1
  have hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|))) :=
    (integrable_exp_neg_abs_plane (half_pos hε)).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g)
    (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g))
    (x₀ := τ₀) (s := Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)))
    (bound := fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))
    (Metric.ball_mem_nhds _ hr)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    hint
    (Continuous.aestronglyMeasurable (Continuous.smul hdotc (hcont τ₀)))
    (ae_of_all _ fun t τ hτ => by
      rw [norm_smul]
      have h1 := norm_dot_le v t
      have h2 := hFn τ hτ t
      have h3 := le_two_div_mul_exp (s := |t.1| + |t.2|) hε
      have h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|))
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← h5]
      calc _ ≤ ((‖v.1‖ + ‖v.2‖) * (2 / ε * Real.exp (ε / 2 * (|t.1| + |t.2|)))) *
            (|M| * Real.exp (-ε * (|t.1| + |t.2|))) := by
            refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
            gcongr
        _ = _ := by ring)
    hbound
    (ae_of_all _ fun t τ _ => by
      have h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t))
          (Complex.exp (dot (p + τ • v) t) * dot v t) τ := by
        have h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)
        have h3 := h2.cexp
        simp only [← dot_add_smul] at h3
        exact h3
      have h4 := h1.smul_const (φ t g)
      rw [smul_smul, mul_comm]
      exact h4)
  exact (hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)
end GlobalTheory.CompanionTheory.TubeFourier.InvLine
