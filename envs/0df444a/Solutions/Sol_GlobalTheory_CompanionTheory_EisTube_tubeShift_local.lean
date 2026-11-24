-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:58.229276+00:00
-- url     : https://prove2.me/submissions/f3f5635e-6eb6-4991-b3e0-c3cd7ea1feeb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_gauss_integrable
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_gauss_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_differentiableOn_integral
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_const_of_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (Ω : Set (ι → ℝ)) (H : (ι → ℂ) → ℂ)
    (hH : DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω})
    (x₀ x₁ : ι → ℝ) (R C : ℝ) (hK : Metric.closedBall x₀ R ⊆ Ω)
    (hC : ∀ x ∈ Metric.closedBall x₀ R, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2))
    (hx : dist x₁ x₀ ≤ R / 2) :
    (∫ y : ι → ℝ, H (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I)) =
      ∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I) := by
  have hR : 0 ≤ R := by linarith [dist_nonneg (x := x₁) (y := x₀)]
  let v : ι → ℝ := fun i => x₁ i - x₀ i
  let F : ℂ → (ι → ℝ) → ℂ := fun w y =>
    H (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ))
  let U : Set ℂ := {w | -1 < w.re} ∩ {w | w.re < 2}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hv : ∀ i, |v i| ≤ R / 2 := fun i => by
    have := dist_le_pi_dist x₁ x₀ i
    rw [Real.dist_eq] at this
    exact this.trans hx
  have hmemK : ∀ w ∈ U, (fun i => x₀ i + w.re * v i) ∈ Metric.closedBall x₀ R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_pi_le_iff hR]
    intro i
    rw [Real.dist_eq, add_sub_cancel_left, abs_mul]
    have h1 : |w.re| ≤ 2 := abs_le.2 ⟨by linarith [hw.1.out], hw.2.out.le⟩
    calc |w.re| * |v i| ≤ 2 * (R / 2) := mul_le_mul h1 (hv i) (abs_nonneg _) (by norm_num)
      _ = R := by ring
  have hz : ∀ (w : ℂ) (y : ι → ℝ),
      (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) =
        fun i => (((x₀ i + w.re * v i : ℝ)) : ℂ) + ((y i + w.im * v i : ℝ) : ℂ) * Complex.I := by
    intro w y
    funext i
    apply Complex.ext <;> simp
  have hT : ∀ w ∈ U, ∀ y : ι → ℝ,
      (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) ∈
        {z : ι → ℂ | (fun i => (z i).re) ∈ Ω} := by
    intro w hw y
    have h1 := hK (hmemK w hw)
    rw [hz w y]
    simpa using h1
  have hol : ∀ y, DifferentiableOn ℂ (fun w => F w y) U := by
    intro y
    refine DifferentiableOn.comp (g := H)
      (f := fun w i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) hH ?_
      (fun w hw => hT w hw y)
    exact (differentiable_pi.2 fun i => by fun_prop).differentiableOn
  have hcont : ∀ w ∈ U, Continuous (F w) := by
    intro w hw
    refine hH.continuousOn.comp_continuous ?_ (fun y => hT w hw y)
    exact continuous_pi fun i => by fun_prop
  have hbd : ∀ w ∈ U, ∀ y : ι → ℝ,
      ‖F w y‖ ≤ |C| * Real.exp (-(∑ i, (y i + w.im * v i) ^ 2) / 2) := by
    intro w hw y
    have h1 := hC _ (hmemK w hw) (fun i => y i + w.im * v i)
    have h2 : F w y = H (fun i => (((x₀ i + w.re * v i : ℝ)) : ℂ) +
        ((y i + w.im * v i : ℝ) : ℂ) * Complex.I) := by
      simp only [F]
      rw [hz w y]
    rw [h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hdiff : DifferentiableOn ℂ (fun w => ∫ y, F w y) U := by
    refine tubeShift_differentiableOn_integral volume U hUo F hol
      (fun w hw => (hcont w hw).aestronglyMeasurable) ?_
    intro w₀ _ ρ _ hb
    refine ⟨fun y => (|C| * Real.exp ((|w₀.im| + ρ) ^ 2 * (∑ i, v i ^ 2) / 2)) *
      Real.exp (-(∑ i, y i ^ 2) / 4), (tubeShift_gauss_integrable ι).const_mul _, ?_⟩
    intro w hw y
    refine (hbd w (hb hw) y).trans ?_
    beta_reduce
    rw [mul_assoc |C|]
    refine mul_le_mul_of_nonneg_left (tubeShift_gauss_bound y v _ _ ?_) (abs_nonneg _)
    have h1 : |w.im - w₀.im| ≤ ρ := by
      have h2 := Complex.abs_im_le_norm (w - w₀)
      rw [Complex.sub_im] at h2
      exact h2.trans (by simpa [dist_eq_norm] using hw)
    have h3 := abs_add_le (w.im - w₀.im) w₀.im
    rw [sub_add_cancel] at h3
    linarith
  have hper : ∀ w ∈ U, ∀ s : ℝ,
      (fun w => ∫ y, F w y) (w + (s : ℂ) * Complex.I) = (fun w => ∫ y, F w y) w := by
    intro w _ s
    have h1 : ∀ y : ι → ℝ, F (w + (s : ℂ) * Complex.I) y = F w (y + s • v) := by
      intro y
      simp only [F]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    simp only [h1]
    exact integral_add_right_eq_self (F w) (s • v)
  have h0 : (0 : ℂ) ∈ U := ⟨by simp, by simp⟩
  have h1 : (1 : ℂ) ∈ U := ⟨by simp, by simp⟩
  have key := tubeShift_const_of_periodic U hUo hUc.isPreconnected _ hdiff hper h0 h1
  simp only [F, zero_mul, add_zero, one_mul] at key
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [v]
  congr 1
  funext i
  push_cast
  ring
end GlobalTheory.CompanionTheory.EisTube
