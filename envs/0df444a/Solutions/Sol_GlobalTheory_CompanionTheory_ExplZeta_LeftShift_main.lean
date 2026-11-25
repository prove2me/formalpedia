-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:40.385897+00:00
-- url     : https://prove2.me/submissions/8efac7f1-d746-45ff-aa30-3af0ecb5c4a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_horiz_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_left_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_horiz_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift
namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift
theorem _root_.solution : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℂ → ℂ) (A x a b : ℝ), 0 ≤ A → 2 ≤ x → a ≤ b → 1 ≤ |a| → 1 ≤ |b| → (∀ s : ℂ, s.re ≤ -(1 / 2) → a ≤ s.im → s.im ≤ b → DifferentiableAt ℂ G s ∧ ‖G s‖ ≤ A * (1 + |s.re| + |s.im|)) → ‖∫ t : ℝ in a..b, G (((-(1/2) : ℝ) : ℂ) + t * I) * (x : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ K * A := by
  refine ⟨32, by norm_num, ?_⟩
  intro G A x a b hA hx hab ha hb hG
  have hxC : (x : ℂ) ≠ 0 := by
    have : x ≠ 0 := by linarith
    exact_mod_cast this
  set f : ℂ → ℂ := fun s => G s * (x : ℂ) ^ s / s with hf
  set B : ℝ := max |a| |b| with hBdef
  have hB0 : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have key : ∀ R : ℝ, 1 ≤ R →
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
    intro R hR
    have H : DifferentiableOn ℂ f
        (Set.uIcc (-R) (-(1 / 2)) ×ℂ Set.uIcc a b) := by
      intro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab] at hs
      obtain ⟨⟨_, h2⟩, ⟨h3, h4⟩⟩ := hs
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0] at h2
        norm_num at h2
      have hd := (hG s h2 h3 h4).1
      have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
        (differentiableAt_id).const_cpow (Or.inl hxC)
      exact ((hd.mul hc).div differentiableAt_id hs0).differentiableWithinAt
    have rect : (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
        - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
        + I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        - I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) = 0 :=
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-R, a⟩ ⟨-(1 / 2), b⟩ H
    have horiz : ∀ τ : ℝ, a ≤ τ → τ ≤ b → 1 ≤ |τ| →
        ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + τ * I)‖ ≤ 16 * A := by
      intro τ h1 h2 h3
      refine horiz_integral hA hR fun σ _ hσ => ?_
      have hre : ((σ : ℂ) + τ * I).re = σ := by simp
      have him : ((σ : ℂ) + τ * I).im = τ := by simp
      have hg := (hG (σ + τ * I) (by rw [hre]; exact hσ) (by rw [him]; exact h1)
        (by rw [him]; exact h2)).2
      have := horiz_bound (s := (σ : ℂ) + τ * I) hA hx (by rw [hre]; linarith)
        (by rw [him]; exact h3) hg
      rwa [hre] at this
    have hleft : ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖
        ≤ (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun t : ℝ => f (((-R : ℝ) : ℂ) + t * I))
        (C := A * (1 + R + B) * Real.exp (-R / 2)) ?_
      · rw [abs_of_nonneg (by linarith)] at h1
        linarith
      · intro t ht
        rw [Set.uIoc_of_le hab] at ht
        have hre : (((-R : ℝ) : ℂ) + t * I).re = -R := by simp
        have him : (((-R : ℝ) : ℂ) + t * I).im = t := by simp
        have hg := (hG (((-R : ℝ) : ℂ) + t * I) (by rw [hre]; linarith)
          (by rw [him]; exact ht.1.le) (by rw [him]; exact ht.2)).2
        have htB : |t| ≤ B := by
          rw [abs_le]
          constructor
          · have := neg_abs_le a
            have := le_max_left |a| |b|
            linarith [ht.1]
          · have := le_abs_self b
            have := le_max_right |a| |b|
            linarith [ht.2]
        have := left_bound (s := ((-R : ℝ) : ℂ) + t * I) (B := B) hA hx
          (by rw [hre]; linarith) (by rw [him]; exact htB) hg
        rw [hre, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R)] at this
        exact this
    have hI : ‖I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hI' : ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have heq : I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        = (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
          - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
          + I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) := by
      linear_combination rect
    have hha := horiz a le_rfl hab ha
    have hhb := horiz b hab le_rfl hb
    rw [← hI, heq]
    calc _ ≤ ‖(∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
            - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := norm_add_le _ _
      _ ≤ ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I)‖
            + ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I)‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by rw [hI']; linarith
  have hlim : Tendsto (fun u : ℝ => 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)))
      atTop (𝓝 (32 * A)) := by
    have e0 : Tendsto (fun u : ℝ => u ^ 0 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have e1 : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h := ((e0.const_mul (1 + B)).add (e1.const_mul 2)).const_mul ((b - a) * A)
    have h' := h.const_add (32 * A)
    simp only [mul_zero, add_zero] at h'
    refine h'.congr fun u => ?_
    have : -(2 * u) / 2 = -u := by ring
    rw [this]
    ring
  have hev : ∀ᶠ u : ℝ in atTop,
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact key (2 * u) (by linarith)
  exact ge_of_tendsto hlim hev
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
