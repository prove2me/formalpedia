-- Prove2me | solution 1 for LogLogJam.lemma_5_10
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:41:11.267272+00:00
-- url     : https://prove2.me/submissions/e0bb76fb-bca6-4435-871c-dff957c35568

import Theorems.Thm_LogLogJam_physical_history_likelihood
import Theorems.Thm_LogLogJam_lemma_5_11
import Theorems.Thm_LogLogJam_posterior_fisher_gain_identity
import Mathlib
import Definitions.Def_LogLogJam_postFisher

open MeasureTheory
open scoped ENNReal
open LogLogJam
theorem solution (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (postFisher lam) =
        postFisher lam H +
          ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ ∧
      ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ ≤
        (1 + ENNReal.ofReal Real.pi * (postFisher lam H) ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ) := by
  refine ⟨posterior_fisher_gain_identity lam hlam H hH k W hW, ?_⟩
  obtain ⟨hp, hper, hc⟩ := physical_history_likelihood lam hlam H hH
  have hz : 0 < postNorm lam H := by
    unfold postNorm
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    apply intervalIntegral.integral_pos Real.pi_pos hc.continuous.continuousOn (fun s _ => (hp s).le)
    exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hp 0⟩
  have hpm (s : ℝ) : 0 < post lam H s := div_pos (hp s) hz
  have hcycle (s : ℝ) : post lam H (s+Real.pi) = post lam H s := by simp only [post,hper]
  have hpc : ContDiff ℝ 1 (post lam H) := hc.div_const _
  have hunit : ∫ s in Set.Ico 0 Real.pi, post lam H s = 1 := by
    simp only [post,integral_div]; exact div_self hz.ne'
  let f := fun s => measFisher lam k W s
  let c := ENNReal.ofReal (1 / Real.pi)
  let P := ENNReal.ofReal Real.pi
  let v := (postFisher lam H)^(1/2:ℝ)
  have hpc1 : P * c = 1 := by
    dsimp [P,c]; rw [← ENNReal.ofReal_mul Real.pi_pos.le]; simp [Real.pi_ne_zero]
  have hfinite : c + v ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨ENNReal.ofReal_ne_top, ?_⟩
    have hvf : postFisher lam H ≠ ⊤ := by
      let F := fun θ => post lam H θ * ((deriv (fun x => Real.log (post lam H x)) θ)^2)
      have hcont : Continuous F := hpc.continuous.mul (((hpc.log (fun s => (hpm s).ne')).continuous_deriv_one).pow 2)
      have hi := hcont.integrableOn_Icc (a:=0) (b:=Real.pi) (μ:=volume)
      have hh := ofReal_integral_eq_lintegral_ofReal (hi.mono_set Set.Ico_subset_Icc_self)
        (ae_of_all _ (fun s => mul_nonneg (hpm s).le (sq_nonneg _)))
      change (∫⁻ x in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H x) * _) ≠ ⊤
      have eq : (∫⁻ x in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H x) * ENNReal.ofReal ((deriv (fun a => Real.log (post lam H a)) x)^2)) = ENNReal.ofReal (∫ x in Set.Ico 0 Real.pi, F x) := by
        rw [hh]; apply lintegral_congr; intro x; exact (ENNReal.ofReal_mul (hpm x).le).symm
      exact eq ▸ ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvf
  calc
    _ ≤ ∫⁻ s in Set.Ico 0 Real.pi, (c+v) * f s := by
      apply lintegral_mono; intro s
      exact mul_le_mul' (lemma_5_11 _ hpm hcycle hpc hunit s) le_rfl
    _ = (c+v) * ∫⁻ s in Set.Ico 0 Real.pi, f s := lintegral_const_mul' _ _ hfinite
    _ = _ := by
      change _ = (1+P*v)*(c*_)
      have hs : (1+P*v)*c = c+v := by rw [add_mul, one_mul, mul_right_comm P v c, hpc1, one_mul]
      rw [← mul_assoc,hs]
