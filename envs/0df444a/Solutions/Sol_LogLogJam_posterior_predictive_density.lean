-- Prove2me | solution 1 for LogLogJam.posterior_predictive_density
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:50.162809+00:00
-- url     : https://prove2.me/submissions/5fe0c203-4590-4c55-9fc5-4c82f5f46b48

import Theorems.Thm_LogLogJam_physical_history_likelihood
import Theorems.Thm_LogLogJam_gaussian_seed_mass_one
import Definitions.Def_LogLogJam_postFisher

open MeasureTheory ProbabilityTheory LogLogJam Matrix
open scoped ENNReal

private theorem cov_cont (l : ℝ) (k : ℕ) : Continuous (fun θ => VsqK l θ k) := by
  apply continuous_pi
  rintro ⟨a,i⟩
  apply continuous_pi
  rintro ⟨b,j⟩
  fin_cases a <;> fin_cases b
  all_goals simp [VsqK, Vsq, rot, Matrix.kroneckerMap_apply]
  all_goals fun_prop

private theorem density_meas {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {k : ℕ} (D : X → Matrix (Q k) (Q k) ℝ)
    (hD : Continuous D) (y : X → Q k → ℝ) (hy : Measurable y) :
    Measurable (fun x => outDens k (D x) (y x)) := by
  have hi (i j : Q k) : Measurable (fun x => (D x)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  have hh (i : Q k) : Measurable (fun x => y x i) := (measurable_pi_apply i).comp hy
  simp only [outDens, dotProduct, Matrix.mulVec]
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    exact (Finset.measurable_fun_sum _ fun i _ => (hh i).mul
      (Finset.measurable_fun_sum _ fun j _ => (hi i j).mul (hh j))).neg
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

private theorem density_nn {k : ℕ} (D : Matrix (Q k) (Q k) ℝ) (y : Q k → ℝ) :
    0 ≤ outDens k D y := by unfold outDens; positivity

theorem solution (l : ℝ) (hl : 1 < l) {t : ℕ} (H : Hist t) (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    Measurable (fun y => ENNReal.ofReal (predDens l H k W y)) ∧
    (∫⁻ y, ENNReal.ofReal (predDens l H k W y)) = 1 := by
  let I := volume.restrict (Set.Ico 0 Real.pi)
  let F (θ : ℝ) := histDens l θ H
  have hmF : Measurable F := by
    unfold F histDens obsDens
    apply Finset.measurable_fun_prod
    intro i _
    exact density_meas _ ((cov_cont l _).add continuous_const) _ measurable_const
  have hF θ : 0 ≤ F θ := Finset.prod_nonneg fun i _ => density_nn _ _
  have hN : 0 ≤ postNorm l H := integral_nonneg hF
  have hp θ : 0 ≤ post l H θ := div_nonneg (hF θ) hN
  have hmp : Measurable (post l H) := hmF.div measurable_const
  obtain ⟨hpos, _, hC⟩ := physical_history_likelihood l hl H hH
  have hstrict : 0 < postNorm l H := by
    unfold postNorm
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    apply intervalIntegral.integral_pos Real.pi_pos hC.continuous.continuousOn (fun s _ => (hpos s).le)
    exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hpos 0⟩
  have hf : Integrable F I := hC.continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hpost : (∫⁻ θ, ENNReal.ofReal (post l H θ) ∂I) = 1 := by
    have hpp : Integrable (post l H) I := hf.div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hpp (ae_of_all _ hp)]
    change ENNReal.ofReal (∫ θ, F θ / postNorm l H ∂I) = 1
    rw [integral_div]
    change ENNReal.ofReal (postNorm l H / postNorm l H) = 1
    simp [hstrict.ne']
  let D (θ : ℝ) := VsqK l θ k + Matrix.of W
  let f (p : ℝ × (Q k → ℝ)) := post l H p.1 * outDens k (D p.1) p.2
  have hmf : Measurable f := (hmp.comp measurable_fst).mul (density_meas _
    (((cov_cont l k).comp continuous_fst).add continuous_const) _ measurable_snd)
  have hnf (θ : ℝ) (y : Q k → ℝ) : 0 ≤ f (θ,y) := mul_nonneg (hp _) (density_nn _ _)
  have hmy : Measurable (predDens l H k W) := hmf.stronglyMeasurable.integral_prod_left' (μ := I) |>.measurable
  refine ⟨hmy.ennreal_ofReal, ?_⟩
  have hmarg : (∫⁻ y, ∫⁻ θ, ENNReal.ofReal (f (θ,y)) ∂I) = 1 := by
   calc
    (∫⁻ y, ∫⁻ θ, ENNReal.ofReal (f (θ,y)) ∂I) = ∫⁻ θ, ∫⁻ y, ENNReal.ofReal (f (θ,y)) ∂volume ∂I :=
      lintegral_lintegral_swap (hmf.ennreal_ofReal.comp measurable_swap).aemeasurable
    _ = ∫⁻ θ, ENNReal.ofReal (post l H θ) ∂I := by
      apply lintegral_congr
      intro θ
      simp only [f, ENNReal.ofReal_mul (hp θ), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [show (∫⁻ y, ENNReal.ofReal (outDens k (D θ) y)) = 1 from gaussian_seed_mass_one l θ hl k W hW]
      simp
    _ = 1 := hpost

  have hfun : Measurable (fun y => ∫⁻ θ, ENNReal.ofReal (f (θ,y)) ∂I) :=
    hmf.ennreal_ofReal.lintegral_prod_left'
  have hfinite := ae_lt_top hfun (by rw [hmarg]; simp)
  rw [← hmarg]
  apply lintegral_congr_ae
  filter_upwards [hfinite] with y hy
  change ENNReal.ofReal (∫ θ, f (θ,y) ∂I) = _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun θ => hnf θ y))
    ((hmf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)]
  exact ENNReal.ofReal_toReal hy.ne
