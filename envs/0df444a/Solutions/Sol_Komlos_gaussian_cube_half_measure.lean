-- Prove2me | solution 1 for Komlos.gaussian_cube_half_measure
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:34:56.74005+00:00
-- url     : https://prove2.me/submissions/2836a32e-21b3-4551-9669-bbf32a4a2a1f

import Definitions.Def_Komlos_model
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace BanaszczykGaussianCube

lemma gaussian_subgaussian : HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by simp [mgf_id_gaussianReal]

lemma std_coordinate_map (m : ℕ) (j : Fin m) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => x j) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) j).map_eq

lemma coordinate_subgaussian (m : ℕ) (j : Fin m) :
    HasSubgaussianMGF (fun x : EuclideanSpace ℝ (Fin m) => x j) 1
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  rw [← HasSubgaussianMGF.id_map_iff (by fun_prop), std_coordinate_map]
  exact gaussian_subgaussian

lemma coordinate_abs_tail (m : ℕ) (j : Fin m) (r : ℝ) (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | r < |x j|} ≤
      2 * Real.exp (-r^2/2) := by
  let mu := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hp := (coordinate_subgaussian m j).measure_ge_le hr
  have hn := (coordinate_subgaussian m j).neg.measure_ge_le hr
  simp only [NNReal.coe_one, mul_one, Pi.neg_apply] at hp hn
  calc
    _ ≤ mu.real ({x | r ≤ x j} ∪ {x | r ≤ -x j}) := by
      exact measureReal_mono (by
        intro x hx
        rcases lt_abs.mp (show r < |x j| from hx) with h | h
        · exact Or.inl h.le
        · exact Or.inr h.le)
    _ ≤ mu.real {x | r ≤ x j} + mu.real {x | r ≤ -x j} := measureReal_union_le _ _
    _ ≤ _ := by dsimp [mu]; linarith



lemma cube_measurable (m : ℕ) (r : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin m) | ∀ j, |x j| ≤ r} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le (by fun_prop) measurable_const)

lemma cube_half_measure (m : ℕ) :
    (1/2 : ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real
      {x | ∀ j, |x j| ≤ 2 * Real.sqrt (Real.log ((m:ℝ)+2))} := by
  let mu := stdGaussian (EuclideanSpace ℝ (Fin m))
  let r := 2 * Real.sqrt (Real.log ((m:ℝ)+2))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp : 0 < (m:ℝ)+2 := by positivity
  have hlog : 0 ≤ Real.log ((m:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hexp : Real.exp (-r^2/2) = 1 / ((m:ℝ)+2)^2 := by
    have hsq := Real.sq_sqrt hlog
    have he : -r^2/2 = -Real.log (((m:ℝ)+2)^2) := by
      dsimp [r]
      rw [Real.log_pow]
      norm_num
      nlinarith
    rw [he, Real.exp_neg, Real.exp_log (sq_pos_of_pos hp), one_div]
  have hbad : mu.real {x | ∃ j, r < |x j|} ≤ (1/2:ℝ) := by
    calc
      _ = mu.real (⋃ j : Fin m, {x | r < |x j|}) := by simp only [ofPred_exists]
      _ ≤ ∑ j : Fin m, mu.real {x | r < |x j|} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin m, 2 * Real.exp (-r^2/2) := by
        exact Finset.sum_le_sum (fun j _ => coordinate_abs_tail m j r hr)
      _ = (m:ℝ) * (2 / ((m:ℝ)+2)^2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hexp]
        ring
      _ ≤ 1/2 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
        rw [← mul_div_assoc, div_mul_eq_mul_div]
        apply (div_le_iff₀ (sq_pos_of_pos hp)).2
        nlinarith [sq_nonneg (m:ℝ)]
  have hc := measureReal_add_measureReal_compl (μ := mu) (cube_measurable m r)
  have heq : {x : EuclideanSpace ℝ (Fin m) | ∀ j, |x j| ≤ r}ᶜ = {x | ∃ j, r < |x j|} := by
    ext x
    simp
  rw [heq] at hc
  have hu : mu.real Set.univ = 1 := by exact probReal_univ
  rw [hu] at hc
  exact (by dsimp [mu,r] at *; linarith)



end BanaszczykGaussianCube

open BanaszczykGaussianCube

theorem solution (m : ℕ) :
    (1/2 : ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real
      {x | ∀ j, |x j| ≤ 2 * Real.sqrt (Real.log ((m:ℝ)+2))} := by
  exact cube_half_measure m

#print axioms solution
