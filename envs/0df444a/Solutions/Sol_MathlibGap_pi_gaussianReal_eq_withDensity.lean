-- Prove2me | solution 1 for MathlibGap.pi_gaussianReal_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:13:09.663335+00:00
-- url     : https://prove2.me/submissions/21f41bfa-3fd6-44b1-bfa3-686dbe413046

import Mathlib
import Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace MGapGaussPi

/-- The density of the standard Gaussian on `Fin k → ℝ`. -/
def gdens (k : ℕ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))

abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

lemma gauss_pi (k : ℕ) : gam k = volume.withDensity (gdens k) := by
  have hg : ∀ x : Fin k → ℝ, gdens k x = ∏ i, gaussianPDF 0 1 (x i) := by
    intro x
    simp only [gdens, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    · rw [NNReal.coe_one, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1; ring
    · rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      simp [neg_div]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (gdens k) =
      fun x => ∏ i, (s i).indicator (gaussianPDF 0 1) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, hg x]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ _)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, volume_pi, lintegral_fintype_prod_eq_prod (fun _ => (s _).indicator _)
    (fun i => (measurable_gaussianPDF 0 1).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero, lintegral_indicator (hs i)]

end MGapGaussPi

end

theorem solution (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))) :=
  MGapGaussPi.gauss_pi k
