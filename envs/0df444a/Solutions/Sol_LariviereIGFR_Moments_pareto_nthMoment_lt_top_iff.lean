-- Prove2me | solution 1 for LariviereIGFR.Moments.pareto_nthMoment_lt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:14:45.732891+00:00
-- url     : https://prove2.me/submissions/bc426a48-2863-4ba1-8fba-5463ca38f220

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LariviereIGFR.Moments

theorem solution (S k : ℝ) (hS : 0 < S) (hk : 0 < k) (n : ℝ) (hn : 0 < n) :
    nthMoment (paretoMeasure S k) n < ⊤ ↔ n < k := by
  have hpdfm : Measurable (paretoPDF S k) :=
    (measurable_paretoPDFReal S k).ennreal_ofReal
  have hgm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ n)) :=
    (measurable_id.pow_const n).ennreal_ofReal
  have h1 : nthMoment (paretoMeasure S k) n =
      ∫⁻ x, ENNReal.ofReal (paretoPDFReal S k x * x ^ n) := by
    unfold nthMoment paretoMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ hpdfm hgm]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, paretoPDF]
    rw [ENNReal.ofReal_mul (paretoPDFReal_nonneg hS.le hk.le x)]
  set f : ℝ → ℝ := fun x => paretoPDFReal S k x * x ^ n with hf
  have hfm : Measurable f := (measurable_paretoPDFReal S k).mul (measurable_id.pow_const n)
  have hf0 : ∀ x, S ≤ x → f x = k * S ^ k * x ^ (n - k - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hS hx
    simp only [hf, paretoPDFReal, if_pos hx]
    have : x ^ (n - k - 1) = x ^ (-(k + 1)) * x ^ n := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]; ring
  have hf1 : ∀ x, x < S → f x = 0 := by
    intro x hx
    simp [hf, paretoPDFReal, not_le.2 hx]
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : S ≤ x
    · rw [hf0 x hx]
      have hx0 : 0 < x := lt_of_lt_of_le hS hx
      have := Real.rpow_pos_of_pos hS k
      have := Real.rpow_pos_of_pos hx0 (n - k - 1)
      positivity
    · rw [hf1 x (not_le.1 hx)]
  rw [h1, lt_top_iff_ne_top, lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfnn)]
  have hsupp : Function.support f ⊆ Set.Ici S := by
    intro x hx
    by_contra hxS
    exact hx (hf1 x (not_le.1 hxS))
  have hunit : IsUnit (k * S ^ k) := by
    have := Real.rpow_pos_of_pos hS k
    exact (mul_pos hk this).ne'.isUnit
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, integrableOn_Ici_iff_integrableOn_Ioi]
  have hcongr : IntegrableOn f (Set.Ioi S) ↔
      IntegrableOn (fun x : ℝ => k * S ^ k * x ^ (n - k - 1)) (Set.Ioi S) :=
    integrableOn_congr_fun (fun x (hx : x ∈ Set.Ioi S) => hf0 x (le_of_lt hx)) measurableSet_Ioi
  rw [hcongr]
  rw [IntegrableOn, integrable_const_mul_iff hunit]
  have := integrableOn_Ioi_rpow_iff (s := n - k - 1) hS
  rw [IntegrableOn] at this
  rw [this]
  constructor <;> intro h <;> linarith
