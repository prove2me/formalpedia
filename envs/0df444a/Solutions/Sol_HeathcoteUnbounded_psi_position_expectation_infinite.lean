-- Prove2me | solution 1 for HeathcoteUnbounded.psi_position_expectation_infinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:22:45.561703+00:00
-- url     : https://prove2.me/submissions/db8cab56-5ff3-43df-9f5d-4f0d5dc9bc97

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi
open MeasureTheory HeathcoteUnbounded Set

namespace HCAux

lemma norm_psi (x : ℝ) : ‖psi x‖ = (Ici (1:ℝ)).indicator (fun x => x⁻¹) x := by
  by_cases h : 1 ≤ x
  · have hx : 0 < x := by linarith
    simp [psi, h, Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), abs_of_pos hx]
  · simp [psi, h, Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h)]

lemma enorm_psi (x : ℝ) : ‖psi x‖ₑ = ENNReal.ofReal ((Ici (1:ℝ)).indicator (fun x => x⁻¹) x) := by
  rw [← ofReal_norm_eq_enorm, norm_psi]

lemma lintegral_Ici_eq_Ioi (f : ℝ → ENNReal) : ∫⁻ x in Ici (1:ℝ), f x = ∫⁻ x in Ioi (1:ℝ), f x :=
  setLIntegral_congr Ioi_ae_eq_Ici.symm

end HCAux

open HCAux in
theorem posdom : ∫⁻ x : ℝ, ‖x‖ₑ ^ 2 * ‖psi x‖ₑ ^ 2 = ⊤ := by
  have e : (fun x : ℝ => ‖x‖ₑ ^ 2 * ‖psi x‖ₑ ^ 2) = (Ici (1:ℝ)).indicator (fun _ => 1) := by
    funext x
    by_cases h : 1 ≤ x
    · have hx : 0 < x := by linarith
      rw [Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), enorm_psi,
        Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_pos hx, ← ENNReal.ofReal_pow hx.le, ← ENNReal.ofReal_pow (inv_nonneg.2 hx.le),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [inv_pow, mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h), enorm_psi,
        Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h)]
      simp
  rw [e, lintegral_indicator measurableSet_Ici]
  simp

open HCAux in
theorem posexp : ∫⁻ x : ℝ, ‖x‖ₑ * ‖psi x‖ₑ ^ 2 = ⊤ := by
  have e : (fun x : ℝ => ‖x‖ₑ * ‖psi x‖ₑ ^ 2) = (Ici (1:ℝ)).indicator (fun x => ENNReal.ofReal x⁻¹) := by
    funext x
    by_cases h : 1 ≤ x
    · have hx : 0 < x := by linarith
      rw [Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), enorm_psi,
        Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_pos hx, ← ENNReal.ofReal_pow (inv_nonneg.2 hx.le), ← ENNReal.ofReal_mul hx.le]
      congr 1; field_simp
    · rw [Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h), enorm_psi,
        Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h)]
      simp
  rw [e, lintegral_indicator measurableSet_Ici]
  by_contra hne
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ici 1) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).1 hne
    · exact (measurable_inv.aestronglyMeasurable)
    · refine (ae_restrict_mem measurableSet_Ici).mono (fun x hx => ?_)
      have : (1:ℝ) ≤ x := hx
      simp only [Pi.zero_apply]; positivity
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-1:ℝ)) (Ioi 1) := by
    refine (hint.mono_set Ioi_subset_Ici_self).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Real.rpow_neg_one]
  have := (integrableOn_Ioi_rpow_iff (s := -1) (t := 1) one_pos).1 h2
  linarith

open HCAux in
theorem unitnorm : MemLp psi 2 volume ∧ ∫⁻ x : ℝ, ‖psi x‖ₑ ^ 2 = 1 := by
  have hsq : ∀ x, ‖psi x‖ ^ 2 = (Ici (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) x := by
    intro x
    rw [norm_psi]
    by_cases h : 1 ≤ x
    · have hx : 0 < x := by linarith
      rw [Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h), Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h),
        Real.rpow_neg hx.le, inv_pow]; norm_cast
    · rw [Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h), Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h)]
      simp
  have hint : IntegrableOn (fun x : ℝ => x ^ (-2:ℝ)) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hmeas : AEStronglyMeasurable psi volume := by
    unfold psi
    refine (Measurable.ite measurableSet_Ici ?_ measurable_const).aestronglyMeasurable
    exact (Complex.measurable_ofReal).inv
  have hval : ∫⁻ x : ℝ, ‖psi x‖ₑ ^ 2 = 1 := by
    have e : (fun x : ℝ => ‖psi x‖ₑ ^ 2) = fun x => ENNReal.ofReal ((Ici (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) x) := by
      funext x
      rw [← hsq, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_indicator measurableSet_Ici, setIntegral_congr_set Ioi_ae_eq_Ici.symm,
        integral_Ioi_rpow_of_lt (by norm_num) one_pos]
      norm_num
    · exact (integrable_indicator_iff measurableSet_Ici).2 hint
    · exact Filter.Eventually.of_forall (fun x => by
        simp only [Pi.zero_apply]
        by_cases h : 1 ≤ x
        · rw [Set.indicator_of_mem (show x ∈ Ici (1:ℝ) from h)]; positivity
        · rw [Set.indicator_of_notMem (show x ∉ Ici (1:ℝ) from h)])
  refine ⟨?_, hval⟩
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have : (fun x => ‖psi x‖ ^ 2) = (Ici (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) := funext hsq
  rw [this]
  exact (integrable_indicator_iff measurableSet_Ici).2 hint

theorem solution : ∫⁻ x : ℝ, ‖x‖ₑ * ‖psi x‖ₑ ^ 2 = ⊤ := posexp
