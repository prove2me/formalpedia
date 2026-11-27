-- Prove2me | solution 1 for Kyprianou.Ch04.boundedClockIntegralPerturbationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:08:39.334483+00:00
-- url     : https://prove2.me/submissions/0418d36d-cba6-47b7-a4ac-aa79fca5e0a2

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A common positive-time bound controls every stopped clock integral. -/
theorem solution (U V : ℝ → ℝ) (T : NNReal) (d : ℝ) (hd : 0 ≤ d)
    (hU : IntegrableOn U (Ioc (0 : ℝ) (T : ℝ)) volume)
    (hV : IntegrableOn V (Ioc (0 : ℝ) (T : ℝ)) volume)
    (h : ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), |U s - V s| ≤ d) :
    ∀ t : NNReal, t ≤ T →
      |(∫ s in Icc (0 : ℝ) (t : ℝ), U s) -
        (∫ s in Icc (0 : ℝ) (t : ℝ), V s)| ≤ d * (T : ℝ) := by
  intro t ht
  have hs : Ioc (0 : ℝ) (t : ℝ) ⊆ Ioc (0 : ℝ) (T : ℝ) :=
    fun x hx => ⟨hx.1,hx.2.trans (by exact_mod_cast ht)⟩
  have hu := hU.mono_set hs
  have hv := hV.mono_set hs
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,← integral_sub hu hv]
  have hi : Integrable (fun _ : ℝ => d) (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
    integrable_const d
  calc
    _ = ‖∫ s in Ioc (0 : ℝ) (t : ℝ), (U s - V s)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ s in Ioc (0 : ℝ) (t : ℝ), ‖U s - V s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Ioc (0 : ℝ) (t : ℝ), d := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hi
      exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs' => by
        simpa only [Real.norm_eq_abs] using h s (hs hs'))
    _ = d * (t : ℝ) := by
      simp [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
        ENNReal.toReal_ofReal t.coe_nonneg, mul_comm]
    _ ≤ d * (T : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hd
