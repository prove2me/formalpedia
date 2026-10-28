-- Prove2me | solution 1 for LL_Linnik1536a.markov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:48:57.654181+00:00
-- url     : https://prove2.me/submissions/225efe92-08ff-4fdc-a4ff-f3814815f056

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

theorem solution {L : ℕ} {d lam : ℝ} (hlam : 0 ≤ lam) :
    volume (LL_Linnik1536a.devSet L d) ≤
      ENNReal.ofReal (Real.exp (-(lam * d * L)) *
        ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖LL_Linnik1536a.Gpow L x‖)) := by
  set f : ℝ → ℝ := fun x => Real.exp (lam * ‖LL_Linnik1536a.Gpow L x‖) with hf
  have hcont : Continuous f := by
    rw [hf]; unfold LL_Linnik1536a.Gpow; fun_prop
  set c := Real.exp (lam * d * L) with hcdef
  have hc : 0 < c := Real.exp_pos _
  have hsub : LL_Linnik1536a.devSet L d ⊆ {0} ∪ ({x | c ≤ f x} ∩ Set.Ioc 0 1) := by
    rintro x ⟨⟨h0, h1⟩, hx⟩
    rcases h0.eq_or_lt with h | h
    · left; exact h.symm
    · right
      refine ⟨?_, h, h1⟩
      show Real.exp (lam * d * L) ≤ Real.exp (lam * ‖LL_Linnik1536a.Gpow L x‖)
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hx.le hlam
      linarith [this]
  have hmeas : MeasurableSet {x | c ≤ f x} := measurableSet_le measurable_const hcont.measurable
  have hint : IntegrableOn f (Set.Ioc 0 1) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hint c
  have hfin : (volume.restrict (Set.Ioc (0:ℝ) 1)) {x | c ≤ f x} ≠ ⊤ := by
    rw [Measure.restrict_apply hmeas]
    exact ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)
  calc volume (LL_Linnik1536a.devSet L d)
      ≤ volume ({0} ∪ ({x | c ≤ f x} ∩ Set.Ioc 0 1)) := measure_mono hsub
    _ ≤ volume ({0} : Set ℝ) + volume ({x | c ≤ f x} ∩ Set.Ioc 0 1) := measure_union_le _ _
    _ = (volume.restrict (Set.Ioc (0:ℝ) 1)) {x | c ≤ f x} := by
        rw [Real.volume_singleton, zero_add, Measure.restrict_apply hmeas]
    _ ≤ ENNReal.ofReal (c⁻¹ * ∫ x in Set.Ioc (0:ℝ) 1, f x) := by
        rw [← ENNReal.ofReal_toReal hfin]
        apply ENNReal.ofReal_le_ofReal
        rw [le_inv_mul_iff₀ hc]
        exact hm
    _ = _ := by
        rw [intervalIntegral.integral_of_le zero_le_one, Real.exp_neg]
