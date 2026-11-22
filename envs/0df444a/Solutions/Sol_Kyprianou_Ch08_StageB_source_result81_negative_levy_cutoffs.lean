-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_negative_levy_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:50:03.854079+00:00
-- url     : https://prove2.me/submissions/6b83819b-cd07-4e24-b635-737265207c0e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (hneg : ν (Ici (0 : ℝ)) = 0) :
    (∀ n : ℕ, IsFiniteMeasure (ν.restrict (Iic (-(((n : ℝ) + 1)⁻¹))))) ∧
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : ℝ → G), Integrable F ν →
      Tendsto (fun n : ℕ => ∫ y in Iic (-(((n : ℝ) + 1)⁻¹)), F y ∂ν)
        atTop (nhds (∫ y, F y ∂ν)) := by
  let c (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  let S (n : ℕ) := Iic (-c n)
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  refine ⟨?_, ?_⟩
  · intro n
    let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min 1 (x ^ 2))
    let u := ENNReal.ofReal (min 1 (c n ^ 2))
    have hg : Measurable g := by fun_prop
    have hu : 0 < u := ENNReal.ofReal_pos.mpr (lt_min zero_lt_one (pow_pos (hc n) _))
    have hsub : S n ⊆ {x | u ≤ g x} := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply min_le_min le_rfl
      have hx' : c n ≤ -x := by
        change x ≤ -c n at hx
        linarith only [hx]
      simpa only [neg_sq] using pow_le_pow_left₀ (hc n).le hx' 2
    have hb := (measure_mono (μ := ν) hsub).trans
      (meas_ge_le_lintegral_div hg.aemeasurable hu.ne' ENNReal.ofReal_ne_top)
    apply isFiniteMeasure_restrict.2
    refine (hb.trans_lt ?_).ne
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top hν.2 (ENNReal.inv_lt_top.mpr hu)
  · intro G _ _ _ F hF
    have hlim : Tendsto c atTop (nhds 0) := tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun n : ℕ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop)
    have hmono : Monotone S := by
      intro i j hij
      apply Iic_subset_Iic.mpr
      exact neg_le_neg (inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hij) le_rfl))
    have hcover : (⋃ n, S n) = Iio (0 : ℝ) := by
      ext y
      constructor
      · intro h
        obtain ⟨n, hn⟩ := mem_iUnion.1 h
        exact lt_of_le_of_lt hn (neg_neg_of_pos (hc n))
      · intro hy
        obtain ⟨n, hn⟩ := (hlim.eventually_lt_const (neg_pos.mpr hy)).exists
        refine mem_iUnion.2 ⟨n, ?_⟩
        change y ≤ -c n
        linarith only [hn]
    have hre : ν.restrict (Iio 0) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      change ν (Iio (0 : ℝ))ᶜ = 0
      rwa [compl_Iio]
    simpa only [hcover, hre] using
      (tendsto_setIntegral_of_monotone (μ := ν) (s := S) (fun _ => measurableSet_Iic) hmono hF.integrableOn)
