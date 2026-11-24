-- Prove2me | solution 1 for Kyprianou.Ch02.positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:49:14.276723+00:00
-- url     : https://prove2.me/submissions/94b63216-591a-45e6-8391-377353ca554a

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ)
    (hm : ∀ n, AEMeasurable (S n) P)
    (hn : ∀ n ω, 0 ≤ S n ω)
    (hb : ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ n, S n ω ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c ≤ ∫ ω, Real.exp (-(S n ω)) ∂P := by
  let V : Ω → ℝ≥0∞ := fun ω => ⨆ n : ℕ, ENNReal.ofReal (S n ω)
  have hV : AEMeasurable V P :=
    AEMeasurable.iSup (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hm n))
  let Z : Ω → ℝ := fun ω => Real.exp (-(V ω).toReal)
  have hZ : AEMeasurable Z P :=
    Real.continuous_exp.measurable.comp_aemeasurable hV.ennreal_toReal.neg
  have hZi : Integrable Z P :=
    Integrable.of_bound hZ.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg))
  have hp : 0 < ∫ ω, Z ω ∂P := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun ω => (Real.exp_pos _).le) hZi).mpr
    have hs : Function.support Z = Set.univ := by
      ext ω
      simp [Z, Function.mem_support, Real.exp_ne_zero]
    rw [hs]
    simp
  refine ⟨∫ ω, Z ω ∂P, hp, ?_⟩
  intro n
  have hEi : Integrable (fun ω => Real.exp (-(S n ω))) P :=
    Integrable.of_bound
      (Real.continuous_exp.measurable.comp_aemeasurable (hm n).neg).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn n ω)))
  apply integral_mono_ae hZi hEi
  filter_upwards [hb] with ω hω
  obtain ⟨B, hB⟩ := hω
  have hVtop : V ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun k => ENNReal.ofReal_le_ofReal (hB k))
  have hle : S n ω ≤ (V ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hVtop).mp (le_iSup (fun k => ENNReal.ofReal (S k ω)) n)
  exact Real.exp_le_exp.mpr (neg_le_neg hle)
