-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegLaplaceCellIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:42:28.747867+00:00
-- url     : https://prove2.me/submissions/6c111f48-8b8f-430e-90e7-e6e51d23d152

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hm : AEMeasurable Z P) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let a := ∫ ω, Real.exp (-(u * max (Z ω) 0)) ∂P
    let b := ∫ ω, Real.exp (-(v * max (-Z ω) 0)) ∂P
    a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ 0 ≤ a + b - 1 ∧
      (∫ ω, Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0)) ∂P) = a + b - 1 := by
  dsimp only
  have hpt (z : ℝ) :
      Real.exp (-(u * max z 0 + v * max (-z) 0)) =
        Real.exp (-(u * max z 0)) + Real.exp (-(v * max (-z) 0)) - 1 := by
    by_cases hz : 0 ≤ z
    · have hn : max (-z) 0 = 0 := max_eq_right (neg_nonpos.mpr hz)
      simp [max_eq_left hz, hn]
    · have hz' : z ≤ 0 := le_of_not_ge hz
      have hp : max z 0 = 0 := max_eq_right hz'
      have hn : max (-z) 0 = -z := max_eq_left (neg_nonneg.mpr hz')
      simp [hp, hn]
  have hle (c : ℝ) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) :
      Real.exp (-(c * x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc hx))
  have hmP : AEMeasurable (fun ω => max (Z ω) 0) P := hm.max aemeasurable_const
  have hmN : AEMeasurable (fun ω => max (-Z ω) 0) P := hm.neg.max aemeasurable_const
  have hEa : AEMeasurable (fun ω => Real.exp (-(u * max (Z ω) 0))) P :=
    Real.measurable_exp.comp_aemeasurable (hmP.const_mul u).neg
  have hEb : AEMeasurable (fun ω => Real.exp (-(v * max (-Z ω) 0))) P :=
    Real.measurable_exp.comp_aemeasurable (hmN.const_mul v).neg
  have hEj : AEMeasurable
      (fun ω => Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0))) P :=
    Real.measurable_exp.comp_aemeasurable (((hmP.const_mul u).add (hmN.const_mul v)).neg)
  have hbound (c : ℝ) (hc : 0 ≤ c) (W : Ω → ℝ)
      (hW : AEMeasurable W P) (hWn : ∀ ω, 0 ≤ W ω) :
      Integrable (fun ω => Real.exp (-(c * W ω))) P ∧
        (∫ ω, Real.exp (-(c * W ω)) ∂P) ∈ Icc (0 : ℝ) 1 := by
    have hE : AEMeasurable (fun ω => Real.exp (-(c * W ω))) P :=
      Real.measurable_exp.comp_aemeasurable (hW.const_mul c).neg
    have hI : Integrable (fun ω => Real.exp (-(c * W ω))) P := by
      refine Integrable.of_bound hE.aestronglyMeasurable 1 ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle c hc _ (hWn ω)
    refine ⟨hI, ⟨integral_nonneg fun _ => (Real.exp_pos _).le, ?_⟩⟩
    calc
      (∫ ω, Real.exp (-(c * W ω)) ∂P) ≤ ∫ _ : Ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall fun _ => (Real.exp_pos _).le) (integrable_const 1) ?_
        filter_upwards with ω
        exact hle c hc _ (hWn ω)
      _ = 1 := by simp [integral_const]
  have ha := hbound u hu (fun ω => max (Z ω) 0) hmP fun _ => le_max_right _ _
  have hb := hbound v hv (fun ω => max (-Z ω) 0) hmN fun _ => le_max_right _ _
  have hIa := ha.1
  have hIb := hb.1
  have hIj : Integrable
      (fun ω => Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0))) P := by
    refine Integrable.of_bound hEj.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)
    exact add_nonneg (mul_nonneg hu (le_max_right _ _)) (mul_nonneg hv (le_max_right _ _))
  have heq :
      (∫ ω, Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0)) ∂P) =
        (∫ ω, Real.exp (-(u * max (Z ω) 0)) ∂P) +
          (∫ ω, Real.exp (-(v * max (-Z ω) 0)) ∂P) - 1 := by
    have hcongr :
        (fun ω => Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0))) =ᵐ[P]
          fun ω =>
            (Real.exp (-(u * max (Z ω) 0)) + Real.exp (-(v * max (-Z ω) 0))) - (1 : ℝ) :=
      Eventually.of_forall fun ω => hpt (Z ω)
    calc
      (∫ ω, Real.exp (-(u * max (Z ω) 0 + v * max (-Z ω) 0)) ∂P)
          = ∫ ω, (Real.exp (-(u * max (Z ω) 0)) + Real.exp (-(v * max (-Z ω) 0))) - (1 : ℝ) ∂P :=
            integral_congr_ae hcongr
      _ = (∫ ω, Real.exp (-(u * max (Z ω) 0)) + Real.exp (-(v * max (-Z ω) 0)) ∂P) -
            ∫ _ : Ω, (1 : ℝ) ∂P :=
            integral_sub (hIa.add hIb) (integrable_const (1 : ℝ))
      _ = (∫ ω, Real.exp (-(u * max (Z ω) 0)) ∂P) +
            (∫ ω, Real.exp (-(v * max (-Z ω) 0)) ∂P) -
            ∫ _ : Ω, (1 : ℝ) ∂P := by
              rw [integral_add hIa hIb]
      _ = (∫ ω, Real.exp (-(u * max (Z ω) 0)) ∂P) +
            (∫ ω, Real.exp (-(v * max (-Z ω) 0)) ∂P) - 1 := by
              simp [integral_const]
  refine ⟨ha.2, hb.2, ?_, heq⟩
  rw [← heq]
  exact integral_nonneg fun _ => (Real.exp_pos _).le
