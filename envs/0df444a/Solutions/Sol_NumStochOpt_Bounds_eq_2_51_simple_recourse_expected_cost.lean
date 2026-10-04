-- Prove2me | solution 1 for NumStochOpt.Bounds.eq_2_51_simple_recourse_expected_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:27:01.520933+00:00
-- url     : https://prove2.me/submissions/91fbfa8c-da51-4f74-ba52-96b3a386693b

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse

open MeasureTheory

set_option autoImplicit false

open MeasureTheory NumStochOpt.Bounds in
lemma sr8a6_div_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → ℝ) (S : Set Ω) :
    (∫ ω in S, h ω ∂P) / (P S).toReal * (P S).toReal = ∫ ω in S, h ω ∂P := by
  by_cases h0 : (P S).toReal = 0
  · have hS : P S = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h1 | h1
      · exact h1
      · exact absurd h1 (measure_ne_top P S)
    rw [Measure.restrict_eq_zero.2 hS]
    simp
  · exact div_mul_cancel₀ _ h0

open MeasureTheory NumStochOpt.Bounds in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hj : Ω → ℝ) (hmeas : Measurable hj)
    (hint : Integrable hj P) (qp qm : ℝ) (hq : 0 ≤ qp + qm) (χ : ℝ) :
    ∫ ω, simpleRecourseCost qp qm χ (hj ω) ∂P =
      qp * (condMeanAbove P hj χ - χ) * probAbove P hj χ +
        qm * (χ - condMeanBelow P hj χ) * probBelow P hj χ := by
  set A : Set Ω := {ω | χ ≤ hj ω} with hA
  set B : Set Ω := {ω | hj ω < χ} with hB
  have mA : MeasurableSet A := measurableSet_le measurable_const hmeas
  have mB : MeasurableSet B := measurableSet_lt hmeas measurable_const
  have hf : (fun ω => simpleRecourseCost qp qm χ (hj ω)) =
      fun ω => A.indicator (fun ω => qp * (hj ω - χ)) ω +
        B.indicator (fun ω => qm * (χ - hj ω)) ω := by
    funext ω
    by_cases hc : χ ≤ hj ω
    · have : ¬ hj ω < χ := not_lt.2 hc
      simp [simpleRecourseCost, Set.indicator, hA, hB, hc, this]
    · have : hj ω < χ := not_le.1 hc
      simp [simpleRecourseCost, Set.indicator, hA, hB, hc, this]
  have i1 : Integrable (fun ω => qp * (hj ω - χ)) P :=
    (hint.sub (integrable_const χ)).const_mul qp
  have i2 : Integrable (fun ω => qm * (χ - hj ω)) P :=
    ((integrable_const χ).sub hint).const_mul qm
  rw [hf, integral_add (i1.indicator mA) (i2.indicator mB), integral_indicator mA,
    integral_indicator mB, integral_const_mul, integral_const_mul,
    integral_sub hint.integrableOn (integrable_const χ),
    integral_sub (integrable_const χ) hint.integrableOn, setIntegral_const, setIntegral_const]
  unfold condMeanAbove condMeanBelow probAbove probBelow
  rw [← hA, ← hB]
  have e1 := sr8a6_div_mul P hj A
  have e2 := sr8a6_div_mul P hj B
  simp only [Measure.real, smul_eq_mul]
  rw [mul_assoc qp, mul_assoc qm, sub_mul, sub_mul, e1, e2]
  ring
