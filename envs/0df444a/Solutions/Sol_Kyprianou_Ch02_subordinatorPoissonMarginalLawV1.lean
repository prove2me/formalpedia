-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorPoissonMarginalLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:56:48.530797+00:00
-- url     : https://prove2.me/submissions/ca936459-eae2-487c-bb8d-cbae15560454

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_subordinatorPositiveIntensityScaleV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (t : ℝ≥0)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          (Complex.I * ((d * ξ : ℝ) : ℂ) +
            ∫ x in Set.Ioi (0 : ℝ),
              (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)) := by
  obtain ⟨Q, hQ, hs, hchar⟩ := Kyprianou.Ch02.subordinatorPositiveIntensityScaleV1 ν hν hint t
  letI : IsProbabilityMeasure Q := hQ
  let c : ℝ := d * (t : ℝ)
  have hc : 0 ≤ c := mul_nonneg hd t.coe_nonneg
  have htrans : Measurable (fun x : ℝ => x + c) := measurable_id.add measurable_const
  refine ⟨Q.map (fun x => x + c), Measure.isProbabilityMeasure_map htrans.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_apply htrans measurableSet_Iio]
    exact measure_mono_null (fun x hx => show x < 0 from by
      have hh : x + c < 0 := hx
      linarith) hs
  · intro ξ
    rw [MeasureTheory.charFun_map_add_const, hchar, ← Complex.exp_add]
    congr 1
    simp [Real.inner_apply, c]
    push_cast
    ring
