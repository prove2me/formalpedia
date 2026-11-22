-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanExpectedPutAtOrBelowBarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:31:37.613798+00:00
-- url     : https://prove2.me/submissions/5d54acbf-699e-4669-871b-030cc73bc7eb

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianImmediateLowerPassageFromBelowBarrierMcKean

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x barrier : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hxb : x ≤ barrier) (hKbarrier : Real.exp barrier ≤ K)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (discountedPut X x K q (firstLowerPassage X x barrier)) P ∧
      (∫ ω, discountedPut X x K q (firstLowerPassage X x barrier) ω ∂P) =
        K - Real.exp x := by
  have hτ :=
    Kyprianou.Ch01.brownianImmediateLowerPassageFromBelowBarrierMcKean
      P X sigma gamma x barrier hsigma hxb hB hXmeas
  have hstart (ω : Ω) : X 0 ω = 0 := by
    simpa using congrFun hB.1.start_zero ω
  have hKx : Real.exp x ≤ K :=
    (Real.exp_le_exp.mpr hxb).trans hKbarrier
  have hreward :
      discountedPut X x K q (firstLowerPassage X x barrier) =ᵐ[P]
        (fun _ : Ω => K - Real.exp x) := by
    filter_upwards [hτ] with ω hω
    simp [discountedPut, hω, hstart ω,
      max_eq_left (sub_nonneg.mpr hKx)]
  constructor
  · exact (integrable_const (K - Real.exp x)).congr hreward.symm
  · calc
      (∫ ω, discountedPut X x K q (firstLowerPassage X x barrier) ω ∂P) =
          ∫ _ω, K - Real.exp x ∂P := integral_congr_ae hreward
      _ = K - Real.exp x := by simp
