-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_S_adapted_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:43:22.218082+00:00
-- url     : https://prove2.me/submissions/e2ed5ae6-3241-4642-b913-5a35feaee811

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The record-level primitive is strongly adapted and its norm
is bounded by the running record. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) :
    StronglyAdapted F (S L beta) ∧
      ∀ t w, ‖S L beta t w‖ ≤ runningSup L t w := by
  let f : Real → Complex := fun y =>
    Complex.exp (Complex.I * (beta:Complex) * (y:Complex))
  let p : Real → Complex := fun x => ∫ y in (0:Real)..x, f y ∂volume
  have hf : Continuous f := by unfold f; fun_prop
  have hp : Continuous p := intervalIntegral.continuous_primitive
    (fun a b => hf.intervalIntegrable a b) 0
  have hEq (t : NNReal) (w : Ω) : S L beta t w = p (runningSup L t w) := by
    unfold S p
    rw [intervalIntegral.integral_of_le (runningSup_eq_rawSup_nonneg L t w).2]
    exact integral_Icc_eq_integral_Ioc
  refine ⟨?_,?_⟩
  · intro t
    have hU : Adapted F (runningSup L) := (runningSup_isDividendStrategy L).2.2.2
    have hm : Measurable[F t] (S L beta t) := by
      rw [show S L beta t = p ∘ runningSup L t from funext (hEq t)]
      exact hp.measurable.comp (hU t)
    exact hm.stronglyMeasurable
  · intro t w
    rw [hEq]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=runningSup L t w) (f:=f) (C:=1)
      (fun y _ => by simp [f,Complex.norm_exp,Complex.mul_re,Complex.mul_im])
    simpa [p, abs_of_nonneg (runningSup_eq_rawSup_nonneg L t w).2] using h
