-- Prove2me | solution 1 for Kyprianou.Ch01.frozenArrivalKernelStronglyMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:56:42.344237+00:00
-- url     : https://prove2.me/submissions/436b64c3-5aa6-4629-a0ca-f1b6b1d316dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_frozenTimeKernelStronglyMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    StronglyMeasurable
      (fun a : ℝ =>
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k}).toReal) := by
  have hg : Measurable (fun a : ℝ => Real.toNNReal ((t : ℝ) - a / (y : ℝ))) := by
    refine (continuous_real_toNNReal.comp ?_).measurable
    exact continuous_const.sub (continuous_id.div_const (y : ℝ))
  exact (frozenTimeKernelStronglyMeasurable Q rate hrate offspring hNoZeroJumps arrival marks
    jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j).comp_measurable hg
