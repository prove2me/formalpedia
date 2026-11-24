-- Prove2me | solution 1 for Kyprianou.Ch01.frozenConjunctionIntegratesHeadPushforward
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:39:47.742063+00:00
-- url     : https://prove2.me/submissions/6f843ada-589b-462c-b061-508938184661
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_frozenKernelStronglyMeasurable
import Theorems.Thm_Kyprianou_Ch01_independentHeadIntegratesFrozenKernel

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
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)}).toReal =
      ∫ z in Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)},
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ)))
              ω).toNat = k}).toReal
        ∂Q.map (fun w => (arrival 0 w, marks 0 w)) := by
  have hs : MeasurableSet (Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)}) :=
    measurableSet_Iic.prod (measurableSet_singleton ((j : ℝ) - 1))
  have hf :
      AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (Q {ω |
              (compoundPoissonToBranching
                (integerCompoundPoisson
                  ((y - 1) + j)
                  (fun n w => arrival (n + 1) w)
                  (fun n w => marks (n + 1) w))
                (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ)))
                ω).toNat = k}).toReal)
        (Q.map (fun w => (arrival 0 w, marks 0 w))) :=
    frozenKernelStronglyMeasurable Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hSupport hHeadLaw hHeadTailIndependent y hy t ht k j
  rw [setIntegral_map hs hf hHeadLaw.aemeasurable]
  exact independentHeadIntegratesFrozenKernel Q rate hrate offspring hNoZeroJumps arrival marks
    jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j
