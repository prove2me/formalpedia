-- Prove2me | solution 1 for Kyprianou.Ch01.frozenConjunctionIntegratesHeadRectangle
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:16:52.983793+00:00
-- url     : https://prove2.me/submissions/28f6f50c-e417-4ee0-8d9b-a28720621ff4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_frozenConjunctionIntegratesHeadPushforward

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
        ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
  rw [← hHeadLaw.map_eq]
  exact frozenConjunctionIntegratesHeadPushforward Q rate hrate offspring hNoZeroJumps arrival
    marks jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j
