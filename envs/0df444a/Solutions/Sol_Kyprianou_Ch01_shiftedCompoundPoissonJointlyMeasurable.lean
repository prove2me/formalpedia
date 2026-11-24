-- Prove2me | solution 1 for Kyprianou.Ch01.shiftedCompoundPoissonJointlyMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:50:56.229176+00:00
-- url     : https://prove2.me/submissions/b79d85f8-875c-4bd5-9622-116fb5485527
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_shiftedSequencesMeasurable
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences

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
    Measurable
      (fun p : Ω × ℝ≥0 =>
        ProbabilityTheory.compoundPoisson 0
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)
          (p.2 : ℝ)
          p.1) := by
  have hseq :=
    shiftedSequencesMeasurable Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw hSupport
      hHeadLaw hHeadTailIndependent y hy t ht k j
  exact compoundPoissonOfMeasurableSequences
    (fun n w => arrival (n + 1) w) (fun n w => marks (n + 1) w) hseq.1 hseq.2
