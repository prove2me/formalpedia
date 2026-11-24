-- Prove2me | solution 1 for Kyprianou.Ch01.shiftedSequencesMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:44:14.413355+00:00
-- url     : https://prove2.me/submissions/f6a03e5a-5847-47b0-bf89-fae7ec2d5571
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_driverSequencesMeasurable

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
    (∀ n : ℕ, Measurable (fun w => arrival (n + 1) w)) ∧
      ∀ n : ℕ, Measurable (fun w => marks (n + 1) w) := by
  have hdrv :=
    driverSequencesMeasurable Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw hSupport
      hHeadLaw hHeadTailIndependent y hy t ht k j
  exact ⟨fun n => hdrv.1 (n + 1), fun n => hdrv.2 (n + 1)⟩
