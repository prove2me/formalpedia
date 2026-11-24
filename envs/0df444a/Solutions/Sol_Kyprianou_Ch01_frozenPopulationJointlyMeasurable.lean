-- Prove2me | solution 1 for Kyprianou.Ch01.frozenPopulationJointlyMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:32:47.172327+00:00
-- url     : https://prove2.me/submissions/d2730e83-eaa3-4154-a2cb-95931d097825
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_frozenPopulationMeasurable

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
    MeasurableSet
      {p : Ω × ℝ≥0 |
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          p.2
          p.1).toNat = k} := by
  have hY :=
    frozenPopulationMeasurable Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw hSupport
      hHeadLaw hHeadTailIndependent y hy t ht k j
  have hto : Measurable (Int.toNat : ℤ → ℕ) := measurable_of_countable _
  have hcount : Measurable (fun p : Ω × ℝ≥0 =>
      (compoundPoissonToBranching
        (integerCompoundPoisson ((y - 1) + j)
          (fun n w => arrival (n + 1) w) (fun n w => marks (n + 1) w))
        p.2 p.1).toNat) :=
    hto.comp hY
  change MeasurableSet ((fun p : Ω × ℝ≥0 =>
      (compoundPoissonToBranching
        (integerCompoundPoisson ((y - 1) + j)
          (fun n w => arrival (n + 1) w) (fun n w => marks (n + 1) w))
        p.2 p.1).toNat) ⁻¹' {k})
  exact hcount (measurableSet_singleton k)
