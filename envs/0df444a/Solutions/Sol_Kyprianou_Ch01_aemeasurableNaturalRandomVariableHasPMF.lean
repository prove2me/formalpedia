-- Prove2me | solution 1 for Kyprianou.Ch01.aemeasurableNaturalRandomVariableHasPMF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:53:28.046079+00:00
-- url     : https://prove2.me/submissions/87ca7327-8a8f-4180-b786-3b9a19202bde

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
set_option autoImplicit false

/-- The law of an a.e. measurable ℕ-valued random variable is
a normalised PMF with the same singleton event probabilities. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℕ) (hf : AEMeasurable f Q) :
    ∃ p : PMF ℕ, ∀ k : ℕ, p k = Q {ω | f ω = k} := by
  classical
  letI : IsProbabilityMeasure (Q.map f) :=
    Measure.isProbabilityMeasure_map hf
  refine ⟨(Q.map f).toPMF, ?_⟩
  intro k
  calc
    (Q.map f).toPMF k = (Q.map f) {k} :=
      Measure.toPMF_apply (Q.map f) k
    _ = Q (f ⁻¹' {k}) :=
      Measure.map_apply_of_aemeasurable hf (measurableSet_singleton k)
    _ = Q {ω | f ω = k} := by
      congr 1
