-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstHoldingMarkProductLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:23:20.590001+00:00
-- url     : https://prove2.me/submissions/b11fdff0-1617-4892-9904-6003fe717f43

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q := by
  have hIndep : IndepFun (arrival 0) (marks 0) Q := by
    simpa using
      (hdriver.indep.indepFun
        (show (Sum.inl (0 : ℕ) : ℕ ⊕ ℕ) ≠
          Sum.inr (0 : ℕ) by decide))
  exact ProbabilityTheory.IndepFun.hasLaw_prod
    (hdriver.law_interarrival 0) (hdriver.law_mark 0) hIndep
