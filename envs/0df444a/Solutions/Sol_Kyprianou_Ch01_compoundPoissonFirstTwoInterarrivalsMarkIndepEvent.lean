-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:54:25.163133+00:00
-- url     : https://prove2.me/submissions/a258c147-ffac-41e4-a96a-d3b59c92c15d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (u v a : ℝ) :
    Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v ∧ marks 0 ω = a} =
      Q {ω | arrival 0 ω ≤ u} *
        Q {ω | arrival 1 ω ≤ v} *
        Q {ω | marks 0 ω = a} := by
  have hm : ∀ i : ℕ ⊕ ℕ,
      Measurable (Sum.elim arrival marks i) := by
    intro i
    cases i with
    | inl n => exact hdriver.measurable_interarrival n
    | inr n => exact hdriver.measurable_mark n
  have hpair : IndepFun
      (fun ω : Ω => (arrival 0 ω, arrival 1 ω))
      (marks 0) Q := by
    have h := hdriver.indep.indepFun_prodMk hm
      (Sum.inl 0) (Sum.inl 1) (Sum.inr 0)
      (by simp) (by simp)
    simpa only [Sum.elim_inl, Sum.elim_inr] using h
  have htwo : IndepFun (arrival 0) (arrival 1) Q := by
    have h := hdriver.indep.indepFun
      (i := (Sum.inl 0 : ℕ ⊕ ℕ)) (j := Sum.inl 1)
      (by simp)
    simpa only [Sum.elim_inl] using h
  have hpairSet :
      MeasurableSet {z : ℝ × ℝ | z.1 ≤ u ∧ z.2 ≤ v} := by
    measurability
  have htriple := hpair.measure_inter_preimage_eq_mul
    {z : ℝ × ℝ | z.1 ≤ u ∧ z.2 ≤ v}
    ({a} : Set ℝ) hpairSet (measurableSet_singleton a)
  have htwoSet := htwo.measure_inter_preimage_eq_mul
    (Set.Iic u) (Set.Iic v) measurableSet_Iic measurableSet_Iic
  have hfirst :
      Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v ∧
        marks 0 ω = a} =
      Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v} *
        Q {ω | marks 0 ω = a} := by
    simpa [Set.preimage, Set.inter_def, Set.mem_setOf_eq,
      and_assoc] using htriple
  have hsecond :
      Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v} =
      Q {ω | arrival 0 ω ≤ u} *
        Q {ω | arrival 1 ω ≤ v} := by
    simpa [Set.preimage, Set.inter_def, Set.mem_setOf_eq,
      Set.Iic] using htwoSet
  rw [hfirst, hsecond]

