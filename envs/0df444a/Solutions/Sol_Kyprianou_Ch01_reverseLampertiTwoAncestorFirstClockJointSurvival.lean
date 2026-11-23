-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoAncestorFirstClockJointSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:10:54.685556+00:00
-- url     : https://prove2.me/submissions/f3b0c26b-0507-4ea3-ba5f-ada7c51b3fe2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (a b : Nat) (t : NNReal) :
    ((Q.prod Q) (Set.prod
      {omega : Omega | (a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
      {omega : Omega | (b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega})).toReal =
    Real.exp (-((rate : Real) *
      (((a + b : Nat) : Real) * (t : Real)))) := by
  let Sa : Set Omega :=
    {omega : Omega | (a : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega}
  let Sb : Set Omega :=
    {omega : Omega | (b : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega}
  change ((Q.prod Q) (Sa ×ˢ Sb)).toReal =
    Real.exp (-((rate : Real) *
      (((a + b : Nat) : Real) * (t : Real))))
  have ha := Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
    Q rate hrate arrival marks jumpLaw hdriver a t
  have hb := Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
    Q rate hrate arrival marks jumpLaw hdriver b t
  have hexp :
      -((rate : Real) * (((a + b : Nat) : Real) * (t : Real))) =
      -((rate : Real) * ((a : Real) * (t : Real))) +
      -((rate : Real) * ((b : Real) * (t : Real))) := by
    push_cast
    ring
  rw [Measure.prod_prod, ENNReal.toReal_mul, ha, hb, hexp, Real.exp_add]
