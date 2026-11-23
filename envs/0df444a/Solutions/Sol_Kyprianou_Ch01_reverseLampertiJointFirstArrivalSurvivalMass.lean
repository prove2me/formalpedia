-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiJointFirstArrivalSurvivalMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:50:22.438018+00:00
-- url     : https://prove2.me/submissions/fcb2cf64-54be-4be4-8aa7-a7d2de204366

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoAncestorFirstClockJointSurvival
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
    Q {omega : Omega | ((a + b : Nat) : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega} =
    (Q.prod Q) (Set.prod
      {omega : Omega | (a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
      {omega : Omega | (b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}) := by
  let S : Set Omega := {omega | ((a + b : Nat) : Real) * (t : Real) <
    ProbabilityTheory.arrival arrival 0 omega}
  let V : Set (Omega × Omega) := Set.prod
      {omega : Omega | (a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
      {omega : Omega | (b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
  change Q S = (Q.prod Q) V
  have hCombined := Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
    Q rate hrate arrival marks jumpLaw hdriver (a + b) t
  have hJoint := Kyprianou.Ch01.reverseLampertiTwoAncestorFirstClockJointSurvival
    Q rate hrate arrival marks jumpLaw hdriver a b t
  have hFiniteCombined : Q S ≠ ⊤ := measure_ne_top Q S
  have hFiniteJoint : (Q.prod Q) V ≠ ⊤ :=
    measure_ne_top (Q.prod Q) V
  calc
    Q S = ENNReal.ofReal (Q S).toReal :=
      (ENNReal.ofReal_toReal hFiniteCombined).symm
    _ = ENNReal.ofReal ((Q.prod Q) V).toReal := by
      rw [show (Q S).toReal =
        Real.exp (-((rate : Real) *
          (((a + b : Nat) : Real) * (t : Real)))) from hCombined]
      rw [show ((Q.prod Q) V).toReal =
        Real.exp (-((rate : Real) *
          (((a + b : Nat) : Real) * (t : Real)))) from hJoint]
    _ = (Q.prod Q) V := ENNReal.ofReal_toReal hFiniteJoint