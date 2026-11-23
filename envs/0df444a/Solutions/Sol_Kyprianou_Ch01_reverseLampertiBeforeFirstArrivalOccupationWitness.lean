-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiBeforeFirstArrivalOccupationWitness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:22:36.073945+00:00
-- url     : https://prove2.me/submissions/7af3d535-0f62-4a64-9cdb-9aab377cbabd

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixOccupationFormula
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiLinearClockWitness
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*}
    (y : Nat) (arrival marks : Nat -> Omega -> Real)
    (t : NNReal) (omega : Omega)
    (hBefore : (y : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega) :
    ∃ s : NNReal,
      (s : Real) < ProbabilityTheory.arrival arrival 0 omega ∧
      (t : ENNReal) <
        reciprocalOccupation (integerCompoundPoisson y arrival marks) s omega := by
  classical
  letI : MeasurableSpace Omega := ⊤
  obtain ⟨s, hsA, hLin⟩ :=
    Kyprianou.Ch01.reverseLampertiLinearClockWitness y t
      (ProbabilityTheory.arrival arrival 0 omega) hBefore
  refine ⟨s, hsA, ?_⟩
  have hConst : ∀ u : NNReal, u ≤ s ->
      integerCompoundPoisson y arrival marks u omega = (y : Int) := by
    intro u hu
    apply Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      y arrival marks u omega
    have huLe : (u : Real) ≤ (s : Real) := by exact_mod_cast hu
    exact lt_of_le_of_lt huLe hsA
  rw [Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula
    (integerCompoundPoisson y arrival marks) omega y s hConst]
  exact hLin