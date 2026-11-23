-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNoArrivalOnePopulationIndicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:57:20.561963+00:00
-- url     : https://prove2.me/submissions/35b3eb1e-9b5a-4647-8fe9-9106b653aa25

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeInitialArrivalPopulationAE
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (offspring : PMF Nat) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : Real | ∃ k : Nat, x = (k : Real) - 1} = 1)
    (hJumpMass : ∀ k : Nat,
      jumpLaw ({((k : Real) - 1)} : Set Real) = offspring k)
    (hNoExplosion : ∀ y : Nat, ∀ᵐ omega ∂Q,
      ∀ t : NNReal, ∃ s : NNReal,
        (t : ENNReal) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s omega)
    (y : Nat) (t : NNReal) (k : Nat) :
    Q {omega : Omega |
      ((y : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 omega) ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t omega).toNat = k} =
    if k = y then
      Q {omega : Omega | (y : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
    else 0 := by
  classical
  let S : Set Omega := {omega | (y : Real) * (t : Real) <
    ProbabilityTheory.arrival arrival 0 omega}
  let F : Omega -> Nat := fun omega =>
    (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t omega).toNat
  change Q {omega | omega ∈ S ∧ F omega = k} =
    if k = y then Q S else 0
  have hState : ∀ᵐ omega ∂Q, omega ∈ S -> F omega = y := by
    simpa only [S, F, Set.mem_setOf_eq] using
      (Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion y t)
  by_cases hk : k = y
  · subst k
    have hMass : Q {omega | omega ∈ S ∧ F omega = y} = Q S := by
      apply measure_congr
      filter_upwards [hState] with omega homega
      exact propext ⟨fun h => h.1, fun h => ⟨h, homega h⟩⟩
    simpa using hMass
  · have hMass : Q {omega | omega ∈ S ∧ F omega = k} =
        Q (∅ : Set Omega) := by
      apply measure_congr
      filter_upwards [hState] with omega homega
      apply propext
      change ((omega ∈ S ∧ F omega = k) ↔ False)
      constructor
      · intro h
        exact hk (h.2.symm.trans (homega h.1))
      · exact False.elim
    simpa [hk] using hMass