-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:49:45.864855+00:00
-- url     : https://prove2.me/submissions/b004dbaa-3eb9-49ea-8da1-d1a8d4da2901

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoArrivalOnePopulationIndicator
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoArrivalTwoPopulationIndicator
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiJointFirstArrivalSurvivalMass
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (a b : ℕ) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    Q {ω |
        (((a + b : Nat) : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ω) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        ((a : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.1 ∧ (b : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.2) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  let Ssum : Set Ω := {omega | ((a + b : Nat) : Real) * (t : Real) <
    ProbabilityTheory.arrival arrival 0 omega}
  let Sa : Set Ω := {omega | (a : Real) * (t : Real) <
    ProbabilityTheory.arrival arrival 0 omega}
  let Sb : Set Ω := {omega | (b : Real) * (t : Real) <
    ProbabilityTheory.arrival arrival 0 omega}
  let V : Set (Ω × Ω) := Set.prod Sa Sb
  let F : Nat -> Ω -> Nat := fun y omega =>
    (compoundPoissonToBranching (integerCompoundPoisson y arrival marks)
      t omega).toNat
  change Q {omega | omega ∈ Ssum ∧ F (a + b) omega = k} =
    (Q.prod Q) {zeta |
      (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
      F a zeta.1 + F b zeta.2 = k}
  have hOne : Q {omega | omega ∈ Ssum ∧ F (a + b) omega = k} =
      if k = a + b then Q Ssum else 0 :=
    Kyprianou.Ch01.reverseLampertiNoArrivalOnePopulationIndicator
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion (a + b) t k
  have hPair :
      (Q.prod Q) {zeta |
        (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
        F a zeta.1 + F b zeta.2 = k} =
      if k = a + b then (Q.prod Q) V else 0 :=
    Kyprianou.Ch01.reverseLampertiNoArrivalTwoPopulationIndicator
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion a b t k
  have hSurvival : Q Ssum = (Q.prod Q) V :=
    Kyprianou.Ch01.reverseLampertiJointFirstArrivalSurvivalMass
      Q rate hrate arrival marks jumpLaw hdriver a b t
  calc
    Q {omega | omega ∈ Ssum ∧ F (a + b) omega = k} =
        if k = a + b then Q Ssum else 0 := hOne
    _ = if k = a + b then (Q.prod Q) V else 0 := by
      rw [hSurvival]
    _ = (Q.prod Q) {zeta |
      (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
      F a zeta.1 + F b zeta.2 = k} := hPair.symm