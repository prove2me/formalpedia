-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiIndependentAncestorPositiveTimeLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:16:13.603468+00:00
-- url     : https://prove2.me/submissions/71155e7a-c995-4591-b8e1-a9997d298f8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorAfterFirstArrivalContribution
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
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  let F : Nat -> Ω -> Nat :=
    fun y omega => (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t omega).toNat
  let S : Nat -> Set Ω :=
    fun y => {omega | (y : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega}
  let L : Set Ω := {omega | F (a + b) omega = k}
  let R : Set (Ω × Ω) := {zeta | F a zeta.1 + F b zeta.2 = k}
  let V : Set (Ω × Ω) := Set.prod (S a) (S b)
  have hArr : Measurable
      (fun omega : Ω => ProbabilityTheory.arrival arrival 0 omega) := by
    simpa [ProbabilityTheory.arrival] using
      hdriver.measurable_interarrival 0
  have hS (y : Nat) : MeasurableSet (S y) := by
    exact measurableSet_lt measurable_const hArr
  have hV : MeasurableSet V := (hS a).prod (hS b)
  have hNo : Q (L ∩ S (a + b)) = (Q.prod Q) (R ∩ V) := by
    convert (Kyprianou.Ch01.reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion
        K hRealisation a b t ht k) using 1
    · congr 1
      ext omega
      simp [F, S, L, R, V, Set.prod, and_comm, and_left_comm, and_assoc]
    · congr 1
      ext zeta
      simp [F, S, L, R, V, Set.prod, and_comm, and_left_comm, and_assoc]
  have hAfter : Q (L \ S (a + b)) =
      (Q.prod Q) (R \ V) := by
    convert (Kyprianou.Ch01.reverseLampertiIndependentAncestorAfterFirstArrivalContribution
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion
        K hRealisation a b t ht k) using 1
    · congr 1
      ext omega
      simp [F, S, L, R, V, Set.prod, and_comm, and_left_comm, and_assoc]
    · congr 1
      ext zeta
      simp [F, S, L, R, V, Set.prod, and_comm, and_left_comm, and_assoc]
  change Q L = (Q.prod Q) R
  calc
    Q L = Q (L ∩ S (a + b)) + Q (L \ S (a + b)) :=
      (measure_inter_add_diff L (hS (a + b))).symm
    _ = (Q.prod Q) (R ∩ V) + (Q.prod Q) (R \ V) := by
      rw [hNo, hAfter]
    _ = (Q.prod Q) R := measure_inter_add_diff R hV
