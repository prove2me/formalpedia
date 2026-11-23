-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiIndependentAncestorAfterFirstArrivalContribution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:46:04.792436+00:00
-- url     : https://prove2.me/submissions/d8d5381c-2264-4aa9-9cf8-86b9666a6d48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiPositiveTimeFirstJumpRenewal
import Theorems.Thm_Kyprianou_Ch01_branchingFirstJumpRenewalGivesAncestorConvolution
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF
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
        Not (((a + b : Nat) : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ω) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        Not ((a : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.1 ∧ (b : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.2) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  classical
  let F : ℕ → Ω → ℕ := fun y ω =>
    (compoundPoissonToBranching (integerCompoundPoisson y arrival marks)
      t ω).toNat
  let W : Ω × Ω → ℕ := fun z => F a z.1 + F b z.2
  let A : Set Ω := {ω | F (a+b) ω = k}
  let B : Set (Ω × Ω) := {z | W z = k}
  let E : Set Ω := {ω |
    ((a+b : Nat) : Real)*(t : Real) <
      ProbabilityTheory.arrival arrival 0 ω}
  let T : Set (Ω × Ω) := {z |
    (a : Real)*(t : Real) < ProbabilityTheory.arrival arrival 0 z.1 ∧
    (b : Real)*(t : Real) < ProbabilityTheory.arrival arrival 0 z.2}
  have hArr : Measurable
      (fun omega : Ω => ProbabilityTheory.arrival arrival 0 omega) := by
    simpa [ProbabilityTheory.arrival] using
      hdriver.measurable_interarrival 0
  have hmE : MeasurableSet E :=
    measurableSet_lt measurable_const hArr
  have hmT : MeasurableSet T := by
    change MeasurableSet
      (Set.prod
        {ω : Ω | (a : Real)*(t : Real) <
          ProbabilityTheory.arrival arrival 0 ω}
        {ω : Ω | (b : Real)*(t : Real) <
          ProbabilityTheory.arrival arrival 0 ω})
    exact (measurableSet_lt measurable_const (hArr)).prod
      (measurableSet_lt measurable_const (hArr))
  have hr : (0 : Real) < (rate : Real) := by exact_mod_cast hrate
  obtain ⟨hZero, hRenew⟩ :=
    Kyprianou.Ch01.reverseLampertiPositiveTimeFirstJumpRenewal
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
  have hConv :=
    Kyprianou.Ch01.branchingFirstJumpRenewalGivesAncestorConvolution
      (rate : Real) hr offspring K hZero hRenew a b t ht k
  have hTotal : Q A = (Q.prod Q) B := by
    calc
      Q A = K (a+b) t k := by
        simpa [A, F] using (hRealisation (a+b) t k).symm
      _ = ((K a t).bind (fun n =>
          (K b t).map (fun m => n+m))) k := hConv
      _ = (Q.prod Q) B := by
        simpa [B, W, F] using
          (Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
            Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
            hdriver hSupport hJumpMass hNoExplosion K hRealisation a b t k).symm
  have hFirst : Q (A ∩ E) = (Q.prod Q) (B ∩ T) := by
    convert
      (Kyprianou.Ch01.reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation a b t ht k)
      using 1
    · congr 1; ext ω; simp [A, E, F, and_comm]
    · congr 1; ext z; simp [B, T, W, F, and_comm]
  have hDiff : Q (A \ E) = (Q.prod Q) (B \ T) := by
    have hParts : Q (A ∩ E) + Q (A \ E) =
        (Q.prod Q) (B ∩ T) + (Q.prod Q) (B \ T) :=
      (measure_inter_add_diff A hmE).trans
        (hTotal.trans (measure_inter_add_diff B hmT).symm)
    rw [hFirst] at hParts
    exact WithTop.add_left_cancel
      (measure_ne_top (Q.prod Q) (B ∩ T)) hParts
  convert hDiff using 1
  · congr 1; ext ω; simp [A, E, F, and_comm]
  · congr 1; ext z; simp [B, T, W, F, and_comm]
