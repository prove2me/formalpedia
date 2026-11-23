-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveDiagonalGenerator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:12:56.880923+00:00
-- url     : https://prove2.me/submissions/9044a5e6-870c-43ff-bab7-6fd143cf65c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_branchingZeroAbsorbing
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveHasBranchingProperty
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosivePositiveDiagonalGenerator
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ y : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal)
        (-((rate : ℝ) * (y : ℝ)))
        (Set.Ici 0) 0 := by
  intro y
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst y
    have hbranch : HasBranchingProperty K :=
      Kyprianou.Ch01.reverseLampertiNonexplosiveHasBranchingProperty
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation
    have hzero := Kyprianou.Ch01.branchingZeroAbsorbing K hbranch
    have hfun :
        (fun t : ℝ => ((K 0 (Real.toNNReal t)) 0).toReal) =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      rw [hzero (Real.toNNReal t)]
      simp [PMF.pure_apply]
    rw [hfun]
    have hc :
        HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0
          (Set.Ici 0) 0 :=
      hasDerivWithinAt_const (c := (1 : ℝ))
        (x := (0 : ℝ)) (s := Set.Ici 0)
    simpa only [Nat.cast_zero, mul_zero, neg_zero] using hc
  · exact Kyprianou.Ch01.reverseLampertiNonexplosivePositiveDiagonalGenerator
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation y hy
