-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_vectorFieldContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:12:22.302938+00:00
-- url     : https://prove2.me/submissions/50dda3ea-38fe-4d63-8f8f-a9892b3267c2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_positive
import Theorems.Thm_Kyprianou_Ch01_branchingMechanism_continuousOn_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

/-- Time-continuous positive cumulants compose continuously with the branching mechanism. -/
theorem solution
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q)
    (hUcont : ContinuousOn
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (Set.Ici 0)) :
    Continuous
      (fun s : ℝ => branchingMechanism rate offspring
        (branchingU law (Real.toNNReal s) q)) := by
  let f : ℝ → ℝ := fun s => branchingU law (Real.toNNReal s) q
  have hUleft : ContinuousOn f (Iic (0 : ℝ)) := by
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => branchingU law 0 q) (Iic (0 : ℝ))).congr
    intro s hs
    dsimp [f]
    rw [Real.toNNReal_of_nonpos hs]
  have hUall : Continuous f := by
    have hu := hUcont.union_of_isClosed hUleft isClosed_Ici isClosed_Iic
    simpa only [Set.Ici_union_Iic, continuousOn_univ] using hu
  have hposU (s : ℝ) : f s ∈ Ioi (0 : ℝ) := by
    change 0 < branchingU law (Real.toNNReal s) q
    exact Kyprianou.Ch01.branchingU_positive law hpositive
      (Real.toNNReal s) q hq
  have hmechanism :
      ContinuousOn (branchingMechanism rate offspring) (Ioi (0 : ℝ)) :=
    Kyprianou.Ch01.branchingMechanism_continuousOn_pos rate offspring
  have hcomp :=
    hmechanism.comp (hUall.continuousOn) (fun s (_ : s ∈ Set.univ) => hposU s)
  simpa only [continuousOn_univ, Function.comp_def, f] using hcomp
