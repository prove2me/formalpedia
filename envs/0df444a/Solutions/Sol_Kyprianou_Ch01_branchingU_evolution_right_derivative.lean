-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_evolution_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:51:53.72326+00:00
-- url     : https://prove2.me/submissions/daea329c-f853-4e3f-941b-29bf64a63419

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_shift_right_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Transport the already-proved shifted right derivative to the natural time coordinate. -/
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
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Ici (t : ℝ)) (t : ℝ) := by
  have hshift := Kyprianou.Ch01.branchingU_shift_right_derivative
    law rate offspring hbranch hsemigroup hinit hpositive hgenerator q hq t
  have hinner : HasDerivWithinAt
      (fun s : ℝ => s - (t : ℝ)) 1
      (Set.Ici (t : ℝ)) (t : ℝ) := by
    simpa using ((hasDerivAt_id (t : ℝ)).sub_const (t : ℝ)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun s : ℝ => s - (t : ℝ))
      (Set.Ici (t : ℝ)) (Set.Ici 0) := by
    intro s hs
    exact sub_nonneg.mpr (Set.mem_Ici.mp hs)
  have hcomp := hshift.comp_of_eq (t : ℝ) hinner hmaps (by ring)
  have hcomp' : HasDerivWithinAt
      (fun s : ℝ => branchingU law (t + Real.toNNReal (s - (t : ℝ))) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Ici (t : ℝ)) (t : ℝ) := by
    simpa only [Function.comp_def, mul_one] using hcomp
  apply hcomp'.congr_of_eventuallyEq_of_mem ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have ht0 : (0 : ℝ) ≤ t := t.property
  have hs0 : (0 : ℝ) ≤ s := le_trans ht0 hs
  have hst : (0 : ℝ) ≤ s - (t : ℝ) := sub_nonneg.mpr hs
  have heq : t + Real.toNNReal (s - (t : ℝ)) = Real.toNNReal s := by
    apply NNReal.coe_injective
    simp [Real.coe_toNNReal, max_eq_left hst, max_eq_left hs0]
  simpa [heq]
