-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.orthogonalBranchRows_eq_adjacentRowDifference_of_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/f37e02a8-1476-4ab9-8c21-de4d4c3b0a57

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankWeylBranchingRecurrence_branchLower_le_of_antitone

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hinterval : ∀ (L U : ℕ), L ≤ U → ∀ shift : ℤ,
      (∑ a : {k : Fin (U + 1) // L ≤ k.val},
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((a.val.val : ℤ) + shift)) =
        orthogonalCompleteSymmetricCoefficient n
            ((U : ℤ) + shift) -
          orthogonalCompleteSymmetricCoefficient n
            (((L : ℤ) - 1) + shift)) :
    (fun i j =>
      ∑ a : OrthogonalBranchCoordinate lam i,
        orthogonalBranchRow n lam i a j) =
      adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) := by
  classical
  funext i j
  have hsum (shift : ℤ) :
      (∑ a : OrthogonalBranchCoordinate lam i,
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((a.val.val : ℤ) + shift)) =
        orthogonalCompleteSymmetricCoefficient n
            ((lam i : ℤ) + shift) -
          orthogonalCompleteSymmetricCoefficient n
            (((branchLower lam i : ℤ) - 1) + shift) :=
    hinterval (branchLower lam i) (lam i)
      (branchLower_le_of_antitone lam hdom i) shift
  have hfirst (a : OrthogonalBranchCoordinate lam i) :
      (a.val.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) =
        (a.val.val : ℤ) + (-(i.val : ℤ) + (j.val : ℤ)) := by omega
  have hsecond (a : OrthogonalBranchCoordinate lam i) :
      (a.val.val : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2 =
        (a.val.val : ℤ) + (-(i.val : ℤ) - (j.val : ℤ) - 2) := by omega
  simp only [orthogonalBranchRow, Finset.sum_sub_distrib]
  simp_rw [hfirst, hsecond]
  rw [hsum (-(i.val : ℤ) + (j.val : ℤ)),
    hsum (-(i.val : ℤ) - (j.val : ℤ) - 2)]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [branchLower_last, adjacentRowDifference_last,
      orthogonalJacobiTrudiMatrix, Fin.val_last, Nat.cast_zero]
    have hj : j.val ≤ r := by have := j.isLt; omega
    have hneg₁ : ((0 : ℤ) - 1) + (-(r : ℤ) + (j.val : ℤ)) < 0 := by
      omega
    have hneg₂ :
        ((0 : ℤ) - 1) + (-(r : ℤ) - (j.val : ℤ) - 2) < 0 := by omega
    rw [orthogonalCompleteSymmetricCoefficient_of_neg n hneg₁,
      orthogonalCompleteSymmetricCoefficient_of_neg n hneg₂]
    simp
    ring_nf
  · simp only [branchLower_castSucc, adjacentRowDifference_castSucc,
      orthogonalJacobiTrudiMatrix]
    simp only [Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring_nf
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
