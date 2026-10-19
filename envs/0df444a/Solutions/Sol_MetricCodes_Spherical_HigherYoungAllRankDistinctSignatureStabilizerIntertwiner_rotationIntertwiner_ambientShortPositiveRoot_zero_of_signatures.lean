-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.rotationIntertwiner_ambientShortPositiveRoot_zero_of_signatures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/af2ca913-57c4-42c0-9b73-c59d5b61ec01

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_complexCombination_eigen_of_signatures

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
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
namespace MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (i : Fin (r + 1)) (t : Fin n)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ambientShortPositiveRoot hn i t
      (youngComplexPair mu p q) = 0) :
    ambientShortPositiveRoot hn i t
        (youngComplexPair nu (A p) (A q)) = 0 := by
  rw [ambientShortPositiveRoot_eq_complexRotations] at hroot ⊢
  change
    complexAmbientRotation (r := r) (evenCoordinate hn i) t
        (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn i) t
          (youngComplexPair nu (A p) (A q)) = 0
  have h := rotationIntertwiner_complexCombination_eigen_of_signatures
    mu nu A hcomm
    ![evenCoordinate hn i, oddCoordinate hn i]
    ![t, t] ![(1 : ℂ), Complex.I] 0 p q (by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        one_smul, zero_smul, add_zero, zero_add, Derivation.add_apply,
        Derivation.smul_apply] using hroot)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
    Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_smul, zero_smul, add_zero, zero_add] using h
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
