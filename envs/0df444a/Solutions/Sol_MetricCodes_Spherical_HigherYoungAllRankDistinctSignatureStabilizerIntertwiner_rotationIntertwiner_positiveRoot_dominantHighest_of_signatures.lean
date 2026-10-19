-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.rotationIntertwiner_positiveRoot_dominantHighest_of_signatures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/8e799d13-611b-458a-8da5-8f3c534f50c8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientPositiveRoot_dominantHighestWeightWitness
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientSumPositiveRoot_dominantHighestWeightWitness
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientShortPositiveRoot_dominantHighestWeightWitness
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_ambientPositiveRoot_zero_of_signatures
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_ambientSumPositiveRoot_zero_of_signatures
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_ambientShortPositiveRoot_zero_of_signatures

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
    (mu nu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (α : OrthogonalPositiveRoot r n) :
    orthogonalPositiveRootDerivation hn α
      (youngIntertwinerHighestPolynomial hn mu nu hdom A) = 0 := by
  cases α with
  | difference i j hij =>
      apply rotationIntertwiner_ambientPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i j
      rw [youngComplexPair_dominantHighest]
      exact ambientPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i j hij
  | sum i j hij =>
      apply rotationIntertwiner_ambientSumPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i j
      rw [youngComplexPair_dominantHighest]
      exact ambientSumPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i j
  | short i t ht =>
      apply rotationIntertwiner_ambientShortPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i t
      rw [youngComplexPair_dominantHighest]
      exact ambientShortPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i t ht
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
