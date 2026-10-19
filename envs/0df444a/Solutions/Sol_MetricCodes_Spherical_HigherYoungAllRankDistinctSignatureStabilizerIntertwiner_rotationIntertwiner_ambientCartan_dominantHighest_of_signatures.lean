-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.rotationIntertwiner_ambientCartan_dominantHighest_of_signatures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/f657e57d-38c6-49b9-9ede-feae749d1a53

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_complexRotation_eigen_of_signatures

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
    (i : Fin (r + 1)) :
    ambientCartan hn i
        (youngIntertwinerHighestPolynomial hn mu nu hdom A) =
      ((2 * mu i : ℕ) : ℂ) •
        youngIntertwinerHighestPolynomial hn mu nu hdom A := by
  unfold youngIntertwinerHighestPolynomial
  rw [ambientCartan_eq_twice_I_complexRotation]
  change
    ((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i)
        (youngComplexPair nu
          (A (dominantHighestRealVector hn mu hdom))
          (A (dominantHighestImaginaryVector hn mu hdom))) = _
  apply rotationIntertwiner_complexRotation_eigen_of_signatures
    mu nu A hcomm (oddCoordinate hn i) (evenCoordinate hn i)
    ((2 : ℂ) * Complex.I) ((2 * mu i : ℕ) : ℂ)
    (dominantHighestRealVector hn mu hdom)
    (dominantHighestImaginaryVector hn mu hdom)
  rw [youngComplexPair_dominantHighest]
  change
    (((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i))
        (dominantHighestWeightWitness hn mu hdom).polynomial = _
  rw [← ambientCartan_eq_twice_I_complexRotation]
  exact ambientCartan_dominantHighestWeightWitness hn mu hdom i
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
