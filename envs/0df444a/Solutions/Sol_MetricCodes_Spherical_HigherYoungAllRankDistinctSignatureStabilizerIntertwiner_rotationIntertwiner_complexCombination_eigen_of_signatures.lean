-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.rotationIntertwiner_complexCombination_eigen_of_signatures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/41319b52-5cd1-4878-992d-07332ec2b15a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    {r n k : ℕ} (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (a b : Fin k → Fin n) (c : Fin k → ℂ) (z : ℂ)
    (p q : HarmonicYoungSpace (n := n) mu)
    (heigen :
      (∑ i : Fin k,
        c i • complexAmbientRotation (r := r) (a i) (b i)
          (youngComplexPair mu p q)) =
        z • youngComplexPair mu p q) :
    (∑ i : Fin k,
      c i • complexAmbientRotation (r := r) (a i) (b i)
        (youngComplexPair nu (A p) (A q))) =
      z • youngComplexPair nu (A p) (A q) := by
  rw [complexRotationCombination_youngComplexPair,
    complex_smul_youngComplexPair] at heigen ⊢
  have hreal :
      (∑ i : Fin k,
        ((c i).re • youngAmbientRotation mu (a i) (b i) p -
          (c i).im • youngAmbientRotation mu (a i) (b i) q)) =
        z.re • p - z.im • q := by
    apply Subtype.ext
    simpa using congrArg polynomialRealPart heigen
  have himag :
      (∑ i : Fin k,
        ((c i).im • youngAmbientRotation mu (a i) (b i) p +
          (c i).re • youngAmbientRotation mu (a i) (b i) q)) =
        z.im • p + z.re • q := by
    apply Subtype.ext
    simpa using congrArg polynomialImaginaryPart heigen
  have hArot (i : Fin k) (v : HarmonicYoungSpace (n := n) mu) :
      A (youngAmbientRotation mu (a i) (b i) v) =
        youngAmbientRotation nu (a i) (b i) (A v) :=
    LinearMap.congr_fun (hcomm (a i) (b i)) v
  have hrealA := congrArg A hreal
  have himagA := congrArg A himag
  simp only [map_sum, map_sub, map_add, map_smul, hArot]
    at hrealA himagA
  exact congrArg₂ (youngComplexPair nu) hrealA himagA
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
