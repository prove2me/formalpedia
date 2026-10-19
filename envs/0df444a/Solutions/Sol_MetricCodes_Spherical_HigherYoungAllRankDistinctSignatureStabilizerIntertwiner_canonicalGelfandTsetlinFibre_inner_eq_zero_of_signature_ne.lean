-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/daa4f964-e7b2-47e1-b004-42bf119ae50c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_youngRotationIntertwiner_eq_zero_of_signature_ne
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_canonicalGelfandTsetlinFibre_crossGram_rotation_intertwine

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
    {r n : ℕ} (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu) (hnu : Interlaces lam nu)
    (hmuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu hmu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hne : mu ≠ nu)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) nu) :
    ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
      canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ = 0 := by
  let A :=
    (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
      (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap
  have hzero : A = 0 :=
    youngRotationIntertwiner_eq_zero_of_signature_ne hstable mu nu
      (interlaces_antitone_stabilizer hmu) hne A
      (canonicalGelfandTsetlinFibre_crossGram_rotation_intertwine
        lam mu nu hmu hnu hmuGram hnuGram)
  calc
    ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
      canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ =
      ⟪A p, q⟫_ℝ := by
        change
          ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
            canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ =
          ⟪(canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint
            (canonicalGelfandTsetlinFibre lam mu hmu hmuGram p), q⟫_ℝ
        exact (LinearMap.adjoint_inner_left
          (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap
          q (canonicalGelfandTsetlinFibre lam mu hmu hmuGram p)).symm
    _ = 0 := by
      rw [hzero, LinearMap.zero_apply, young_inner_eq_polynomialInner]
      rw [SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
