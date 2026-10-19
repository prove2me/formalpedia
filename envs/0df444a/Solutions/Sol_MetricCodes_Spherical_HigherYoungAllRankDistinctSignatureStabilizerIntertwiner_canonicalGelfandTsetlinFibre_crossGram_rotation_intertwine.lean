-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.canonicalGelfandTsetlinFibre_crossGram_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/f3e30d6b-bdee-4d93-9013-cb2a26828f3b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine

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
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu) (hnu : Interlaces lam nu)
    (hmuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu hmu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (((canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
        (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap).comp
          (youngAmbientRotation mu a b)) =
      (youngAmbientRotation nu a b).comp
        ((canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
          (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap) := by
  exact crossGram_intertwines_of_skew
    (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap
    (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap
    (youngAmbientRotation nu a b)
    (youngAmbientRotation mu a b)
    (youngAmbientRotation lam a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint nu a b)
    (youngAmbientRotation_adjoint lam a.castSucc b.castSucc)
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam nu hnu hnuGram a b)
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu hmu hmuGram a b)
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
