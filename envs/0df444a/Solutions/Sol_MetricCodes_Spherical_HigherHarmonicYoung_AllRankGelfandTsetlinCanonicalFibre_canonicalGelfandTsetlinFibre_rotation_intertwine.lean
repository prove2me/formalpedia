-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre.canonicalGelfandTsetlinFibre_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/84d9f30e-13c3-4e80-a491-33d96706e117

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranchRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentFibrePhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankGelfandTsetlinGramRotationCommutation
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungMovingFibres
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap := by
  apply LinearMap.ext
  intro p
  change
    (Real.sqrt (canonicalGelfandTsetlinFischerGram
      lam mu h hgram))⁻¹ •
        reverseInterlacingHarmonicBranch lam mu h
          (youngAmbientRotation mu a b p) =
      youngAmbientRotation lam a.castSucc b.castSucc
        ((Real.sqrt (canonicalGelfandTsetlinFischerGram
          lam mu h hgram))⁻¹ •
            reverseInterlacingHarmonicBranch lam mu h p)
  rw [map_smul]
  congr 1
  exact DFunLike.congr_fun
    (reverseInterlacingHarmonicBranch_rotation_intertwine lam mu h a b) p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
