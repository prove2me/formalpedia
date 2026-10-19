-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLowerCrossGram_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/3592e2d9-3980-45c6-9fe9-83e631254d6a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranchFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTProjectedLowerRange_projectedCoordinateLower_fixedAxis_rotation_intertwine

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
theorem _root_.solution
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low) (a b : Fin n) :
    (canonicalBranchProjectedLowerCrossGram
      low high mu hlow hhigh hdeg row hn nu).comp
        (youngAmbientRotation (appendZeroWeight mu) a b) =
      (youngAmbientRotation (fullBranchSignature nu) a b).comp
        (canonicalBranchProjectedLowerCrossGram
          low high mu hlow hhigh hdeg row hn nu) := by
  let F := (canonicalFullBranchFibre low hn nu).toLinearMap
  let H := (canonicalGelfandTsetlinFibre high mu hhigh
    (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
      high mu hhigh)).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let D := projectedCoordinateLower low high hdeg row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
  change (F.adjoint.comp (D.comp (H.comp Z))).comp
      (youngAmbientRotation (appendZeroWeight mu) a b) =
    (youngAmbientRotation (fullBranchSignature nu) a b).comp
      (F.adjoint.comp (D.comp (H.comp Z)))
  apply crossGram_intertwines_of_skew F (D.comp (H.comp Z))
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight mu) a b)
    (youngAmbientRotation low a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (youngAmbientRotation_adjoint low a.castSucc b.castSucc)
    (canonicalFullBranchFibre_rotation_intertwine low hn nu a b)
  apply LinearMap.ext
  intro p
  change D (H (Z (youngAmbientRotation (appendZeroWeight mu) a b p))) =
    youngAmbientRotation low a.castSucc b.castSucc (D (H (Z p)))
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) p
  have hH := LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      high mu hhigh
      (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
        high mu hhigh) a b) (Z p)
  have hD := LinearMap.congr_fun
    (projectedCoordinateLower_fixedAxis_rotation_intertwine
      low high hdeg row a b) (H (Z p))
  exact (congrArg (fun q => D (H q)) hZ).trans
    ((congrArg D hH).trans hD)
end MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
