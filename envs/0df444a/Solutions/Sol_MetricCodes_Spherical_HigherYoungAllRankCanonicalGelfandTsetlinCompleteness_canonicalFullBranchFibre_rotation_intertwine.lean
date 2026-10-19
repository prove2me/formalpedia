-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranchFibre_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/d2f1db88-5a91-4434-9aa7-496e5c123cf5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine

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
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) (a b : Fin n) :
    (canonicalFullBranchFibre lam hn mu).toLinearMap.comp
        (youngAmbientRotation (fullBranchSignature mu) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalFullBranchFibre lam hn mu).toLinearMap := by
  let h := fullBranchSignature_interlaces_appendZeroWeight lam mu
  let hgram : PositiveGelfandTsetlinFischerGram (n := n)
      (appendZeroWeight lam) (fullBranchSignature mu) h :=
    positiveGelfandTsetlinFischerGram (by omega)
      (appendZeroWeight lam) (fullBranchSignature mu) h
  let B := canonicalGelfandTsetlinFibre
    (appendZeroWeight lam) (fullBranchSignature mu) h hgram
  let Z := (appendZeroRowIsometryEquiv
    (n := n + 1) lam).symm.toLinearIsometry
  have hB := canonicalGelfandTsetlinFibre_rotation_intertwine
    (appendZeroWeight lam) (fullBranchSignature mu) h hgram a b
  have hZ := appendZeroRowIsometryEquiv_symm_rotation_intertwine
    lam a.castSucc b.castSucc
  apply LinearMap.ext
  intro p
  change Z (B (youngAmbientRotation (fullBranchSignature mu) a b p)) =
    youngAmbientRotation lam a.castSucc b.castSucc (Z (B p))
  have hBp := LinearMap.congr_fun hB p
  have hZp := LinearMap.congr_fun hZ (B p)
  exact (congrArg Z hBp).trans hZp
end MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
