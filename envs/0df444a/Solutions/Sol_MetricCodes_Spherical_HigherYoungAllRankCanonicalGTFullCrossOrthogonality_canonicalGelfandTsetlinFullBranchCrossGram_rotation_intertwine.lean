-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality.canonicalGelfandTsetlinFullBranchCrossGram_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/ad0e4d34-d9e2-4d6d-af16-f37f4caefd27

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranchFibre_rotation_intertwine

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
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (nu : FullBranchWeight lam) (a b : Fin n) :
    (canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu).comp
        (youngAmbientRotation (appendZeroWeight mu) a b) =
      (youngAmbientRotation (fullBranchSignature nu) a b).comp
        (canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu) := by
  let F := (canonicalFullBranchFibre lam hn nu).toLinearMap
  let G := (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  change (F.adjoint.comp (G.comp Z)).comp
      (youngAmbientRotation (appendZeroWeight mu) a b) =
    (youngAmbientRotation (fullBranchSignature nu) a b).comp
      (F.adjoint.comp (G.comp Z))
  apply crossGram_intertwines_of_skew F (G.comp Z)
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight mu) a b)
    (youngAmbientRotation lam a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (youngAmbientRotation_adjoint lam a.castSucc b.castSucc)
    (canonicalFullBranchFibre_rotation_intertwine lam hn nu a b)
  apply LinearMap.ext
  intro p
  change G (Z (youngAmbientRotation (appendZeroWeight mu) a b p)) =
    youngAmbientRotation lam a.castSucc b.castSucc (G (Z p))
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) p
  have hG := LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu h hgram a b) (Z p)
  exact (congrArg G hZ).trans hG
end MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
