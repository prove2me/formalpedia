-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality.canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/ab73d1ff-c47f-4346-acec-db3b787c9195

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGTFullCrossOrthogonality_canonicalGelfandTsetlinFullBranchCrossGram_eq_zero_of_ne_selected

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
    (nu : FullBranchWeight lam)
    (hne : nu ≠ fullBranchOfInterlaces mu h)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪canonicalGelfandTsetlinFibre lam mu h hgram p,
      canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0 := by
  let F := (canonicalFullBranchFibre lam hn nu).toLinearMap
  let G := (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  have hzero := LinearMap.congr_fun
    (canonicalGelfandTsetlinFullBranchCrossGram_eq_zero_of_ne_selected
      lam mu h hn hgram nu hne) (Z p)
  change ⟪G p, F q⟫_ℝ = 0
  calc
    ⟪G p, F q⟫_ℝ = ⟪F.adjoint (G p), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left F q (G p)).symm
    _ = 0 := by
      have hz : F.adjoint (G p) = 0 := by
        change F.adjoint (G (Z.symm (Z p))) = 0 at hzero
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hzero
      rw [hz]
      exact inner_zero_left q
end MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
