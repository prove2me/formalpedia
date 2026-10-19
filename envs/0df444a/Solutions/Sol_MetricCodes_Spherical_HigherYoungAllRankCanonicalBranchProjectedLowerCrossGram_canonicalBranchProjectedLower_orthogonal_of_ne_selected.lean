-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLower_orthogonal_of_ne_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/cddd5e80-63f9-4c45-9711-5664aab1e520

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram_canonicalBranchProjectedLowerCrossGram_eq_zero_of_ne_selected

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
    (nu : FullBranchWeight low)
    (hne : nu ≠ fullBranchOfInterlaces mu hlow)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪projectedCoordinateLower low high hdeg row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre high mu hhigh
          (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
            high mu hhigh) p),
      canonicalFullBranchFibre low hn nu q⟫_ℝ = 0 := by
  let F := (canonicalFullBranchFibre low hn nu).toLinearMap
  let H := (canonicalGelfandTsetlinFibre high mu hhigh
    (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
      high mu hhigh)).toLinearMap
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let D := projectedCoordinateLower low high hdeg row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
  have hzero := LinearMap.congr_fun
    (canonicalBranchProjectedLowerCrossGram_eq_zero_of_ne_selected
      low high mu hlow hhigh hdeg row hn nu hne) (Z p)
  change ⟪D (H p), F q⟫_ℝ = 0
  calc
    ⟪D (H p), F q⟫_ℝ = ⟪F.adjoint (D (H p)), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left F q (D (H p))).symm
    _ = 0 := by
      change ⟪F.adjoint (D (H p)), q⟫_ℝ = 0
      have hz : F.adjoint (D (H p)) = 0 := by
        change F.adjoint (D (H (Z.symm (Z p)))) = 0 at hzero
        simpa using hzero
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _
end MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
