-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranchFibre_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/14b82249-1aa6-4854-ba02-84c4c4ae008f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_fullBranchSignature_injective

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
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (p : HarmonicYoungSpace
      (n := n - 1) (fullBranchSignature mu))
    (q : HarmonicYoungSpace
      (n := n - 1) (fullBranchSignature nu)) :
    ⟪canonicalFullBranchFibre lam hn mu p,
      canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      let hmu := fullBranchSignature_interlaces_appendZeroWeight lam mu
      let hnu := fullBranchSignature_interlaces_appendZeroWeight lam nu
      let hmuGram : PositiveGelfandTsetlinFischerGram (n := n)
          (appendZeroWeight lam) (fullBranchSignature mu) hmu :=
        positiveGelfandTsetlinFischerGram (by omega)
          (appendZeroWeight lam) (fullBranchSignature mu) hmu
      let hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
          (appendZeroWeight lam) (fullBranchSignature nu) hnu :=
        positiveGelfandTsetlinFischerGram (by omega)
          (appendZeroWeight lam) (fullBranchSignature nu) hnu
      let Z := (appendZeroRowIsometryEquiv
        (n := n + 1) lam).symm.toLinearIsometry
      let Bmu := canonicalGelfandTsetlinFibre
        (appendZeroWeight lam) (fullBranchSignature mu) hmu hmuGram
      let Bnu := canonicalGelfandTsetlinFibre
        (appendZeroWeight lam) (fullBranchSignature nu) hnu hnuGram
      change ⟪Z (Bmu p), Z (Bnu q)⟫_ℝ = 0
      calc
        ⟪Z (Bmu p), Z (Bnu q)⟫_ℝ = ⟪Bmu p, Bnu q⟫_ℝ :=
          Z.inner_map_map (Bmu p) (Bnu q)
        _ = 0 := canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
          (by omega) (appendZeroWeight lam)
          (fullBranchSignature mu) (fullBranchSignature nu)
          hmu hnu hmuGram hnuGram
          (fun heq => hne (fullBranchSignature_injective lam heq)) p q
end MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
