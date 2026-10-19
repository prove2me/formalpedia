-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLowerCrossGram_eq_zero_of_ne_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/ebfdfa93-1715-44ed-8a30-6ae6a4d948d2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_BranchingDimension_fullBranchSignature_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankBranching_fullBranchOfInterlaces_signature_eq_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_youngRotationIntertwiner_eq_zero_of_signature_ne
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankSelectedBranchSignature_fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram_canonicalBranchProjectedLowerCrossGram_rotation_intertwine

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
    (hne : nu ≠ fullBranchOfInterlaces mu hlow) :
    canonicalBranchProjectedLowerCrossGram
      low high mu hlow hhigh hdeg row hn nu = 0 := by
  have hsignature : appendZeroWeight mu ≠ fullBranchSignature nu :=
    Ne.symm
      ((fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
        mu hlow nu).mp hne)
  have hdom : Antitone (appendZeroWeight mu) := by
    have h := fullBranchSignature_antitone
      (fullBranchOfInterlaces mu hlow)
    rwa [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hlow] at h
  exact youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega) (appendZeroWeight mu) (fullBranchSignature nu)
    hdom hsignature
    (canonicalBranchProjectedLowerCrossGram
      low high mu hlow hhigh hdeg row hn nu)
    (canonicalBranchProjectedLowerCrossGram_rotation_intertwine
      low high mu hlow hhigh hdeg row hn nu)
end MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
