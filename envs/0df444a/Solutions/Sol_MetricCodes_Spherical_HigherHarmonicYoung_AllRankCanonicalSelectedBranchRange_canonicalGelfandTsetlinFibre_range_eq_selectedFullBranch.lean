-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange.canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/7985fd24-0f5f-4fe3-a05b-05b4a5bdb4c9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_ThreeRowYoungBranching_finrank_harmonicYoung_appendZero_eq
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankBranching_fullBranchOfInterlaces_signature_eq_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranchFibre_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_finrank_sum_allRank
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGTFullCrossOrthogonality_canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_orthogonalBranch_range_eq_of_cross_orthogonal

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
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    LinearMap.range (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap =
      LinearMap.range
        (canonicalFullBranchFibre lam hn
          (fullBranchOfInterlaces mu h)).toLinearMap := by
  apply orthogonalBranch_range_eq_of_cross_orthogonal
    (canonicalFullBranchFibre lam hn)
    (canonicalFullBranchFibre_orthogonal lam hn)
    (canonicalFullBranch_finrank_sum_allRank lam hn hdom)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (fullBranchOfInterlaces mu h)
  · intro nu hne p q
    exact canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
      lam mu h hn hgram nu hne p q
  · rw [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu h]
    exact (finrank_harmonicYoung_appendZero_eq mu).symm
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
