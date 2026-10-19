-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange.canonicalBoxReverseAxisRange_of_strongStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/de6b1c35-1973-442b-be95-4bbad5e137ff

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranchFibre_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_mem_range_of_orthogonal_allRank
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram_canonicalBranchProjectedLower_orthogonal_of_ne_selected
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch

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
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
theorem _root_.solution
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row) :
    CanonicalBoxReverseAxisRange
      a b hstable hgram low high row hrow := by
  let lam := boxSignature (m := m) a (n + 1) low
  let highLam := boxSignature (m := m) a (n + 1) high
  let mu := Weyl.flooredWeight b (n + 1)
  let hlow : Interlaces lam mu := boxSignature_interlaces a b hstable low
  let hhigh : Interlaces highLam mu :=
    boxSignature_interlaces a b hstable high
  let selected : FullBranchWeight lam := fullBranchOfInterlaces mu hlow
  have hdom : Antitone lam := hlow.antitone_ambient
  have hdeg : (∑ i, highLam i) = (∑ i, lam i) + 1 := by
    change (∑ i, boxSignature (m := m) a (n + 1) high i) =
      (∑ i, boxSignature (m := m) a (n + 1) low i) + 1
    rw [hrow]
    exact sum_raiseWeight (boxSignature (m := m) a (n + 1) low) row
  have hrange :
      LinearMap.range
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram low).toLinearMap =
        LinearMap.range
          (canonicalFullBranchFibre lam hnstrong selected).toLinearMap := by
    change LinearMap.range
        (canonicalGelfandTsetlinFibre lam mu hlow (hgram low)).toLinearMap = _
    exact canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu hlow hnstrong hdom (hgram low)
  intro p
  rw [hrange]
  apply canonicalFullBranch_mem_range_of_orthogonal_allRank
    lam hnstrong hdom
    (canonicalFullBranchFibre_orthogonal lam hnstrong) selected
  intro nu hnu q
  rw [boxAxis_succ_val_eq_basisFun]
  exact canonicalBranchProjectedLower_orthogonal_of_ne_selected
    lam highLam mu hlow hhigh hdeg row hnstrong nu hnu p q
end MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
