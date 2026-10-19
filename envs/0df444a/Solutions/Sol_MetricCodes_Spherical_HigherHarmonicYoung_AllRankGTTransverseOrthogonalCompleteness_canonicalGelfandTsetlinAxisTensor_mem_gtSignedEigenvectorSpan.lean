-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness.canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/8fe105ae-263b-4881-934b-435a55cc1981

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAppendedPieriPhysicalAxisOrthogonality_paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalPaddedPieriSignedSpan_gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedPieriPhysicalAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p ∈
      gtSignedEigenvectorSpan (n := n + 1) lam := by
  have hdominant : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu h)).antitone_ambient
  have hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  apply gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    hfamily lam hdominant
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
  intro i hi q
  cases i with
  | inl row =>
      have hlast : row.val = Fin.last (r + 2) := by
        by_contra hne
        exact hi hne
      have hsource : Antitone
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))) := by
        simpa [hlast] using row.property
      have hrow : row = ⟨Fin.last (r + 2), hsource⟩ :=
        Subtype.ext hlast
      subst row
      exact paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
        lam mu h hgram hdominant hsource hn p q
  | inr row =>
      exact False.elim (hi trivial)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
