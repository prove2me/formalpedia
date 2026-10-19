-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation.normalizedGTTransverseNegativeSector_mem_gtSignedEigenvectorSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/0a9be7e6-4a4b-42d2-ad98-dab2378c0911

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseAppendedChannelOrthogonality_paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseSectorSignedSpan_gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal

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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSectorSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise p ∈
        gtSignedEigenvectorSpan (n := n + 1) lam := by
  let hdom : Antitone (appendZeroWeight lam) :=
    appendZeroWeight_antitone lam hnu.antitone_ambient
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise p)
  intro hsource q
  change
    ⟪normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
      lam mu kappa row hnu hnuGram hfinite hraise hdom hsource hn p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
