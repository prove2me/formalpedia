-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.gtSelectedPhysicalAxisCompression_fibre_eq_plusProbability_of_minor_and_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/7a8973f3-70ea-4ed3-ba0e-be3430697bb9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedProjectorCompression_gtSelectedProjectorCompression_eq_plusProbability_of_minor
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedProjectorCompression_gtSelectedProjectorCompression_eq_fibre_adjoint_physical_of_selected

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 2))
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (stabilizerShift (n + 1) mu))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector lam (row, true)
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) =
        gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p))
    (hrange : ∀ p : HarmonicYoungSpace (n := n) mu,
      gtSelectedPhysicalAxisCompression lam row
          (canonicalGelfandTsetlinFibre lam mu h hgram p) ∈
        LinearMap.range
          (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtSelectedPhysicalAxisCompression lam row
        (canonicalGelfandTsetlinFibre lam mu h hgram p) =
      plusProbability (n + 1) lam mu row •
        canonicalGelfandTsetlinFibre lam mu h hgram p := by
  let F := canonicalGelfandTsetlinFibre lam mu h hgram
  obtain ⟨q, hq⟩ := hrange p
  have hcompressed := LinearMap.congr_fun
    (gtSelectedProjectorCompression_eq_plusProbability_of_minor
      lam mu h hgram hfinite row hminor) p
  rw [gtSelectedProjectorCompression_eq_fibre_adjoint_physical_of_selected
    lam mu h hgram row hselected] at hcompressed
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hcompressed
  change F.adjoint (gtSelectedPhysicalAxisCompression lam row (F p)) =
    plusProbability (n + 1) lam mu row • p at hcompressed
  rw [← hq] at hcompressed
  have hleft := LinearMap.congr_fun F.adjoint_comp_self' q
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hleft
  rw [hleft] at hcompressed
  calc
    gtSelectedPhysicalAxisCompression lam row (F p) = F q := hq.symm
    _ = F (plusProbability (n + 1) lam mu row • p) := by
      rw [hcompressed]
    _ = plusProbability (n + 1) lam mu row • F p := F.map_smul _ _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
