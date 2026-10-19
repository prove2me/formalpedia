-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.gtSelectedProjectorCompression_eq_plusProbability_of_minor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/e584a45f-15e7-44f7-8646-e289f8caf7f4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedProjectorCompression_gtSelectedProjectorCompression_inner_eq_plusProbability_of_minor

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
            (stabilizerShift (n + 1) mu)) :
    gtSelectedProjectorCompression lam mu h hgram row =
      plusProbability (n + 1) lam mu row • LinearMap.id := by
  apply LinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro p
  calc
    ⟪p, gtSelectedProjectorCompression lam mu h hgram row q⟫_ℝ =
        ⟪p, q⟫_ℝ * plusProbability (n + 1) lam mu row :=
      gtSelectedProjectorCompression_inner_eq_plusProbability_of_minor
        lam mu h hgram hfinite row p q (hminor p q)
    _ = ⟪p, (plusProbability (n + 1) lam mu row • LinearMap.id) q⟫_ℝ := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [young_inner_eq_polynomialInner mu p q,
        young_inner_eq_polynomialInner mu p
          (plusProbability (n + 1) lam mu row • q)]
      change
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n) (q : PolynomialSpace r n) *
              plusProbability (n + 1) lam mu row =
          SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n)
            (plusProbability (n + 1) lam mu row •
              (q : PolynomialSpace r n))
      rw [SpherePacking.Fischer.polynomialInner_smul_right]
      ring
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
