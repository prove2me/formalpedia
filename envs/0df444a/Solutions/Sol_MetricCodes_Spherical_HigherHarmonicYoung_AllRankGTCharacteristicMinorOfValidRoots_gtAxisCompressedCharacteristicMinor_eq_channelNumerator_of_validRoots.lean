-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots.gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_validRoots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/2d6dad2b-b979-4bc6-8da0-40dd35da79c1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalInvalidRowProjectorVanishing_gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalInvalidRowProjectorVanishing_gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots

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
open scoped InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hwall : (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0)
    (hnegative : ∀ row : Fin (r + 1),
      Interlaces lam (raiseWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, false))) = 0)
    (hpositive : ∀ row : Fin (r + 1), 0 < mu row →
      Interlaces lam (loweredInternalYoungWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, true))) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) := by
  apply gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots
    lam mu h hgram hfinite p q
  intro node
  cases node with
  | inl wall =>
      cases wall
      exact hwall
  | inr signed =>
      rcases signed with ⟨row, sign⟩
      cases sign with
      | false =>
          by_cases hvalid : Interlaces lam (raiseWeight mu row)
          · exact hnegative row hvalid
          · exact
              gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row hvalid p q
      | true =>
          by_cases hzero : mu row = 0
          · exact
              gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row (.inl hzero) p q
          · by_cases hvalid :
              Interlaces lam (loweredInternalYoungWeight mu row)
            · exact hpositive row (Nat.pos_of_ne_zero hzero) hvalid
            · exact
                gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                  lam mu h hgram hfinite hn row (.inr hvalid) p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
