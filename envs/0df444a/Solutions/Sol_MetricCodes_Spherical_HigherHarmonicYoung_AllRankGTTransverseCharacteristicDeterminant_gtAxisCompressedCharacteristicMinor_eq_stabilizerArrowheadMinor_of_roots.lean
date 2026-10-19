-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.gtAxisCompressedCharacteristicMinor_eq_stabilizerArrowheadMinor_of_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/1069d494-6823-4bf3-883c-26a3fe7c0d18

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAxisCompressedCharacteristicMinor_gtAxisCompressedCharacteristicMinor_degree_lt
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_gtAxisCompressedCharacteristicMinor_coeff_card_pred
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_gtStabilizerArrowheadNode_injective_of_interlacing

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ∀ j : Unit ⊕ (Fin (r + 1) × Bool),
      (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) j) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        gtStabilizerArrowheadMinor
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  unfold gtStabilizerArrowheadMinor
  apply polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    (gtStabilizerArrowheadNode
      (wallShift (n + 1) (r + 1))
      (stabilizerShift (n + 1) mu))
    (gtStabilizerArrowheadNode_injective_of_interlacing hfinite)
  · have hdegree := gtAxisCompressedCharacteristicMinor_degree_lt
      lam mu h hgram hfinite p q
    convert hdegree using 1 <;>
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool] <;> push_cast <;> ring
  · convert gtAxisCompressedCharacteristicMinor_coeff_card_pred
      lam mu h hgram hfinite p q using 2 <;>
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool] <;> omega
  · exact hroot
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
