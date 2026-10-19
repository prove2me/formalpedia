-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing.gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/1df48809-857d-4a95-a5d5-0ba2133ef926

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAxisCompressedCharacteristicMinor_gtAxisCompressedCharacteristicMinor_eval_signedNode
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidRowCharacteristicMinorVanishing_not_interlaces_raiseWeight_iff_upperWall
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidRowCharacteristicMinorVanishing_negativeStabilizerNode_eq_negativeAmbient_of_upperWall

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
set_option maxHeartbeats 2400000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1)) (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, false))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (signedNode (ambientShift (n + 1) lam)
            (row.castSucc, false)) *
        gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
          (row.castSucc, false) := by
  rw [negativeStabilizerNode_eq_negativeAmbient_of_upperWall lam mu row
    ((not_interlaces_raiseWeight_iff_upperWall lam mu h row).mp hbad)]
  exact gtAxisCompressedCharacteristicMinor_eval_signedNode
    lam mu h hgram hfinite p q (row.castSucc, false)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
