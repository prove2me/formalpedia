-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing.gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/93655025-4eed-4ca3-b30c-ae2aa2d7068c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidRowCharacteristicMinorVanishing_gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode

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
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hzero : gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (row.succ, true) = 0) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 := by
  rw [gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode
    lam mu h hgram hfinite row hbad p q, hzero, mul_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
