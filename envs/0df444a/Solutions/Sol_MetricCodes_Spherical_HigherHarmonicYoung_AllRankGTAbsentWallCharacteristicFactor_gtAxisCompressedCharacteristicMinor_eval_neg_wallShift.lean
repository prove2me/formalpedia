-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor.gtAxisCompressedCharacteristicMinor_eval_neg_wallShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/467706ea-d6de-4e0f-9852-cec59f76d4f0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAxisCompressedCharacteristicMinor_gtAxisCompressedCharacteristicMinor_eval_signedNode
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentWallCharacteristicFactor_signedNode_last_false_eq_neg_wallShift

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
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (-(wallShift (n + 1) (r + 1))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (-(wallShift (n + 1) (r + 1))) *
        gtAxisCompressedSignedProjectorCoefficient
          lam mu h hgram p q (Fin.last (r + 1), false) := by
  simpa [signedNode_last_false_eq_neg_wallShift lam hlast] using
    gtAxisCompressedCharacteristicMinor_eval_signedNode
      lam mu h hgram hfinite p q (Fin.last (r + 1), false)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
