-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates.herm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:18.178865+00:00
-- url     : https://prove2.me/submissions/868dd0f8-788b-4a7a-bb85-35c2ebb75843

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ActionCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
namespace GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
theorem _root_.solution {P Q : ℕ} (x : Wsp P Q) : herm x x = (qf x : ℂ) := by
  have term : ∀ j, sgn j * x j * (starRingEnd ℂ) (x j) =
      (((sgn j).re * Complex.normSq (x j) : ℝ) : ℂ) := by
    intro j
    rw [mul_assoc, Complex.mul_conj]
    rcases j with j | j <;> simp [sgn]
  unfold qf herm
  simp_rw [term]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
end GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
