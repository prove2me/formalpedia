-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.riem_eq_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:50.000208+00:00
-- url     : https://prove2.me/submissions/ab16781a-dac3-4b0e-84e9-167c085489d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped Real ContDiff
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
theorem _root_.solution {g : ℕ} (x y : Fl g) : riem x y = x ⬝ᵥ (Matrix.J (Fin g) ℝ *ᵥ y) := by
  simp [riem, Matrix.J, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
