-- Prove2me | solution 1 for GlobalTheory.JR.HaarExist.continuousStar_of_norm_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:54.127528+00:00
-- url     : https://prove2.me/submissions/5fd8df85-0db2-4512-a072-7503422d9df9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HaarExist
variable (r : ℕ)
namespace GlobalTheory.JR.HaarExist
theorem _root_.solution (E : Type) [NormedField E] [StarRing E] (h : ∀ y : E, ‖star y‖ = ‖y‖) :
    ContinuousStar E :=
  ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) h).continuous⟩
end GlobalTheory.JR.HaarExist
