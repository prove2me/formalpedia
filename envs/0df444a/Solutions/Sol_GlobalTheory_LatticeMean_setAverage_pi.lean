-- Prove2me | solution 1 for GlobalTheory.LatticeMean.setAverage_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:49.429941+00:00
-- url     : https://prove2.me/submissions/8378f058-55aa-42b3-9b2b-0b48b6a04cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SetAverageProdFundamentalDomainPlaneLatticePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeMean
namespace GlobalTheory.LatticeMean
theorem _root_.solution (r : ℕ) (F : Set ℂ) (f : ℂ → ℝ) :
    ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) = (⨍ z in F, f z) ^ r := by
  rw [setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, mul_pow]
end GlobalTheory.LatticeMean
