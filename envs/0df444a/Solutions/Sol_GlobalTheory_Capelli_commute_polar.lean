-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_polar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:20.889309+00:00
-- url     : https://prove2.me/submissions/d365a508-2508-4db0-a49d-6c11d58472bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_lie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}
namespace GlobalTheory.Capelli
theorem _root_.solution {u v w s : σ} (h₁ : v ≠ w) (h₂ : s ≠ u) :
    Commute (polar K u v) (polar K w s) := by
  classical
  have := polar_lie (K := K) u v w s
  rw [if_neg h₁, if_neg h₂, sub_zero] at this
  exact sub_eq_zero.mp this
end GlobalTheory.Capelli
