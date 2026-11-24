-- Prove2me | solution 1 for GlobalTheory.ExpDivision.hasTemperateGrowth_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:40.254081+00:00
-- url     : https://prove2.me/submissions/371a17d6-0dd7-466d-aabc-ee2ad6028442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution {f : ℝ → ℂ} (hf : f.HasTemperateGrowth) :
    (deriv f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_deriv.1 hf.1).2, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  refine ⟨k, C, fun x => ?_⟩
  have := h x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this ⊢
  rwa [iteratedDeriv_succ'] at this
end GlobalTheory.ExpDivision
