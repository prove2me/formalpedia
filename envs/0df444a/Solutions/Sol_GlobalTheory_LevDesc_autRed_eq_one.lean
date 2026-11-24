-- Prove2me | solution 1 for GlobalTheory.LevDesc.autRed_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:27.210025+00:00
-- url     : https://prove2.me/submissions/02227a3f-a61a-4e7c-a8ad-88f1dc91ec90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
namespace GlobalTheory.LevDesc
theorem _root_.solution (h : I ≤ J) (γ : QAut N I) : autRed h γ = 1 ↔ γ ∈ trivMod N I J := by
  refine ⟨fun e q => (qProj_eq_zero h _).1 ?_, fun e => LinearEquiv.ext fun q => ?_⟩
  · rw [map_sub, ← autRed_qProj, e]; exact sub_self _
  · obtain ⟨q, rfl⟩ := qProj_surjective h q
    rw [autRed_qProj]
    exact sub_eq_zero.1 ((map_sub (qProj h) _ _).symm.trans ((qProj_eq_zero h _).2 (e q)))
end GlobalTheory.LevDesc
