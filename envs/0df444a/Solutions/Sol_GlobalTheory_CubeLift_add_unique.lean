-- Prove2me | solution 1 for GlobalTheory.CubeLift.add_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:53.440186+00:00
-- url     : https://prove2.me/submissions/07fe083e-8906-4ebd-9e7c-d2401a93d3e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mv_id
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_inr
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_one

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
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (h : A[X]) (H : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y),
    mv (a + b + c) h + mv a h + mv b h + mv c h - mv (a + b) h - mv (a + c) h - mv (b + c) h = 0) : h = 0 := by
  have e₁ : ∀ (Y : Type) [AddCommGroup Y] (b c : X →+ Y), mv b h + mv c h = mv (b + c) h := fun Y _ b c => by
    have := congrArg avg (H _ (.inl X Y) ((AddMonoidHom.inr X Y).comp b) ((AddMonoidHom.inr X Y).comp c))
    simp only [map_add, map_sub, map_zero] at this
    rw [avg_mv_one _ (by simp), avg_mv_one _ (by simp), avg_mv_inr _ b (by simp), avg_mv_inr _ c (by simp),
      avg_mv_one _ (by simp), avg_mv_one _ (by simp), avg_mv_inr _ (b + c) (by simp)] at this
    linear_combination this
  have := congrArg avg (e₁ _ (.inl X X) (.inr X X))
  rw [map_add, avg_mv_one _ (by simp), avg_mv_inr _ (.id X) (by simp), avg_mv_one _ (by simp), mv_id] at this
  linear_combination this
end GlobalTheory.CubeLift
