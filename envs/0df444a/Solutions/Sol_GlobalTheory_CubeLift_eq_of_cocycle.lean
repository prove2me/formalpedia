-- Prove2me | solution 1 for GlobalTheory.CubeLift.eq_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:21.979637+00:00
-- url     : https://prove2.me/submissions/7236c2b1-b6a3-452f-89b8-f90f26f1a0b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_fst
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_inr

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
theorem _root_.solution (u : A[X × X × W]) (a b : X →+ Y) (w : W →+ Y)
    (h : ∀ (a b c : X →+ X × Y) (w : W →+ X × Y), mv ((a + b).coprod (c.coprod w)) u + mv (a.coprod (b.coprod w)) u =
      mv (a.coprod ((b + c).coprod w)) u + mv (b.coprod (c.coprod w)) u) :
    mv (b.coprod w) (avg u) + mv (a.coprod w) (avg u) =
      mv ((a + b).coprod w) (avg u) + mv (a.coprod (b.coprod w)) u := by
  have := congrArg avg (h (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b)
    ((AddMonoidHom.inr X Y).comp w))
  rw [map_add, map_add, avg_mv_fst _ (b.coprod w) (by simp) (by simp),
    avg_mv_fst _ (a.coprod w) (by simp) (by simp), avg_mv_fst _ ((a + b).coprod w) (by simp) (by simp),
    avg_mv_inr _ (a.coprod (b.coprod w)) (by simp)] at this
  exact this
end GlobalTheory.CubeLift
