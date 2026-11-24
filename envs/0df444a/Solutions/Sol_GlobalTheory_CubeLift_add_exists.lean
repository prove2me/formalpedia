-- Prove2me | solution 1 for GlobalTheory.CubeLift.add_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:18.654373+00:00
-- url     : https://prove2.me/submissions/3ff003b3-60a4-492f-ba7d-96a5e1c154b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_fst
import Theorems.Thm_GlobalTheory_CubeLift_avg_mv_inr
import Theorems.Thm_GlobalTheory_CubeLift_eq_of_cocycle

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
theorem _root_.solution (u : A[X × X × X])
    (s₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri b a c) u)
    (s₂ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri a c b) u)
    (co : ∀ (Y : Type) [AddCommGroup Y] (a b c d : X →+ Y),
      mv (tri (a + b) c d) u + mv (tri a b d) u = mv (tri a (b + c) d) u + mv (tri b c d) u) (a b c : X →+ Y) :
    mv (tri a b c) u = mv (a + b + c) (avg (avg u)) + mv a (avg (avg u)) + mv b (avg (avg u)) + mv c (avg (avg u)) -
      mv (a + b) (avg (avg u)) - mv (a + c) (avg (avg u)) - mv (b + c) (avg (avg u)) := by
  have e₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), _ := fun Y _ a b c =>
    eq_of_cocycle u a b c (co _)
  have e₂ : ∀ (Y : Type) [AddCommGroup Y] (a b : X →+ Y),
      mv (a.coprod b) (avg u) = mv (b.coprod a) (avg u) := fun Y _ a b => by
    have := congrArg avg (s₂ _ (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b))
    rwa [avg_mv_fst _ (a.coprod b) (by simp) (by simp), avg_mv_fst _ (b.coprod a) (by simp) (by simp)] at this
  have e₃ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y),
      mv ((a + b).coprod c) (avg u) + mv (a.coprod b) (avg u) =
        mv (a.coprod (b + c)) (avg u) + mv (b.coprod c) (avg u) := fun Y _ a b c => by
    have p := e₁ Y a b c
    have q := e₁ Y b c a
    have r : mv (tri a b c) u = mv (tri b c a) u := (s₁ Y a b c).trans (s₂ Y b a c)
    linear_combination q - p - r + e₂ Y a b - e₂ Y c a - e₂ Y a (b + c)
  have e₄ : ∀ a b : X →+ Y, mv b (avg (avg u)) + mv a (avg (avg u)) =
      mv (a + b) (avg (avg u)) + mv (a.coprod b) (avg u) := fun a b => by
    have := congrArg avg (e₃ _ (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b))
    rwa [map_add, map_add, avg_mv_fst _ b (by simp) (by simp), avg_mv_fst _ a (by simp) (by simp),
      avg_mv_fst _ (a + b) (by simp) (by simp), avg_mv_inr _ (a.coprod b) (by simp)] at this
  linear_combination -e₁ Y a b c - e₄ b c - e₄ a c + e₄ (a + b) c
end GlobalTheory.CubeLift
