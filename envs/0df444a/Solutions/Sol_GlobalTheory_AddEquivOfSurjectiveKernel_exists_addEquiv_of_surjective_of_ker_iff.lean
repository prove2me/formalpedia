-- Prove2me | solution 1 for GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:19.301931+00:00
-- url     : https://prove2.me/submissions/e1214ec6-b046-4f99-91e0-e34ac9e6a37b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AddEquivOfSurjectiveKernel
universe u_1 u_2 u_3
namespace GlobalTheory.AddEquivOfSurjectiveKernel
theorem _root_.solution {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have key : ∀ a b : A, f a = f b ↔ g a = g b := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, h, map_sub, sub_eq_zero]
  choose s hs using hf
  choose t ht using hg
  have h1 : ∀ a, g (s (f a)) = g a := fun a => (key _ _).1 (hs _)
  have h2 : ∀ a, f (t (g a)) = f a := fun a => (key _ _).2 (ht _)
  refine ⟨{ toFun := fun b => g (s b)
            invFun := fun c => f (t c)
            left_inv := fun b => by
              show f (t (g (s b))) = b
              rw [h2, hs]
            right_inv := fun c => by
              show g (s (f (t c))) = c
              rw [h1, ht]
            map_add' := fun x y => by
              show g (s (x + y)) = g (s x) + g (s y)
              rw [← map_add, ← key, map_add, hs, hs, hs] }, fun a => h1 a⟩
end GlobalTheory.AddEquivOfSurjectiveKernel
