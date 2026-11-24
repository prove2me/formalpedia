-- Prove2me | solution 1 for GlobalTheory.EvenCubicNorm.eq_zero_of_even_cubic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:41.765031+00:00
-- url     : https://prove2.me/submissions/c4cc5c5f-84f9-4212-8997-c0b77c1af394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.EvenCubicNorm
open Finset
namespace GlobalTheory.EvenCubicNorm
theorem _root_.solution {ι X G : Type*} [AddCommGroup X] [AddCommGroup G]
    (b : Module.Basis ι ℤ X) (f : X → G) (hev : ∀ a, f (-a) = f a)
    (hcub : ∀ a a' c, f (a + a' + c) + f a + f a' + f c = f (a + a') + f (a + c) + f (a' + c))
    (h1 : ∀ i, f (b i) = 0) (h2 : ∀ i j, i ≠ j → f (b i + b j) = 0) : ∀ a, f a = 0 := by
  have hext : ∀ g : X →+ G, (∀ i, g (b i) = 0) → ∀ a, g a = 0 := by
    intro g hg a
    have : g.toIntLinearMap = 0 := b.ext (fun i => by simpa using hg i)
    simpa using LinearMap.congr_fun this a
  have h0 : f 0 = 0 := by simpa using hcub 0 0 0
  let B : X → X →+ G := fun c =>
    { toFun := fun a => f (a + c) - f a - f c
      map_zero' := by simp [h0]
      map_add' := by
        intro a a'
        have h := hcub a a' c
        have e : f (a + a' + c) - f (a + a') - f c - (f (a + c) - f a - f c + (f (a' + c) - f a' - f c))
            = (f (a + a' + c) + f a + f a' + f c) - (f (a + a') + f (a + c) + f (a' + c)) := by abel
        rw [← sub_eq_zero, e, h, sub_self] }
  have hBapp : ∀ c a, B c a = f (a + c) - f a - f c := fun _ _ => rfl
  have hdiag : ∀ i, B (b i) (b i) = 0 := by
    intro i
    have h := (B (b i)).map_add (b i) (-(b i))
    rw [add_neg_cancel, map_zero, hBapp (b i) (-(b i)), neg_add_cancel, hev, h0, h1] at h
    simpa using h.symm
  have hA : ∀ j a, B (b j) a = 0 := by
    intro j
    apply hext
    intro i
    by_cases hij : i = j
    · subst hij; exact hdiag i
    · rw [hBapp, h2 i j hij, h1, h1]; simp
  have hAll : ∀ a c, B c a = 0 := by
    intro a c
    have h := hext (B a) (fun j => by rw [hBapp, add_comm (b j) a, ← hA j a, hBapp]; abel) c
    rw [hBapp] at h ⊢
    rw [add_comm c a] at h
    rw [← h]; abel
  let F : X →+ G :=
    { toFun := f
      map_zero' := h0
      map_add' := by
        intro a c
        have h := hAll a c
        rw [hBapp, sub_sub, sub_eq_zero] at h
        exact h }
  intro a
  exact hext F h1 a
end GlobalTheory.EvenCubicNorm
