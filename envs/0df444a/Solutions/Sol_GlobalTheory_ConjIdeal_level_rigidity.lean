-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.level_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:39:06.047384+00:00
-- url     : https://prove2.me/submissions/4b132252-70a8-4dac-a5ca-8b95e831d072

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_dvd_of_zmod
import Theorems.Thm_GlobalTheory_ConjIdeal_eq_id_of_fix_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
variable {O : Type*} [CommRing O]
namespace GlobalTheory.ConjIdeal
theorem _root_.solution (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) (hIJ : I * I.map bar = Ideal.span {(M : O)}) :
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] (d : X →ₗ[O] X),
      (∀ x ∈ I.map bar, ∀ y, ∃ z : X, d (x • y) = M • z) →
      (∀ t : X →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) →
      ∀ y, ∃ z : X, d y = M • z) ∧
    (∀ (N A : Type) [AddCommGroup N] [Module O N] [AddCommGroup A], (∀ x : N, M • x = 0) →
      ∀ e : N →+ N →+ A, (∀ x, e x = 0 → x = 0) → (∀ (a : O) x y, e (a • x) y = e x (bar a • y)) →
      ∀ θ : N ≃ₗ[O] N, (∀ x y, e (θ x) (θ y) = e x y) → (∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) →
      θ = LinearEquiv.refl O N) := by
  refine ⟨fun X _ _ _ d h₁ h₂ y => dvd_of_zmod bar hbar I hsup M d h₁ h₂ y,
    fun N A _ _ _ hN e hnd hadj θ hiso hfix => ?_⟩
  have h := eq_id_of_fix_conj bar I hsup M hIJ.le hN (fun x y => e x y)
    (fun x x' y => by simp) (fun x h => hnd x (AddMonoidHom.ext h)) hadj θ.toLinearMap hiso hfix
  exact LinearEquiv.toLinearMap_injective h
end GlobalTheory.ConjIdeal
