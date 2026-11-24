-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.dvd_of_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:10.008846+00:00
-- url     : https://prove2.me/submissions/0c4dc763-e9a3-4c2c-aef3-fd2261026f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_exists_eq_nsmul_of_forall_addChar
import Theorems.Thm_GlobalTheory_ConjIdeal_dvd_of_dvd_conj

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
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : AddChar Y C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 1) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_addChar hM hζ _ fun t ht => h₂ t ht x hx y) y
end GlobalTheory.ConjIdeal
