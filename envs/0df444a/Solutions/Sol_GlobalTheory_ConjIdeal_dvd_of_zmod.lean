-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.dvd_of_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:20.676024+00:00
-- url     : https://prove2.me/submissions/1cdc6cde-17c0-4e8a-b319-adb13b0c0726

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_exists_eq_nsmul_of_forall_zmod
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
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : Y →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_zmod M _ fun t => h₂ t x hx y) y
end GlobalTheory.ConjIdeal
