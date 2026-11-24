-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.eq_id_of_fix_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:21.480022+00:00
-- url     : https://prove2.me/submissions/c7cf870c-7d6b-45bc-a2f2-557b116f45df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_fix_torsion_of_fix_conj

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
theorem _root_.solution (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [CommGroup N] [CommGroup A]
    (hN : ∀ x : N, x ^ M = 1) (act : O → N →* N) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : N → N → A) (e_mul : ∀ x x' y, e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 1) → x = 1)
    (e_adj : ∀ a x y, e (act a x) y = e x (act (bar a) y))
    (θ : N →* N) (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (act a y) = act a y) : θ = MonoidHom.id N :=
  MonoidHom.ext fun x => fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e
    (fun x x' y _ _ _ => e_mul x x' y) (fun x _ h => e_nondeg x fun y => h y (hN y))
    (fun a x y _ _ => e_adj a x y) θ (fun a x _ => θ_act a x) (fun x y _ _ => θ_iso x y)
    (fun a ha y _ => θ_fix a ha y) x (hN x)
end GlobalTheory.ConjIdeal
