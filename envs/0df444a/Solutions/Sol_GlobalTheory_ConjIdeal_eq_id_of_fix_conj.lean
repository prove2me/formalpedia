-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.eq_id_of_fix_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:21:00.252627+00:00
-- url     : https://prove2.me/submissions/234f165b-89c7-4cb2-8bb4-ab86b98cf0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_eq_id_of_fix_conj_mul

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
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [AddCommGroup N] [Module O N]
    [AddCommGroup A] (hN : ∀ x : N, M • x = 0)
    (e : N → N → A) (e_add : ∀ x x' y, e (x + x') y = e x y + e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 0) → x = 0)
    (e_adj : ∀ (a : O) x y, e (a • x) y = e x (bar a • y))
    (θ : N →ₗ[O] N) (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) : θ = LinearMap.id := by
  have h := eq_id_of_fix_conj_mul bar I hsup M hIJ (N := Multiplicative N) (A := Multiplicative A)
    (fun x => hN x.toAdd)
    (fun a => AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom N a))
    (fun x => one_smul O x.toAdd) (fun a b x => add_smul a b x.toAdd)
    (fun a b x => mul_smul a b x.toAdd)
    (fun x y => Multiplicative.ofAdd (e x.toAdd y.toAdd)) (fun x x' y => e_add _ _ _)
    (fun x h => e_nondeg x.toAdd fun y => h (Multiplicative.ofAdd y)) (fun a x y => e_adj a _ _)
    (AddMonoidHom.toMultiplicative θ.toAddMonoidHom) (fun a x => θ.map_smul a x.toAdd)
    (fun x y => θ_iso _ _) (fun a ha y => θ_fix a ha _)
  ext x
  exact DFunLike.congr_fun h (Multiplicative.ofAdd x)
end GlobalTheory.ConjIdeal
