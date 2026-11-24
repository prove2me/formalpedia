-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.fix_torsion_of_fix_conj_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:14:07.980045+00:00
-- url     : https://prove2.me/submissions/ceb0f02a-eadc-4cb5-bdd0-83e2986612ed

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
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (R : G → G → A → Prop)
    (R_ex : ∀ x y, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (R_mul : ∀ x x' y c c', x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → R x y c → R x' y c' →
      R (x * x') y (c * c'))
    (R_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → R x y 1) → x = 1)
    (R_adj : ∀ a x y c, x ^ M = 1 → y ^ M = 1 → R x (act (bar a) y) c → R (act a x) y c)
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → R (θ x) (θ y) c)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  classical
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  let e : G → G → A := fun x y => if h : ∃ c, R x y c then h.choose else 1
  have he : ∀ x y, x ^ M = 1 → y ^ M = 1 → R x y (e x y) := fun x y hx hy => by
    have h : ∃ c, R x y c := (R_ex x y hx hy).exists
    simp only [e, dif_pos h]
    exact h.choose_spec
  have hu : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → e x y = c := fun x y c hx hy h =>
    (R_ex x y hx hy).unique (he x y hx hy) h
  refine fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e ?_ ?_ ?_ θ θ_act ?_
    θ_fix x hx
  · intro x x' y hx hx' hy
    exact hu _ _ _ (by rw [mul_pow, hx, hx', mul_one]) hy
      (R_mul _ _ _ _ _ hx hx' hy (he _ _ hx hy) (he _ _ hx' hy))
  · intro x hx h
    exact R_nondeg x hx fun y hy => h y hy ▸ he x y hx hy
  · intro a x y hx hy
    exact hu _ _ _ (tors _ _ hx) hy (R_adj _ _ _ _ hx hy (he _ _ hx (tors _ _ hy)))
  · intro x y hx hy
    exact hu _ _ _ (tors _ _ hx) (tors _ _ hy) (θ_iso _ _ _ hx hy (he _ _ hx hy))
end GlobalTheory.ConjIdeal
