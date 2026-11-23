-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.fix_torsion_of_fix_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:18.589797+00:00
-- url     : https://prove2.me/submissions/aa49ccb5-3708-4a3c-a76a-4a4b64deea26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar

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
    (e : G → G → A)
    (e_mul : ∀ x x' y, x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → e x y = 1) → x = 1)
    (e_adj : ∀ a x y, x ^ M = 1 → y ^ M = 1 → e (act a x) y = e x (act (bar a) y))
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, x ^ M = 1 → y ^ M = 1 → e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  have act_zero : ∀ y, act 0 y = 1 := fun y => by
    have := act_add 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.mp this
  have act_nat : ∀ (n : ℕ) y, act (n : O) y = y ^ n := fun n y => by
    induction n with
    | zero => simpa using act_zero y
    | succ n ih => rw [Nat.cast_succ, act_add, ih, act_one, pow_succ]
  have e_one : ∀ y, y ^ M = 1 → e 1 y = 1 := fun y hy => by
    have := e_mul 1 1 y (one_pow _) (one_pow _) hy
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have e_one' : ∀ y, y ^ M = 1 → e y 1 = 1 := fun y hy => by
    have := e_adj 0 y 1 hy (one_pow _)
    rw [act_zero, map_one, e_one 1 (one_pow _)] at this
    exact this.symm
  have split : ∀ w y, w ^ M = 1 → y ^ M = 1 → e w y = e w (act i y) * e w (act j y) := fun w y hw hy => by
    have h1 : w = act (bar.symm i) w * act (bar.symm j) w := by
      rw [← act_add, ← map_add, hij, map_one, act_one]
    conv_lhs => rw [h1]
    rw [e_mul _ _ _ (tors _ _ hw) (tors _ _ hw) hy, e_adj _ _ _ hw hy, e_adj _ _ _ hw hy,
      bar.apply_symm_apply, bar.apply_symm_apply]
  have hm : (θ x * x⁻¹) ^ M = 1 := by rw [mul_pow, tors θ x hx, inv_pow, hx, inv_one, mul_one]
  have hu : act i x ^ M = 1 := tors _ _ hx
  have hw : θ (act i x) = act i (θ x * x⁻¹) * act i x := by
    rw [← map_mul, θ_act _ _ hx, inv_mul_cancel_right]
  have key : act i (θ x * x⁻¹) = 1 := by
    refine e_nondeg _ (tors _ _ hm) fun y hy => ?_
    rw [split _ _ (tors _ _ hm) hy]
    have hA : e (act i (θ x * x⁻¹)) (act i y) = 1 := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (hIJ (Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem bar hi)))
      rw [e_adj _ _ _ hm (tors _ _ hy), ← act_mul, mul_comm (bar i), ← hc, act_mul, act_nat, hy,
        map_one, e_one' _ hm]
    have hB : e (act i (θ x * x⁻¹)) (act j y) = 1 := by
      have hv : act j y ^ M = 1 := tors _ _ hy
      have h := θ_iso _ _ hu hv
      rw [θ_fix j hj y hy, hw, e_mul _ _ _ (tors _ _ hm) hu hv] at h
      exact mul_eq_right.mp h
    rw [hA, hB, mul_one]
  have hx' : x = act i x * act j x := by rw [← act_add, hij, act_one]
  conv_lhs => rw [hx']
  rw [map_mul, hw, key, one_mul, θ_fix j hj x hx, ← hx']
end GlobalTheory.ConjIdeal
