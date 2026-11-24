-- Prove2me | solution 1 for GlobalTheory.pow_vacuum_fock_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:09.166258+00:00
-- url     : https://prove2.me/submissions/0fd5cefc-dab9-4669-bcb8-ca6fa8fd087b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowSubCreationVacuumFockBound
import Theorems.Thm_GlobalTheory_annihilation_pow_vacuum
import Theorems.Thm_GlobalTheory_pow_vacuum_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (T H : Type) [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H)
    (a c : Module.End ℂ T) (s : ℝ) (v : T) (hs : 0 ≤ s)
    (hadj : ∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y)))
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0) :
    (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧
      ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  have hc : ∀ w, a (c w) = c (a w) + (s : ℂ) • w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ T => f w) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [← h]; abel
  refine ⟨fun K hvK hcK k => (pow_vacuum_mem a c s v hcomm hv K hvK hcK k).1, ?_⟩
  have hcn : ∀ y, ‖Φ (c y)‖ ^ 2 = ‖Φ (a y)‖ ^ 2 + s * ‖Φ y‖ ^ 2 := by
    intro y
    have e : inner ℂ (Φ (c y)) (Φ (c y)) =
        inner ℂ (Φ (a y)) (Φ (a y)) + (s : ℂ) * inner ℂ (Φ y) (Φ y) := by
      rw [hadj, hc, map_add, map_smul, inner_add_right, inner_smul_right]
      congr 1
      rw [← inner_conj_symm (Φ y) (Φ (c (a y))), hadj]
      exact inner_conj_symm _ _
    simp only [inner_self_eq_norm_sq_to_K] at e
    apply Complex.ofReal_injective
    push_cast
    linear_combination e
  have hDn : ∀ y, ‖Φ ((c - a) y)‖ ^ 2 ≤ 2 * ‖Φ (c y)‖ ^ 2 + 2 * ‖Φ (a y)‖ ^ 2 := by
    intro y
    rw [LinearMap.sub_apply, map_sub]
    have h := norm_sub_le (Φ (c y)) (Φ (a y))
    have h2 : ‖Φ (c y) - Φ (a y)‖ ^ 2 ≤ (‖Φ (c y)‖ + ‖Φ (a y)‖) ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖Φ (c y)‖ - ‖Φ (a y)‖)]
  have hsm : ∀ k : ℕ, ‖Φ (a (((c - a) ^ (k + 1)) v))‖ =
      ((k : ℝ) + 1) * s * ‖Φ (((c - a) ^ k) v)‖ := by
    intro k
    rw [annihilation_pow_vacuum a c s v hcomm hv k, map_smul, norm_smul]
    congr 1
    have e : ((k : ℂ) + 1) * (s : ℂ) = ((((k : ℝ) + 1) * s : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) hs)]

  have main : ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial ∧
      ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 ≤
        ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      have h := hcn v
      rw [hv, map_zero, norm_zero] at h
      simp only [zero_add, pow_one, LinearMap.sub_apply, hv, sub_zero, Nat.factorial_one,
        Nat.cast_one, mul_one]
      rw [h]
      nlinarith [mul_nonneg hs (sq_nonneg ‖Φ v‖)]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      rw [pow_succ' (c - a) (k + 1), Module.End.mul_apply]
      have hA := mul_le_mul_of_nonneg_left h1
        (show (0 : ℝ) ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 by positivity)
      have hB := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 * s by linarith)
      calc ‖Φ ((c - a) (((c - a) ^ (k + 1)) v))‖ ^ 2
          ≤ 2 * ‖Φ (c (((c - a) ^ (k + 1)) v))‖ ^ 2
              + 2 * ‖Φ (a (((c - a) ^ (k + 1)) v))‖ ^ 2 := hDn _
        _ = 4 * (((k : ℝ) + 1) * s) ^ 2 * ‖Φ (((c - a) ^ k) v)‖ ^ 2
              + 2 * s * ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 := by
          rw [hcn, hsm]; ring
        _ ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 * (‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial)
              + 2 * s * (‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial) := add_le_add hA hB
        _ = ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1 + 1) * (k + 1 + 1).factorial := by
          rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]; push_cast; ring
  exact fun k => (main k).1
end GlobalTheory
