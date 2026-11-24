-- Prove2me | solution 1 for GlobalTheory.newton_step_root_in_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:53.76654+00:00
-- url     : https://prove2.me/submissions/607fa051-36b0-478e-81a4-cc8eeae72378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  intro K _ _ g a ρ d hρ ha hle hlt
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a := by
    intro k
    rw [mul_comm]
    exact coeff_mul_X_sub_C
  have hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0 := by
    rw [mul_coeff_zero]
    simp

  have hM : 0 < ‖g.coeff d‖ * ρ ^ d := by
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    linarith
  have hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖ := by
    rw [norm_mul]
    have hp : 0 < ρ ^ (d + 1) := by positivity
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    have h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1) := by
      calc ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1)
          = (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ‖a‖ := by ring
        _ ≤ (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
        _ < (‖g.coeff d‖ * ρ ^ d) * ρ := mul_lt_mul_of_pos_right h hρ
        _ = ‖g.coeff d‖ * ρ ^ (d + 1) := by ring
    exact lt_of_mul_lt_mul_right h2 hp.le
  have htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖ := by
    rw [hcoef d, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'),
      norm_neg]
    exact max_eq_left hsmall.le
  have htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d) := by
    rw [htopn]; ring

  have key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤
      max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
    intro k
    rw [hcoef k]
    have h1 := hsub (g.coeff k) (g.coeff (k + 1) * a)
    rw [norm_mul] at h1
    have hp : 0 ≤ ρ ^ (k + 1) := by positivity
    have hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1) := by positivity
    calc ‖g.coeff k - g.coeff (k + 1) * a‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ (‖g.coeff (k + 1)‖ * ‖a‖) * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right h1 hp
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hp
      _ ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
          apply max_le_max
          · exact le_of_eq (by ring)
          · calc ‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)
                = (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ‖a‖ := by ring
              _ ≤ (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
              _ = ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) := by ring
  constructor
  · intro j
    rw [htop]
    cases j with
    | zero =>
      rw [hcoef0, norm_mul, norm_neg, pow_zero, mul_one]
      have h0 := hle 0
      rw [pow_zero, mul_one] at h0
      calc ‖a‖ * ‖g.coeff 0‖ ≤ ρ * ‖g.coeff 0‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ρ * (‖g.coeff d‖ * ρ ^ d) := mul_le_mul_of_nonneg_left h0 hρ.le
    | succ k =>
      exact (key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le)
        (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))
  · intro j hj
    rw [htop]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ)
      (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))
end GlobalTheory
