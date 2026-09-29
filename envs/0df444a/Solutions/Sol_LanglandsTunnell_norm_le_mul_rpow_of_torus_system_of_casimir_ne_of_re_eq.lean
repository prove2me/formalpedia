-- Prove2me | solution 1 for LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12b6d096-131b-5332-949d-2639ec718c56

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq

set_option autoImplicit false

open scoped Real

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "norm_le_mul_rpow_near_zero_of_first_order_system_of_diag"
namespace AlphaAux
p2m_open "LanglandsTunnell"

open Finset

noncomputable def qR (n i : ℕ) : ℝ := (n : ℝ) - 2 * (i : ℝ)

noncomputable def G (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) : ℝ → ℂ :=
  if 2 * i = n ∨ n < i then (fun _ => 0) else f i

noncomputable def aC (n : ℕ) (lam lam' : ℂ) (i : ℕ) : ℂ :=
  if 2 * i = n then 1 else 1 - 2 * (lam - lam') / (qR n i : ℂ)

noncomputable def uC (n : ℕ) (κ : ℂ) (i : ℕ) : ℂ := -(4 * (Real.pi : ℂ) * Complex.I * κ) / (qR n i : ℂ)

noncomputable def vC (n : ℕ) (κ : ℂ) (i : ℕ) : ℂ :=
  -(4 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ)))) / (qR n i : ℂ)

noncomputable def αC (κ lam lam' : ℂ) : ℂ := -(2 * (Real.pi : ℂ) * Complex.I * κ) / (lam - lam')

noncomputable def βC (n : ℕ) (κ lam lam' : ℂ) (i : ℕ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ)))) / (lam - lam')

noncomputable def δ (j t : ℕ) : ℂ := if j = t then 1 else 0

noncomputable def χ (n t : ℕ) : ℂ := if 2 * t = n then 1 else 0

noncomputable def Bn (n : ℕ) (κ lam lam' : ℂ) (y : ℝ) (i j : ℕ) : ℂ :=
  if 2 * i = n then 0 else
    (y : ℂ) * (uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1)) +
    (y : ℂ) ^ 2 *
      (χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
        χ n (i - 1) * vC n κ i * (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1)))

theorem norm_δ_le (j t : ℕ) : ‖δ j t‖ ≤ 1 := by
  unfold δ; split_ifs <;> simp

theorem norm_χ_le (n t : ℕ) : ‖χ n t‖ ≤ 1 := by
  unfold χ; split_ifs <;> simp

theorem G_of_lt (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : n < i) : G n f i = fun _ => 0 := by
  unfold G; rw [if_pos (Or.inr h)]

theorem G_of_mid (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : 2 * i = n) : G n f i = fun _ => 0 := by
  unfold G; rw [if_pos (Or.inl h)]

theorem G_of_ne (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : ¬ 2 * i = n) (hi : i ≤ n) : G n f i = f i := by
  unfold G; rw [if_neg (by omega)]

theorem sum_delta (n : ℕ) (f : ℕ → ℝ → ℂ) (t : ℕ) (y : ℝ) :
    ∑ j ∈ range (n + 1), δ j t * G n f j y = G n f t y := by
  simp only [δ, boole_mul, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [G_of_lt n f t (by omega)]

theorem rowsum (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) (y : ℝ) (i : ℕ) (h : ¬ 2 * i = n) :
    ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y =
      (y : ℂ) * (uC n κ i * G n f (i + 1) y + vC n κ i * G n f (i - 1) y) +
      (y : ℂ) ^ 2 *
        (χ n (i + 1) * uC n κ i * (αC κ lam lam' * G n f (i + 2) y + βC n κ lam lam' (i + 1) * G n f i y) +
          χ n (i - 1) * vC n κ i *
            (αC κ lam lam' * G n f (i - 1 + 1) y + βC n κ lam lam' (i - 1) * G n f (i - 1 - 1) y)) := by
  simp only [Bn, if_neg h, add_mul, mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, sum_delta]

theorem rowsum_mid (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) (y : ℝ) (i : ℕ) (h : 2 * i = n) :
    ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y = 0 := by
  simp [Bn, h]

theorem sysN (n : ℕ) (Gf : ℕ → ℝ → ℂ) (a : ℕ → ℂ) (B : ℝ → ℕ → ℕ → ℂ) (c : ℝ)
    (ha : ∀ i, i ≤ n → 1 ≤ (a i).re)
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, i ≤ n → j ≤ n → ‖B y i j‖ ≤ c * y)
    (hG : ∀ i, i ≤ n → DifferentiableOn ℝ (Gf i) (Set.Ioi 0))
    (hrow : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, i ≤ n →
      (y : ℂ) * deriv (Gf i) y = a i * Gf i y + ∑ j ∈ range (n + 1), B y i j * Gf j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, i ≤ n → ‖Gf i y‖ ≤ C * y ^ (1 - ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag (n + 1)
    (fun i => a i) 1 c 1 one_pos (fun i => ha i (Nat.lt_succ_iff.mp i.isLt)) (fun y i j => B y i j)
    (fun y hy hy1 i j => by
      simpa using hB y hy hy1 i j (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt))
    (fun i => Gf i) (fun i => hG i (Nat.lt_succ_iff.mp i.isLt))
    (fun y hy hy1 i => by
      beta_reduce
      rw [Fin.sum_univ_eq_sum_range (fun j => B y i j * Gf j y) (n + 1)]
      exact hrow y hy hy1 i (Nat.lt_succ_iff.mp i.isLt)) ε hε
  exact ⟨C, fun y hy hy1 i hi => hC y hy hy1 ⟨i, Nat.lt_succ_iff.mpr hi⟩⟩

end LanglandsTunnell.AlphaAux

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "norm_le_mul_rpow_near_zero_of_first_order_system_of_diag"
namespace AlphaAux
p2m_open "LanglandsTunnell"

open Finset

def HSys (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) : Prop :=
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)

variable {n : ℕ} {κ lam lam' : ℂ} {f : ℕ → ℝ → ℂ}

theorem hstar (hsys : HSys n κ lam lam' f) (i : ℕ) (hi : i ≤ n) (y : ℝ) (hy : 0 < y) :
    2 * ((n : ℂ) - 2 * (i : ℂ)) * (y : ℂ) * deriv (f i) y +
        (4 * (lam - lam') - 2 * ((n : ℂ) - 2 * (i : ℂ))) * f i y +
      8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) *
        (κ * f (i + 1) y + (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ))) * f (i - 1) y) = 0 := by
  obtain ⟨E1, E2⟩ := (hsys ⟨i, Nat.lt_succ_iff.mpr hi⟩).2.2 y hy
  dsimp only at E1 E2
  linear_combination E1 - E2

theorem qR_cast (n i : ℕ) : ((qR n i : ℝ) : ℂ) = (n : ℂ) - 2 * (i : ℂ) := by
  simp [qR]

theorem q_ne_zero (i : ℕ) (h : ¬ 2 * i = n) : (n : ℂ) - 2 * (i : ℂ) ≠ 0 := by
  have h' : ((n : ℤ) - 2 * (i : ℤ)) ≠ 0 := by omega
  have h'' : (((n : ℤ) - 2 * (i : ℤ) : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr h'
  push_cast at h''
  exact h''

theorem rel (hsys : HSys n κ lam lam' f) (i : ℕ) (hi : i ≤ n) (h : ¬ 2 * i = n) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) * deriv (f i) y =
      aC n lam lam' i * f i y + (y : ℂ) * (uC n κ i * f (i + 1) y + vC n κ i * f (i - 1) y) := by
  have H := hstar hsys i hi y hy
  have hq0 := q_ne_zero (n := n) i h
  have hinv : ((n : ℂ) - 2 * (i : ℂ)) * ((n : ℂ) - 2 * (i : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hq0
  rw [aC, if_neg h, uC, vC, qR_cast]
  linear_combination ((2 : ℂ)⁻¹ * ((n : ℂ) - 2 * (i : ℂ))⁻¹) * H + (f i y - (y : ℂ) * deriv (f i) y) * hinv

theorem alg (hne : lam ≠ lam' ∨ Odd n) (hsys : HSys n κ lam lam' f) (j : ℕ) (hj : j ≤ n) (h : 2 * j = n)
    (y : ℝ) (hy : 0 < y) :
    f j y = (y : ℂ) * (αC κ lam lam' * f (j + 1) y + βC n κ lam lam' j * f (j - 1) y) := by
  have H := hstar hsys j hj y hy
  have hd : lam ≠ lam' := hne.resolve_right (by rintro ⟨k, hk⟩; omega)
  have hd' : lam - lam' ≠ 0 := sub_ne_zero.mpr hd
  have hdinv : (lam - lam') * (lam - lam')⁻¹ = 1 := mul_inv_cancel₀ hd'
  have hq : (n : ℂ) - 2 * (j : ℂ) = 0 := by
    have : (n : ℂ) = ((2 * j : ℕ) : ℂ) := by rw [h]
    rw [this]; push_cast; ring
  rw [αC, βC]
  linear_combination (4 : ℂ)⁻¹ * (lam - lam')⁻¹ * H - f j y * hdinv -
    (2 : ℂ)⁻¹ * (lam - lam')⁻¹ * ((y : ℂ) * deriv (f j) y - f j y) * hq

theorem f_eq (hne : lam ≠ lam' ∨ Odd n) (hfn : ∀ y : ℝ, f (n + 1) y = 0) (hsys : HSys n κ lam lam' f)
    (j : ℕ) (hj : j ≤ n + 1) (y : ℝ) (hy : 0 < y) :
    f j y = G n f j y +
      χ n j * ((y : ℂ) * (αC κ lam lam' * G n f (j + 1) y + βC n κ lam lam' j * G n f (j - 1) y)) := by
  by_cases hm : 2 * j = n
  · have hjn : j ≤ n := by omega
    have A := alg hne hsys j hjn hm y hy
    have h1 : f (j + 1) y = G n f (j + 1) y := by
      by_cases hj1 : n < j + 1
      · rw [G_of_lt n f (j + 1) hj1]
        have e : j + 1 = n + 1 := by omega
        rw [e, hfn]
      · rw [G_of_ne n f (j + 1) (by omega) (by omega)]
    have h2 : βC n κ lam lam' j * f (j - 1) y = βC n κ lam lam' j * G n f (j - 1) y := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp [βC]
      · rw [G_of_ne n f (j - 1) (by omega) (by omega)]
    rw [G_of_mid n f j hm, χ, if_pos hm, one_mul, A, h1, mul_add, h2]
    ring
  · rw [χ, if_neg hm, zero_mul, add_zero]
    by_cases hjn : n < j
    · have e : j = n + 1 := by omega
      subst e
      rw [G_of_lt n f (n + 1) hjn, hfn]
    · rw [G_of_ne n f j hm (by omega)]

theorem row (hne : lam ≠ lam' ∨ Odd n) (hfn : ∀ y : ℝ, f (n + 1) y = 0) (hsys : HSys n κ lam lam' f)
    (y : ℝ) (hy : 0 < y) (i : ℕ) (hi : i ≤ n) :
    (y : ℂ) * deriv (G n f i) y =
      aC n lam lam' i * G n f i y + ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y := by
  by_cases hm : 2 * i = n
  · rw [rowsum_mid n κ lam lam' f y i hm, G_of_mid n f i hm]
    simp
  · rw [rowsum n κ lam lam' f y i hm]
    have hGi : G n f i = f i := G_of_ne n f i hm hi
    have R := rel hsys i hi hm y hy
    have E1 := f_eq hne hfn hsys (i + 1) (by omega) y hy
    have E2 := f_eq hne hfn hsys (i - 1) (by omega) y hy
    have e1 : i + 1 + 1 = i + 2 := by omega
    rw [Nat.add_sub_cancel, e1] at E1
    rw [hGi, R, E1, E2, hGi]
    ring

theorem G_differentiableOn (hsys : HSys n κ lam lam' f) (i : ℕ) :
    DifferentiableOn ℝ (G n f i) (Set.Ioi 0) := by
  unfold G
  split_ifs with h
  · exact differentiableOn_const 0
  · exact (hsys ⟨i, by omega⟩).1

theorem aC_re (hre : lam.re = lam'.re) (i : ℕ) : 1 ≤ (aC n lam lam' i).re := by
  unfold aC
  split_ifs with h
  · simp
  · have h2 : (2 * (lam - lam')).re = 0 := by simp [Complex.mul_re, hre]
    rw [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, h2, zero_div, sub_zero]

theorem norm_mul_le_of_norm_le_one_right (a d : ℂ) (h : ‖d‖ ≤ 1) : ‖a * d‖ ≤ ‖a‖ := by
  rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) h

theorem norm_mul_le_of_norm_le_one_left (x a : ℂ) (h : ‖x‖ ≤ 1) : ‖x * a‖ ≤ ‖a‖ := by
  rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) h

theorem norm_block_le (x u α β d1 d2 : ℂ) (hx : ‖x‖ ≤ 1) (h1 : ‖d1‖ ≤ 1) (h2 : ‖d2‖ ≤ 1) :
    ‖x * u * (α * d1 + β * d2)‖ ≤ ‖u‖ * (‖α‖ + ‖β‖) := by
  have e3 : ‖α * d1 + β * d2‖ ≤ ‖α‖ + ‖β‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_mul_le_of_norm_le_one_right α d1 h1)
      (norm_mul_le_of_norm_le_one_right β d2 h2))
  have e4 : ‖x * u‖ ≤ ‖u‖ := norm_mul_le_of_norm_le_one_left x u hx
  rw [norm_mul]
  exact mul_le_mul e4 e3 (norm_nonneg _) (norm_nonneg _)

noncomputable def K (n : ℕ) (κ lam lam' : ℂ) (i : ℕ) : ℝ :=
  ‖uC n κ i‖ + ‖vC n κ i‖ +
    (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
      ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖))

theorem K_nonneg (i : ℕ) : 0 ≤ K n κ lam lam' i := by
  unfold K; positivity

noncomputable def Kc (n : ℕ) (κ lam lam' : ℂ) : ℝ := ∑ i ∈ range (n + 1), K n κ lam lam' i

theorem Kc_nonneg : 0 ≤ Kc n κ lam lam' := Finset.sum_nonneg fun i _ => K_nonneg i

theorem norm_Bn_le (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (i j : ℕ) (hi : i ≤ n) :
    ‖Bn n κ lam lam' y i j‖ ≤ Kc n κ lam lam' * y := by
  have hK : K n κ lam lam' i ≤ Kc n κ lam lam' :=
    Finset.single_le_sum (f := K n κ lam lam') (fun k _ => K_nonneg k) (mem_range.mpr (by omega))
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  unfold Bn
  split_ifs with hm
  · rw [norm_zero]; exact mul_nonneg Kc_nonneg hy.le
  · have hA : ‖uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1)‖ ≤ ‖uC n κ i‖ + ‖vC n κ i‖ :=
      (norm_add_le _ _).trans (add_le_add
        (norm_mul_le_of_norm_le_one_right _ _ (norm_δ_le _ _))
        (norm_mul_le_of_norm_le_one_right _ _ (norm_δ_le _ _)))
    have hB :
        ‖χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
            χ n (i - 1) * vC n κ i *
              (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1))‖ ≤
          ‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
            ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖) :=
      (norm_add_le _ _).trans (add_le_add
        (norm_block_le _ _ _ _ _ _ (norm_χ_le _ _) (norm_δ_le _ _) (norm_δ_le _ _))
        (norm_block_le _ _ _ _ _ _ (norm_χ_le _ _) (norm_δ_le _ _) (norm_δ_le _ _)))
    have hy2 : y ^ 2 ≤ y := pow_le_of_le_one hy.le hy1 two_ne_zero
    calc _ ≤ ‖(y : ℂ) * (uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1))‖ +
            ‖(y : ℂ) ^ 2 *
              (χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
                χ n (i - 1) * vC n κ i *
                  (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1)))‖ :=
          norm_add_le _ _
      _ ≤ y * (‖uC n κ i‖ + ‖vC n κ i‖) +
            y ^ 2 * (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
              ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖)) := by
          rw [norm_mul, norm_mul, norm_pow, hny]
          exact add_le_add (mul_le_mul_of_nonneg_left hA hy.le) (mul_le_mul_of_nonneg_left hB (sq_nonneg y))
      _ ≤ y * (‖uC n κ i‖ + ‖vC n κ i‖) +
            y * (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
              ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hy2 (by positivity))
      _ = K n κ lam lam' i * y := by rw [K]; ring
      _ ≤ Kc n κ lam lam' * y := mul_le_mul_of_nonneg_right hK hy.le

end LanglandsTunnell.AlphaAux

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "norm_le_mul_rpow_near_zero_of_first_order_system_of_diag"
namespace AlphaAux
p2m_open "LanglandsTunnell"

open Finset

variable {n : ℕ} {κ lam lam' : ℂ} {f : ℕ → ℝ → ℂ}

theorem main (hne : lam ≠ lam' ∨ Odd n) (hre : lam.re = lam'.re) (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hsys : HSys n κ lam lam' f) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := sysN n (G n f) (aC n lam lam') (Bn n κ lam lam') (Kc n κ lam lam')
    (fun i _ => aC_re hre i) (fun y hy hy1 i j hi _ => norm_Bn_le y hy hy1 i j hi)
    (fun i _ => G_differentiableOn hsys i) (fun y hy _ i hi => row hne hfn hsys y hy i hi) ε hε
  have hC0 : 0 ≤ C := by
    have h := hC 1 one_pos le_rfl 0 (Nat.zero_le _)
    rw [Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hCall : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖G n f i y‖ ≤ C * y ^ (1 - ε) := by
    intro y hy hy1 i
    by_cases hi : i ≤ n
    · exact hC y hy hy1 i hi
    · rw [G_of_lt n f i (by omega), norm_zero]
      exact mul_nonneg hC0 (Real.rpow_nonneg hy.le _)
  set S := ∑ i ∈ range (n + 1), ‖βC n κ lam lam' i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C * (1 + ‖αC κ lam lam'‖ + S), ?_⟩
  intro p y hy hy1
  have hp : (p : ℕ) ≤ n := Nat.lt_succ_iff.mp p.isLt
  have E := f_eq hne hfn hsys p (by omega) y hy
  have hβ : ‖βC n κ lam lam' p‖ ≤ S :=
    Finset.single_le_sum (f := fun i => ‖βC n κ lam lam' i‖) (fun _ _ => norm_nonneg _) (mem_range.mpr p.isLt)
  set s := y ^ (1 - ε) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hy.le _
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h1 := hCall y hy hy1 p
  have h2 := hCall y hy hy1 (p + 1)
  have h3 := hCall y hy hy1 (p - 1)
  have hin : ‖αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y‖ ≤
      (‖αC κ lam lam'‖ + S) * (C * s) := by
    calc _ ≤ ‖αC κ lam lam' * G n f (p + 1) y‖ + ‖βC n κ lam lam' p * G n f (p - 1) y‖ := norm_add_le _ _
      _ = ‖αC κ lam lam'‖ * ‖G n f (p + 1) y‖ + ‖βC n κ lam lam' p‖ * ‖G n f (p - 1) y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖αC κ lam lam'‖ * (C * s) + S * (C * s) :=
          add_le_add (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (mul_le_mul hβ h3 (norm_nonneg _) hS0)
      _ = (‖αC κ lam lam'‖ + S) * (C * s) := by ring
  have hcorr : ‖χ n p * ((y : ℂ) * (αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y))‖ ≤
      (‖αC κ lam lam'‖ + S) * (C * s) := by
    rw [norm_mul, norm_mul, hny]
    calc _ ≤ 1 * (1 * ((‖αC κ lam lam'‖ + S) * (C * s))) :=
          mul_le_mul (norm_χ_le _ _) (mul_le_mul hy1 hin (norm_nonneg _) zero_le_one)
            (mul_nonneg hy.le (norm_nonneg _)) zero_le_one
      _ = _ := by ring
  rw [E]
  calc _ ≤ ‖G n f p y‖ +
        ‖χ n p * ((y : ℂ) * (αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y))‖ :=
        norm_add_le _ _
    _ ≤ C * s + (‖αC κ lam lam'‖ + S) * (C * s) := add_le_add h1 hcorr
    _ = C * (1 + ‖αC κ lam lam'‖ + S) * s := by ring

end LanglandsTunnell.AlphaAux

theorem solution
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (hne : lam ≠ lam' ∨ Odd n) (hre : lam.re = lam'.re) (f : ℕ → ℝ → ℂ)
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
  intro ε hε
  exact LanglandsTunnell.AlphaAux.main hne hre hfn hsys ε hε

end S_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
end P2MW
export P2MW.S_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq (solution)
