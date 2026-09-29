-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/32eb0d85-0de4-51e3-9cab-ef438812e0cf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial

namespace GammaUniq

theorem injective_rpow_neg (N : ℕ) (hN : 1 < N) : Function.Injective fun t : ℝ => (N : ℂ) ^ (-(t : ℂ)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  intro t₁ t₂ ht
  have e1 : ∀ t : ℝ, (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (N : ℝ))]
    push_cast
    rfl
  simp only [e1] at ht
  have ht2 : (N : ℝ) ^ (-t₁) = (N : ℝ) ^ (-t₂) := by exact_mod_cast ht
  have hmono : StrictMono fun t : ℝ => (N : ℝ) ^ t := fun a b hab => (Real.rpow_lt_rpow_left_iff hN1).2 hab
  have := hmono.injective ht2
  linarith

theorem poly_form_eq (N : ℕ) (hN : 1 < N) (S : Set ℝ) (hS : S.Infinite) (f : ℝ → ℂ)
    (P Q P' Q' : ℂ[X]) (m m' : ℤ)
    (h : ∀ t : ℝ, t ∈ S → f t * Q.eval ((N : ℂ) ^ (-(t : ℂ))) = (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))))
    (h' : ∀ t : ℝ, t ∈ S → f t * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ)))) :
    Polynomial.X ^ (m' - m).toNat * (P * Q') = Polynomial.X ^ (m - m').toNat * (P' * Q) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  set M : ℤ := max m m' with hM
  have hMe : (M : ℤ) - m = e := by
    simp only [he, hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : (M : ℤ) - m' = e' := by
    simp only [he', hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
  have hx : ∀ (k : ℤ) (n : ℕ) (t : ℝ), (M : ℤ) - k = n →
      (N : ℂ) ^ ((k : ℂ) * (t : ℂ)) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) = ((N : ℂ) ^ (-(t : ℂ))) ^ n := by
    intro k n t hk
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_nat_mul]
    congr 1
    have : (n : ℂ) = (M : ℂ) - (k : ℂ) := by exact_mod_cast hk.symm
    rw [this]; ring
  have hA : ∀ t : ℝ, t ∈ S →
      (Polynomial.X ^ e * (P * Q')).eval ((N : ℂ) ^ (-(t : ℂ))) =
        (Polynomial.X ^ e' * (P' * Q)).eval ((N : ℂ) ^ (-(t : ℂ))) := by
    intro t ht
    have h1 := h t ht
    have h2 := h' t ht
    have key : (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) =
        (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by
      calc (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))
          = (f t * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h1]
        _ = (f t * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by ring
        _ = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h2]
    have key2 := congrArg (fun z => z * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ)))) key
    have l1 := hx m e t hMe
    have l2 := hx m' e' t hMe'
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc ((N : ℂ) ^ (-(t : ℂ))) ^ e * (P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))))
        = ((N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := by rw [← l1]; ring
      _ = ((N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := key2
      _ = ((N : ℂ) ^ (-(t : ℂ))) ^ e' * (P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) := by rw [← l2]; ring
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' S) ?_ ?_
  · rintro x ⟨t, ht, rfl⟩; exact hA t ht
  · exact hS.image (injective_rpow_neg N hN).injOn

theorem eval_identity (N : ℕ) (hN : 1 < N) (A B : ℂ[X]) (i j : ℕ) (a b : ℤ) (hij : (i : ℤ) + a = (j : ℤ) + b)
    (h : Polynomial.X ^ i * A = Polynomial.X ^ j * B) (s : ℂ) :
    A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hev := congrArg (Polynomial.eval ((N : ℂ) ^ (-s))) h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hev
  have hi : ((N : ℂ) ^ (-s)) ^ i * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s) = (N : ℂ) ^ ((a : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have hj : ((N : ℂ) ^ (-s)) ^ j * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s) = (N : ℂ) ^ ((b : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have hc : (((i : ℤ) + a : ℂ)) = (((j : ℤ) + b : ℂ)) := by exact_mod_cast hij
  calc A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s)
      = A.eval ((N : ℂ) ^ (-s)) * (((N : ℂ) ^ (-s)) ^ i * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s)) := by rw [hi]
    _ = (((N : ℂ) ^ (-s)) ^ i * A.eval ((N : ℂ) ^ (-s))) * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s) := by ring
    _ = (((N : ℂ) ^ (-s)) ^ j * B.eval ((N : ℂ) ^ (-s))) * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s) := by rw [hev, hc]
    _ = B.eval ((N : ℂ) ^ (-s)) * (((N : ℂ) ^ (-s)) ^ j * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s)) := by ring
    _ = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by rw [hj]

theorem toNat_sub_toNat (k l : ℤ) : (((k - l).toNat : ℤ)) - (((l - k).toNat : ℤ)) = k - l := by
  rw [show l - k = -(k - l) by ring]; exact Int.toNat_sub_toNat_neg (k - l)

theorem gamma_unique (N : ℕ) (hN : 1 < N) (Z Zd : ℂ → ℂ) (E : ℂ) (e : ℤ)
    (P Pd : ℂ[X]) (m md : ℤ) (σ₀ σ₁ : ℝ)
    (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, s.re < σ₁ → Zd s = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)))
    (hE : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) =
      (E * (N : ℂ) ^ ((e : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (P' Q' Pd' Qd' Γn Γd : ℂ[X]) (m' md' a : ℤ) (σ₀' σ₁' : ℝ) (hQ' : Q' ≠ 0) (hQd' : Qd' ≠ 0)
    (hZ' : ∀ s : ℂ, σ₀' < s.re → Z s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)))
    (hZd' : ∀ s : ℂ, s.re < σ₁' → Zd s * Qd'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s)))
    (hΓ : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ (-s)) * ((N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s))) * Q'.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) * ((N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) * Qd'.eval ((N : ℂ) ^ (-s)))
    (hP : P ≠ 0) :
    ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = E * (N : ℂ) ^ ((e : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  have B1 := poly_form_eq N hN (Set.Ioi (max σ₀ σ₀')) (Set.Ioi_infinite _) (fun t => Z t) P 1 P' Q' m m' ?_ ?_
  rotate_left
  · intro t ht
    have : σ₀ < ((t : ℂ)).re := by simp only [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_left _ _) ht
    simp only [Polynomial.eval_one, mul_one]; exact hZ _ this
  · intro t ht
    have : σ₀' < ((t : ℂ)).re := by simp only [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_right _ _) ht
    exact hZ' _ this

  have B2 := poly_form_eq N hN (Set.Iio (min σ₁ σ₁')) (Set.Iio_infinite _) (fun t => Zd t) Pd 1 Pd' Qd' md md' ?_ ?_
  rotate_left
  · intro t ht
    have : ((t : ℂ)).re < σ₁ := by simp only [Complex.ofReal_re]; exact lt_of_lt_of_le ht (min_le_left _ _)
    simp only [Polynomial.eval_one, mul_one]; exact hZd _ this
  · intro t ht
    have : ((t : ℂ)).re < σ₁' := by simp only [Complex.ofReal_re]; exact lt_of_lt_of_le ht (min_le_right _ _)
    exact hZd' _ this

  have B3 := poly_form_eq N hN Set.univ Set.infinite_univ
    (fun t => (N : ℂ) ^ ((md : ℂ) * (t : ℂ)) * Pd.eval ((N : ℂ) ^ (-(t : ℂ)))) Pd 1 (Polynomial.C E * P) 1 md (m + e) ?_ ?_
  rotate_left
  · intro t _; simp only [Polynomial.eval_one, mul_one]
  · intro t _
    simp only [Polynomial.eval_one, mul_one]
    rw [hE, Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (((m + e : ℤ)) : ℂ) * (t : ℂ) = (e : ℂ) * (t : ℂ) + (m : ℂ) * (t : ℂ) by push_cast; ring, Complex.cpow_add _ _ hN0]
    ring

  have B4 := poly_form_eq N hN Set.univ Set.infinite_univ
    (fun t => Γd.eval ((N : ℂ) ^ (-(t : ℂ))) * ((N : ℂ) ^ ((md' : ℂ) * (t : ℂ)) * Pd'.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))))
    (Γd * Pd' * Q') 1 (Γn * P' * Qd') 1 md' (a + m') ?_ ?_
  rotate_left
  · intro t _; simp only [Polynomial.eval_one, mul_one, Polynomial.eval_mul]; ring
  · intro t _
    simp only [Polynomial.eval_one, mul_one]
    rw [hΓ, Polynomial.eval_mul, Polynomial.eval_mul]
    rw [show (((a + m' : ℤ)) : ℂ) * (t : ℂ) = (a : ℂ) * (t : ℂ) + (m' : ℂ) * (t : ℂ) by push_cast; ring, Complex.cpow_add _ _ hN0]
    ring

  set i₁ := (m' - m).toNat; set j₁ := (m - m').toNat
  set i₂ := (md' - md).toNat; set j₂ := (md - md').toNat
  set i₃ := (m + e - md).toNat; set j₃ := (md - (m + e)).toNat
  set i₄ := (a + m' - md').toNat; set j₄ := (md' - (a + m')).toNat
  have hG : Polynomial.X ^ (j₄ + j₂ + i₁ + i₃) * Γn * (P * Q' * Qd') =
      Polynomial.X ^ (i₄ + j₁ + i₂ + j₃) * (Polynomial.C E * Γd) * (P * Q' * Qd') := by
    linear_combination (Polynomial.X ^ (j₄ + j₂ + i₃) * Γn * Qd') * B1 + (-(Polynomial.X ^ (i₄ + j₁ + i₃) * Γd * Q')) * B2 +
      (Polynomial.X ^ (i₄ + j₁ + i₂) * Γd * Qd' * Q') * B3 + (-(Polynomial.X ^ (j₁ + j₂ + i₃))) * B4
  have hnz : P * Q' * Qd' ≠ 0 := mul_ne_zero (mul_ne_zero hP hQ') hQd'
  have hpoly : Polynomial.X ^ (j₄ + j₂ + i₁ + i₃) * Γn = Polynomial.X ^ (i₄ + j₁ + i₂ + j₃) * (Polynomial.C E * Γd) :=
    mul_right_cancel₀ hnz hG

  have r₁ := toNat_sub_toNat m' m
  have r₂ := toNat_sub_toNat md' md
  have r₃ := toNat_sub_toNat (m + e) md
  have r₄ := toNat_sub_toNat (a + m') md'
  intro s
  have := eval_identity N hN Γn (Polynomial.C E * Γd) (j₄ + j₂ + i₁ + i₃) (i₄ + j₁ + i₂ + j₃) a e
    (by push_cast; omega) hpoly s
  rw [Polynomial.eval_mul, Polynomial.eval_C] at this
  rw [this]; ring

end GammaUniq

theorem solution
    (N : ℕ) (hN : 1 < N) (Z Zd : ℂ → ℂ) (E : ℂ) (e : ℤ)
    (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ)
    (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, s.re < σ₁ → Zd s = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)))
    (hE : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) =
      (E * (N : ℂ) ^ ((e : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (P' Q' Pd' Qd' Γn Γd : Polynomial ℂ) (m' md' a : ℤ) (σ₀' σ₁' : ℝ) (hQ' : Q' ≠ 0) (hQd' : Qd' ≠ 0)
    (hZ' : ∀ s : ℂ, σ₀' < s.re → Z s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)))
    (hZd' : ∀ s : ℂ, s.re < σ₁' → Zd s * Qd'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s)))
    (hΓ : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ (-s)) * ((N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s))) * Q'.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) * ((N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) * Qd'.eval ((N : ℂ) ^ (-s)))
    (hP : P ≠ 0) :
    ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = E * (N : ℂ) ^ ((e : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)) := by
  exact GammaUniq.gamma_unique N hN Z Zd E e P Pd m md σ₀ σ₁ hZ hZd hE P' Q' Pd' Qd' Γn Γd m' md' a σ₀' σ₁' hQ' hQd' hZ' hZd' hΓ hP

end S_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe (solution)
