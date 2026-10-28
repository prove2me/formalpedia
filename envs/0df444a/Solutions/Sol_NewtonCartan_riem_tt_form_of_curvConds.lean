-- Prove2me | solution 1 for NewtonCartan.riem_tt_form_of_curvConds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:18:09.327742+00:00
-- url     : https://prove2.me/submissions/c891c2bd-3a14-416a-af0e-f9b624d46279

import Definitions.Def_NewtonCartan_defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! CurvConds (2)+(3) ⇒ Trautman $t_b$-factor form of Riemann. -/

private lemma tt_zero : tt (0 : Fin 4) = 1 := rfl

private lemma tt_of_ne {a : Fin 4} (ha : a ≠ 0) : tt a = 0 := by
  simp [tt, ha]

private lemma riem_antisymm_last (Γ : Conn) (x : E) (a b c d : Fin 4) :
    riem Γ x a b c d = -riem Γ x a b d c := by
  simp only [riem]
  have hsum :
      (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) =
        -∑ e : Fin 4, (Γ x a c e * Γ x e d b - Γ x a d e * Γ x e c b) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  linarith [hsum]

private lemma riemUp2_of_ne (Γ : Conn) (x : E) (a b c d : Fin 4) (hb : b ≠ 0) :
    riemUp2 Γ x a b c d = riem Γ x a b c d := by
  simp only [riemUp2]
  have hterm (n : Fin 4) :
      riem Γ x a n c d * hh n b = if n = b then riem Γ x a b c d else 0 := by
    simp only [hh]
    by_cases hn : n = b
    · subst hn; simp [hb]
    · simp [hn]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma riem_middle_spatial_zero (Γt : Conn) (ρ : E → ℝ)
    (hcurv : CurvConds Γt ρ) (x : E) (a b c d : Fin 4) (hb : b ≠ 0) :
    riem Γt x a b c d = 0 := by
  have h := hcurv.2.2 x a b c d
  rwa [riemUp2_of_ne Γt x a b c d hb] at h

private lemma riemUp3_of_ne (Γ : Conn) (x : E) (a b c d : Fin 4) (hc : c ≠ 0) :
    riemUp3 Γ x a b c d = riem Γ x a b c d := by
  simp only [riemUp3]
  have hterm (n : Fin 4) :
      riem Γ x a b n d * hh n c = if n = c then riem Γ x a b c d else 0 := by
    simp only [hh]
    by_cases hn : n = c
    · subst hn; simp [hc]
    · simp [hn]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma riem_time_spatial_zero (Γt : Conn) (ρ : E → ℝ)
    (hcurv : CurvConds Γt ρ) (x : E) (a i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    riem Γt x a 0 i j = 0 := by
  have hL : riemUp3 Γt x a 0 i j = riem Γt x a 0 i j :=
    riemUp3_of_ne Γt x a 0 i j hi
  have hR : riemUp3 Γt x i j a 0 = 0 := by
    by_cases ha : a = 0
    · subst ha
      simp only [riemUp3, hh]
      apply Finset.sum_eq_zero; intro n _
      split_ifs with h <;> simp_all
    · have hEq : riemUp3 Γt x i j a 0 = riem Γt x i j a 0 :=
        riemUp3_of_ne Γt x i j a 0 ha
      rw [hEq]
      exact riem_middle_spatial_zero Γt ρ hcurv x i j a 0 hj
  have hsym := hcurv.2.1 x a 0 i j
  calc riem Γt x a 0 i j = riemUp3 Γt x a 0 i j := hL.symm
    _ = riemUp3 Γt x i j a 0 := hsym
    _ = 0 := hR

theorem solution (Γt : Conn) (ρ : E → ℝ)
    (_hΓt : IsClassical Γt) (hcurv : CurvConds Γt ρ) (x : E) (a b c d : Fin 4) :
    riem Γt x a b c d =
      tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c) := by
  by_cases hb : b = 0
  · subst hb
    rw [tt_zero, one_mul]
    by_cases hc : c = 0
    · subst hc
      rw [tt_zero, one_mul]
      by_cases hd : d = 0
      · subst hd
        -- Goal: R000 = R000 - R000
        have h000 : riem Γt x a 0 0 0 = 0 := by
          have h := riem_antisymm_last Γt x a 0 0 0
          linarith
        simp [h000]
      · rw [tt_of_ne hd, zero_mul, sub_zero]
    · rw [tt_of_ne hc, zero_mul, zero_sub]
      by_cases hd : d = 0
      · subst hd
        rw [tt_zero, one_mul]
        exact riem_antisymm_last Γt x a 0 c 0
      · rw [tt_of_ne hd, zero_mul, neg_zero]
        exact riem_time_spatial_zero Γt ρ hcurv x a c d hc hd
  · rw [tt_of_ne hb, zero_mul, riem_middle_spatial_zero Γt ρ hcurv x a b c d hb]
