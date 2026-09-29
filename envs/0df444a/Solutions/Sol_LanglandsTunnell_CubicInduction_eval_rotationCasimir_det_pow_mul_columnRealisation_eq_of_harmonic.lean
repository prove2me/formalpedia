-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c24dfa87-5d84-5c36-94fb-70f74e660f5c

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic

set_option autoImplicit false

namespace WsE
namespace O5

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ
abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

def orth (o : Fin 3 → Fin 3 → ℝ) : Prop := ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0
def pt (o : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

def Lop (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : R9 := act ν c d P - act ν d c P

def Omega (ν : Fin 3 → ℂ) (P : R9) : R9 :=
  Lop ν 0 1 (Lop ν 0 1 P) + Lop ν 0 2 (Lop ν 0 2 P) + Lop ν 1 2 (Lop ν 1 2 P)

theorem f01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
theorem f02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
theorem f10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
theorem f12 : ((1 : Fin 3) = 2) = False := eq_false (by decide)
theorem f20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
theorem f21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
theorem lt01 : (0 : Fin 3) < 1 := by decide
theorem lt02 : (0 : Fin 3) < 2 := by decide
theorem lt12 : (1 : Fin 3) < 2 := by decide
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide

theorem orthC {o : Fin 3 → Fin 3 → ℝ} (ho : orth o) (x y : Fin 3) :
    ((o 0 x : ℝ) : ℂ) * ((o 0 y : ℝ) : ℂ) + ((o 1 x : ℝ) : ℂ) * ((o 1 y : ℝ) : ℂ) +
      ((o 2 x : ℝ) : ℂ) * ((o 2 y : ℝ) : ℂ) = if x = y then 1 else 0 := by
  have h := ho x y
  simp only [Fin.sum_univ_three] at h
  split_ifs with hxy
  · rw [if_pos hxy] at h; exact_mod_cast h
  · rw [if_neg hxy] at h; exact_mod_cast h

theorem hasDerivAt_eval {σ : Type} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (x : ℝ → σ → ℂ) (x' : σ → ℂ) (t₀ : ℝ) (hx : ∀ k, HasDerivAt (fun t => x t k) (x' k) t₀) :
    HasDerivAt (fun t => eval (x t) P) (∑ k, eval (x t₀) (pderiv k P) * x' k) t₀ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const t₀ a
  | add p q hp hq =>
    simp only [map_add]
    have := hp.fun_add hq
    convert this using 1 <;> try with_reducible_and_instances rfl
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  | mul_X p k hp =>
    simp only [map_mul, eval_X]
    have := hp.fun_mul (hx k)
    convert this using 1 <;> try with_reducible_and_instances rfl
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X]
    have h1 : ∀ k' : σ, (eval (x t₀) (pderiv k' p) * x t₀ k +
        eval (x t₀) p * eval (x t₀) (Pi.single (M := fun _ => MvPolynomial σ ℂ) k' 1 k)) * x' k' =
        eval (x t₀) (pderiv k' p) * x' k' * x t₀ k + (if k = k' then eval (x t₀) p * x' k' else 0) := by
      intro k'
      rw [Pi.single_apply]
      split_ifs with h
      · rw [map_one]; ring
      · rw [map_zero]; ring
    rw [Finset.sum_congr rfl (fun k' _ => h1 k'), Finset.sum_add_distrib, Finset.sum_ite_eq,
      ← Finset.sum_mul]
    simp

def cR (c d : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a j => if j = c then Real.cos t * o a c - Real.sin t * o a d
    else if j = d then Real.sin t * o a c + Real.cos t * o a d else o a j

theorem cR_zero (c d : Fin 3) (hcd : c ≠ d) (o : Fin 3 → Fin 3 → ℝ) : cR c d o 0 = o := by
  funext a j
  simp only [cR, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero, zero_add]
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2]
  · rfl

theorem cR_cR (c d : Fin 3) (hcd : c ≠ d) (o : Fin 3 → Fin 3 → ℝ) (t s : ℝ) :
    cR c d (cR c d o t) s = cR c d o (t + s) := by
  funext a j
  simp only [cR, if_pos rfl, if_neg (Ne.symm hcd), if_neg hcd, Real.cos_add, Real.sin_add]
  split_ifs with h1 h2
  · ring
  · ring
  · rfl

theorem hasDerivAt_cR (c d : Fin 3) (hcd : c ≠ d) (o : Fin 3 → Fin 3 → ℝ) (t₀ : ℝ) (a j : Fin 3) :
    HasDerivAt (fun t => ((cR c d o t a j : ℝ) : ℂ))
      (((if j = c then -Real.sin t₀ * o a c - Real.cos t₀ * o a d
        else if j = d then Real.cos t₀ * o a c - Real.sin t₀ * o a d else 0 : ℝ) : ℂ)) t₀ := by
  apply HasDerivAt.ofReal_comp
  simp only [cR]
  split_ifs with h1 h2
  · have := ((Real.hasDerivAt_cos t₀).mul_const (o a c)).fun_sub ((Real.hasDerivAt_sin t₀).mul_const (o a d))
    simpa using this
  · have := ((Real.hasDerivAt_sin t₀).mul_const (o a c)).fun_add ((Real.hasDerivAt_cos t₀).mul_const (o a d))
    simpa [sub_eq_add_neg, neg_mul] using this
  · exact hasDerivAt_const t₀ (o a j)

theorem cR_orth01 (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (t : ℝ) : orth (cR 0 1 o t) := by
  have h := fun x y => ho x y
  simp only [Fin.sum_univ_three] at h
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2; have h10 := h 1 0; have h11 := h 1 1
  have h12 := h 1 2; have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hT := Real.sin_sq_add_cos_sq t
  intro i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp only [cR, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false]
  · linear_combination (Real.cos t)^2 * h00 + (Real.sin t)^2 * h11 - 2 * (Real.sin t) * (Real.cos t) * h01 + hT
  · linear_combination (Real.sin t) * (Real.cos t) * h00 - (Real.sin t) * (Real.cos t) * h11 + ((Real.cos t)^2 - (Real.sin t)^2) * h01
  · linear_combination (Real.cos t) * h02 - (Real.sin t) * h12
  · linear_combination (Real.sin t) * (Real.cos t) * h00 - (Real.sin t) * (Real.cos t) * h11 + ((Real.cos t)^2 - (Real.sin t)^2) * h01
  · linear_combination (Real.sin t)^2 * h00 + (Real.cos t)^2 * h11 + 2 * (Real.sin t) * (Real.cos t) * h01 + hT
  · linear_combination (Real.sin t) * h02 + (Real.cos t) * h12
  · linear_combination (Real.cos t) * h20 - (Real.sin t) * h21
  · linear_combination (Real.sin t) * h20 + (Real.cos t) * h21
  · linear_combination h22

theorem cR_orth02 (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (t : ℝ) : orth (cR 0 2 o t) := by
  have h := fun x y => ho x y
  simp only [Fin.sum_univ_three] at h
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2; have h10 := h 1 0; have h11 := h 1 1
  have h12 := h 1 2; have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hT := Real.sin_sq_add_cos_sq t
  intro i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp only [cR, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false]
  · linear_combination (Real.cos t)^2 * h00 + (Real.sin t)^2 * h22 - 2 * (Real.sin t) * (Real.cos t) * h02 + hT
  · linear_combination (Real.cos t) * h01 - (Real.sin t) * h21
  · linear_combination (Real.sin t) * (Real.cos t) * h00 - (Real.sin t) * (Real.cos t) * h22 + ((Real.cos t)^2 - (Real.sin t)^2) * h02
  · linear_combination (Real.cos t) * h10 - (Real.sin t) * h12
  · linear_combination h11
  · linear_combination (Real.sin t) * h10 + (Real.cos t) * h12
  · linear_combination (Real.sin t) * (Real.cos t) * h00 - (Real.sin t) * (Real.cos t) * h22 + ((Real.cos t)^2 - (Real.sin t)^2) * h02
  · linear_combination (Real.sin t) * h01 + (Real.cos t) * h21
  · linear_combination (Real.sin t)^2 * h00 + (Real.cos t)^2 * h22 + 2 * (Real.sin t) * (Real.cos t) * h02 + hT

theorem cR_orth12 (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (t : ℝ) : orth (cR 1 2 o t) := by
  have h := fun x y => ho x y
  simp only [Fin.sum_univ_three] at h
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2; have h10 := h 1 0; have h11 := h 1 1
  have h12 := h 1 2; have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hT := Real.sin_sq_add_cos_sq t
  intro i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp only [cR, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false]
  · linear_combination h00
  · linear_combination (Real.cos t) * h01 - (Real.sin t) * h02
  · linear_combination (Real.sin t) * h01 + (Real.cos t) * h02
  · linear_combination (Real.cos t) * h10 - (Real.sin t) * h20
  · linear_combination (Real.cos t)^2 * h11 + (Real.sin t)^2 * h22 - 2 * (Real.sin t) * (Real.cos t) * h12 + hT
  · linear_combination (Real.sin t) * (Real.cos t) * h11 - (Real.sin t) * (Real.cos t) * h22 + ((Real.cos t)^2 - (Real.sin t)^2) * h12
  · linear_combination (Real.sin t) * h10 + (Real.cos t) * h20
  · linear_combination (Real.sin t) * (Real.cos t) * h11 - (Real.sin t) * (Real.cos t) * h22 + ((Real.cos t)^2 - (Real.sin t)^2) * h12
  · linear_combination (Real.sin t)^2 * h11 + (Real.cos t)^2 * h22 + 2 * (Real.sin t) * (Real.cos t) * h12 + hT

theorem bridge01 (ν : Fin 3 → ℂ) (H : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) :
    eval (pt o) (Lop ν 0 1 H) =
      ∑ a : Fin 3, (((o a 0 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 1) H) -
        ((o a 1 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 0) H)) := by
  have hC := orthC ho
  have hC00 := hC 0 0; have hC01 := hC 0 1; have hC02 := hC 0 2; have hC10 := hC 1 0; have hC11 := hC 1 1
  have hC12 := hC 1 2; have hC20 := hC 2 0; have hC21 := hC 2 1; have hC22 := hC 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at hC00 hC01 hC02 hC10 hC11 hC12 hC20 hC21 hC22
  simp only [Lop, act, Fin.sum_univ_three, map_add, map_sub, map_mul, map_sum, map_neg, map_zero, eval_X, eval_C,
    lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false]
  simp only [pt]
  linear_combination eval (pt o) (pderiv (0, 0) H) * ((↑(o 0 0) : ℂ) * hC10 - (↑(o 0 1) : ℂ) * hC00) +
    eval (pt o) (pderiv (0, 1) H) * ((↑(o 0 0) : ℂ) * hC11 - (↑(o 0 1) : ℂ) * hC01) +
    eval (pt o) (pderiv (0, 2) H) * ((↑(o 0 0) : ℂ) * hC12 - (↑(o 0 1) : ℂ) * hC02) +
    eval (pt o) (pderiv (1, 0) H) * ((↑(o 1 0) : ℂ) * hC10 - (↑(o 1 1) : ℂ) * hC00) +
    eval (pt o) (pderiv (1, 1) H) * ((↑(o 1 0) : ℂ) * hC11 - (↑(o 1 1) : ℂ) * hC01) +
    eval (pt o) (pderiv (1, 2) H) * ((↑(o 1 0) : ℂ) * hC12 - (↑(o 1 1) : ℂ) * hC02) +
    eval (pt o) (pderiv (2, 0) H) * ((↑(o 2 0) : ℂ) * hC10 - (↑(o 2 1) : ℂ) * hC00) +
    eval (pt o) (pderiv (2, 1) H) * ((↑(o 2 0) : ℂ) * hC11 - (↑(o 2 1) : ℂ) * hC01) +
    eval (pt o) (pderiv (2, 2) H) * ((↑(o 2 0) : ℂ) * hC12 - (↑(o 2 1) : ℂ) * hC02)

theorem bridge02 (ν : Fin 3 → ℂ) (H : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) :
    eval (pt o) (Lop ν 0 2 H) =
      ∑ a : Fin 3, (((o a 0 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 2) H) -
        ((o a 2 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 0) H)) := by
  have hC := orthC ho
  have hC00 := hC 0 0; have hC01 := hC 0 1; have hC02 := hC 0 2; have hC10 := hC 1 0; have hC11 := hC 1 1
  have hC12 := hC 1 2; have hC20 := hC 2 0; have hC21 := hC 2 1; have hC22 := hC 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at hC00 hC01 hC02 hC10 hC11 hC12 hC20 hC21 hC22
  simp only [Lop, act, Fin.sum_univ_three, map_add, map_sub, map_mul, map_sum, map_neg, map_zero, eval_X, eval_C,
    lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false]
  simp only [pt]
  linear_combination eval (pt o) (pderiv (0, 0) H) * ((↑(o 0 0) : ℂ) * hC20 - (↑(o 0 2) : ℂ) * hC00) +
    eval (pt o) (pderiv (0, 1) H) * ((↑(o 0 0) : ℂ) * hC21 - (↑(o 0 2) : ℂ) * hC01) +
    eval (pt o) (pderiv (0, 2) H) * ((↑(o 0 0) : ℂ) * hC22 - (↑(o 0 2) : ℂ) * hC02) +
    eval (pt o) (pderiv (1, 0) H) * ((↑(o 1 0) : ℂ) * hC20 - (↑(o 1 2) : ℂ) * hC00) +
    eval (pt o) (pderiv (1, 1) H) * ((↑(o 1 0) : ℂ) * hC21 - (↑(o 1 2) : ℂ) * hC01) +
    eval (pt o) (pderiv (1, 2) H) * ((↑(o 1 0) : ℂ) * hC22 - (↑(o 1 2) : ℂ) * hC02) +
    eval (pt o) (pderiv (2, 0) H) * ((↑(o 2 0) : ℂ) * hC20 - (↑(o 2 2) : ℂ) * hC00) +
    eval (pt o) (pderiv (2, 1) H) * ((↑(o 2 0) : ℂ) * hC21 - (↑(o 2 2) : ℂ) * hC01) +
    eval (pt o) (pderiv (2, 2) H) * ((↑(o 2 0) : ℂ) * hC22 - (↑(o 2 2) : ℂ) * hC02)

theorem bridge12 (ν : Fin 3 → ℂ) (H : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) :
    eval (pt o) (Lop ν 1 2 H) =
      ∑ a : Fin 3, (((o a 1 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 2) H) -
        ((o a 2 : ℝ) : ℂ) * eval (pt o) (pderiv (a, 1) H)) := by
  have hC := orthC ho
  have hC00 := hC 0 0; have hC01 := hC 0 1; have hC02 := hC 0 2; have hC10 := hC 1 0; have hC11 := hC 1 1
  have hC12 := hC 1 2; have hC20 := hC 2 0; have hC21 := hC 2 1; have hC22 := hC 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at hC00 hC01 hC02 hC10 hC11 hC12 hC20 hC21 hC22
  simp only [Lop, act, Fin.sum_univ_three, map_add, map_sub, map_mul, map_sum, map_neg, map_zero, eval_X, eval_C,
    lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false]
  simp only [pt]
  linear_combination eval (pt o) (pderiv (0, 0) H) * ((↑(o 0 1) : ℂ) * hC20 - (↑(o 0 2) : ℂ) * hC10) +
    eval (pt o) (pderiv (0, 1) H) * ((↑(o 0 1) : ℂ) * hC21 - (↑(o 0 2) : ℂ) * hC11) +
    eval (pt o) (pderiv (0, 2) H) * ((↑(o 0 1) : ℂ) * hC22 - (↑(o 0 2) : ℂ) * hC12) +
    eval (pt o) (pderiv (1, 0) H) * ((↑(o 1 1) : ℂ) * hC20 - (↑(o 1 2) : ℂ) * hC10) +
    eval (pt o) (pderiv (1, 1) H) * ((↑(o 1 1) : ℂ) * hC21 - (↑(o 1 2) : ℂ) * hC11) +
    eval (pt o) (pderiv (1, 2) H) * ((↑(o 1 1) : ℂ) * hC22 - (↑(o 1 2) : ℂ) * hC12) +
    eval (pt o) (pderiv (2, 0) H) * ((↑(o 2 1) : ℂ) * hC20 - (↑(o 2 2) : ℂ) * hC10) +
    eval (pt o) (pderiv (2, 1) H) * ((↑(o 2 1) : ℂ) * hC21 - (↑(o 2 2) : ℂ) * hC11) +
    eval (pt o) (pderiv (2, 2) H) * ((↑(o 2 1) : ℂ) * hC22 - (↑(o 2 2) : ℂ) * hC12)

end

end WsE.O5

namespace WsE
namespace O5

open MvPolynomial

noncomputable section

def realise (j : Fin 3) (q : R3) : R9 :=
  MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q

theorem eval_realise (k : Fin 3 × Fin 3 → ℂ) (j : Fin 3) (q : R3) :
    eval k (realise j q) = eval (fun a => k (a, j)) q := by
  rw [show realise j q = rename (fun a : Fin 3 => (a, j)) q by
    rw [realise, MvPolynomial.rename_eq, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]; rfl]
  rw [eval_rename]; rfl

section Flow

variable (ν : Fin 3 → ℂ) (c d : Fin 3) (hcd : c ≠ d)
  (horth : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → ∀ t : ℝ, orth (cR c d o t))
  (hbridge : ∀ (H : R9) (o : Fin 3 → Fin 3 → ℝ), orth o → eval (pt o) (Lop ν c d H) =
      ∑ a : Fin 3, (((o a c : ℝ) : ℂ) * eval (pt o) (pderiv (a, d) H) -
        ((o a d : ℝ) : ℂ) * eval (pt o) (pderiv (a, c) H)))
include hcd

def vel (o : Fin 3 → Fin 3 → ℝ) (t : ℝ) (a j : Fin 3) : ℝ :=
  if j = c then -Real.sin t * o a c - Real.cos t * o a d
  else if j = d then Real.cos t * o a c - Real.sin t * o a d else 0

omit hcd in
theorem vel_def (o : Fin 3 → Fin 3 → ℝ) (t : ℝ) (a j : Fin 3) : vel c d o t a j =
    (if j = c then -Real.sin t * o a c - Real.cos t * o a d
      else if j = d then Real.cos t * o a c - Real.sin t * o a d else 0) := rfl

include horth hbridge in
theorem hasDerivAt_flow (H : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) :
    HasDerivAt (fun t => eval (pt (cR c d o t)) H) (eval (pt o) (Lop ν c d H)) 0 := by
  classical
  have hD := hasDerivAt_eval H (fun t => pt (cR c d o t)) (fun aj => ((vel c d o 0 aj.1 aj.2 : ℝ) : ℂ)) 0
    (fun aj => hasDerivAt_cR c d hcd o 0 aj.1 aj.2)
  convert hD using 1
  rw [hbridge H o ho, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [cR_zero c d hcd]
  rw [Fintype.sum_eq_add c d hcd (fun j hj => by
    rw [vel_def, if_neg hj.1, if_neg hj.2]; push_cast; ring)]
  rw [vel_def, vel_def, if_pos rfl, if_neg (Ne.symm hcd), if_pos rfl]
  simp only [Real.sin_zero, Real.cos_zero]
  push_cast
  ring

include horth hbridge in

theorem flow_deriv (F : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (t₀ : ℝ) {g₁ : ℂ}
    (hg : HasDerivAt (fun t => eval (pt (cR c d o t)) F) g₁ t₀) :
    eval (pt (cR c d o t₀)) (Lop ν c d F) = g₁ := by
  have h1 := hasDerivAt_flow ν c d hcd horth hbridge F (cR c d o t₀) (horth o ho t₀)
  have h3 : HasDerivAt (fun s => (fun t => eval (pt (cR c d o t)) F) (t₀ + s)) g₁ 0 :=
    HasDerivAt.comp_const_add t₀ 0 (by rw [add_zero]; exact hg)
  have h2' : (fun s => eval (pt (cR c d (cR c d o t₀) s)) F) =ᶠ[nhds (0 : ℝ)]
      (fun s => (fun t => eval (pt (cR c d o t)) F) (t₀ + s)) :=
    Filter.Eventually.of_forall fun s => by simp only [cR_cR c d hcd]
  exact h1.unique (h3.congr_of_eventuallyEq h2')

include horth hbridge in

theorem flow_second (F : R9) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (g₁ : ℝ → ℂ) (g₂ : ℂ)
    (hg : ∀ t, HasDerivAt (fun t => eval (pt (cR c d o t)) F) (g₁ t) t) (hg₁ : HasDerivAt g₁ g₂ 0) :
    eval (pt o) (Lop ν c d (Lop ν c d F)) = g₂ := by
  have h1 := hasDerivAt_flow ν c d hcd horth hbridge (Lop ν c d F) o ho
  have h2 : g₁ =ᶠ[nhds (0 : ℝ)] (fun t => eval (pt (cR c d o t)) (Lop ν c d F)) :=
    Filter.Eventually.of_forall fun t => (flow_deriv ν c d hcd horth hbridge F o ho t (hg t)).symm
  exact (h1.congr_of_eventuallyEq h2).unique hg₁

def acc (o : Fin 3 → Fin 3 → ℝ) (a j : Fin 3) : ℝ :=
  if j = c then -o a c else if j = d then -o a d else 0

omit hcd in
theorem hasDerivAt_vel (o : Fin 3 → Fin 3 → ℝ) (a j : Fin 3) :
    HasDerivAt (fun t => ((vel c d o t a j : ℝ) : ℂ)) ((acc c d o a j : ℝ) : ℂ) 0 := by
  apply HasDerivAt.ofReal_comp
  simp only [vel, acc]
  split_ifs with h1 h2
  · have := ((Real.hasDerivAt_sin 0).neg.mul_const (o a c)).fun_sub ((Real.hasDerivAt_cos 0).mul_const (o a d))
    simpa [neg_mul] using this
  · have := ((Real.hasDerivAt_cos 0).mul_const (o a c)).fun_sub ((Real.hasDerivAt_sin 0).mul_const (o a d))
    simpa using this
  · exact hasDerivAt_const 0 0

def g₁ (j : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (p : R3) (t : ℝ) : ℂ :=
  ∑ k : Fin 3, eval (fun a => ((cR c d o t a j : ℝ) : ℂ)) (pderiv k p) * ((vel c d o t k j : ℝ) : ℂ)

def g₂ (j : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (p : R3) : ℂ :=
  ∑ k : Fin 3, ((∑ m : Fin 3, eval (fun a => ((cR c d o 0 a j : ℝ) : ℂ)) (pderiv m (pderiv k p)) *
      ((vel c d o 0 m j : ℝ) : ℂ)) * ((vel c d o 0 k j : ℝ) : ℂ) +
    eval (fun a => ((cR c d o 0 a j : ℝ) : ℂ)) (pderiv k p) * ((acc c d o k j : ℝ) : ℂ))

theorem hasDerivAt_g (j : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (p : R3) (t : ℝ) :
    HasDerivAt (fun t => eval (pt (cR c d o t)) (realise j p)) (g₁ c d j o p t) t := by
  classical
  have hfun : (fun t => eval (pt (cR c d o t)) (realise j p)) =
      fun t => eval (fun a => ((cR c d o t a j : ℝ) : ℂ)) p := funext fun t => eval_realise _ j p
  rw [hfun]
  exact hasDerivAt_eval p (fun t a => ((cR c d o t a j : ℝ) : ℂ)) (fun k => ((vel c d o t k j : ℝ) : ℂ)) t
    (fun k => hasDerivAt_cR c d hcd o t k j)

theorem hasDerivAt_g₁ (j : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (p : R3) :
    HasDerivAt (g₁ c d j o p) (g₂ c d j o p) 0 := by
  classical
  have h : ∀ k ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt
      (fun t => eval (fun a => ((cR c d o t a j : ℝ) : ℂ)) (pderiv k p) * ((vel c d o t k j : ℝ) : ℂ))
      ((∑ m : Fin 3, eval (fun a => ((cR c d o 0 a j : ℝ) : ℂ)) (pderiv m (pderiv k p)) *
          ((vel c d o 0 m j : ℝ) : ℂ)) * ((vel c d o 0 k j : ℝ) : ℂ) +
        eval (fun a => ((cR c d o 0 a j : ℝ) : ℂ)) (pderiv k p) * ((acc c d o k j : ℝ) : ℂ)) 0 :=
    fun k _ => (hasDerivAt_eval (pderiv k p) (fun t a => ((cR c d o t a j : ℝ) : ℂ))
      (fun m => ((vel c d o 0 m j : ℝ) : ℂ)) 0 (fun m => hasDerivAt_cR c d hcd o 0 m j)).mul (hasDerivAt_vel c d o k j)
  exact HasDerivAt.sum h

include horth hbridge in
theorem eval_Lop_Lop_realise (j : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (p : R3) :
    eval (pt o) (Lop ν c d (Lop ν c d (realise j p))) = g₂ c d j o p :=
  flow_second ν c d hcd horth hbridge (realise j p) o ho (g₁ c d j o p) (g₂ c d j o p)
    (hasDerivAt_g c d hcd j o p) (hasDerivAt_g₁ c d hcd j o p)

end Flow

end

end WsE.O5

namespace WsE
namespace O5

open MvPolynomial

noncomputable section

theorem euler1 {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (x : Fin 3 → ℂ) :
    ∑ k : Fin 3, x k * eval x (pderiv k p) = (ℓ : ℂ) * eval x p := by
  have h := congrArg (eval x) hp.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast] at h
  exact h

theorem rowOrthC {o : Fin 3 → Fin 3 → ℝ} (ho : orth o) (m k : Fin 3) :
    ((o m 0 : ℝ) : ℂ) * ((o k 0 : ℝ) : ℂ) + ((o m 1 : ℝ) : ℂ) * ((o k 1 : ℝ) : ℂ) +
      ((o m 2 : ℝ) : ℂ) * ((o k 2 : ℝ) : ℂ) = if m = k then 1 else 0 := by
  have h1 : (Matrix.of o).transpose * Matrix.of o = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply] using ho i j
  have h2 : Matrix.of o * (Matrix.of o).transpose = 1 := mul_eq_one_comm.1 h1
  have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M m k) h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_three] at h3
  split_ifs with hmk
  · rw [if_pos hmk] at h3; exact_mod_cast h3
  · rw [if_neg hmk] at h3; exact_mod_cast h3

theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide

theorem core (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : R3) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, pderiv i (pderiv i p)) = 0) (j : Fin 3)
    (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) :
    eval (pt o) (Omega ν (realise j p)) = -(((ℓ : ℂ) * ((ℓ : ℂ) + 1))) * eval (pt o) (realise j p) := by
  have h01 := eval_Lop_Lop_realise ν 0 1 ne01 (fun o ho t => cR_orth01 o ho t) (fun H o ho => bridge01 ν H o ho)
    j o ho p
  have h02 := eval_Lop_Lop_realise ν 0 2 ne02 (fun o ho t => cR_orth02 o ho t) (fun H o ho => bridge02 ν H o ho)
    j o ho p
  have h12 := eval_Lop_Lop_realise ν 1 2 ne12 (fun o ho t => cR_orth12 o ho t) (fun H o ho => bridge12 ν H o ho)
    j o ho p
  rw [Omega, map_add, map_add, h01, h02, h12, eval_realise]
  have R' := rowOrthC ho
  have R00 := R' 0 0; have R01 := R' 0 1; have R02 := R' 0 2; have R10 := R' 1 0; have R11 := R' 1 1
  have R12 := R' 1 2; have R20 := R' 2 0; have R21 := R' 2 1; have R22 := R' 2 2
  simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] at R00 R01 R02 R10 R11 R12 R20 R21 R22
  have hcast : ((ℓ - 1 : ℕ) : ℂ) * (ℓ : ℂ) = (ℓ : ℂ) * ℓ - ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h; simp
    · rw [Nat.cast_sub h]; push_cast; ring
  rcases fin3_cases j with hj | hj | hj <;> subst hj
  · have E1 := euler1 hp (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ))
    have E2 := fun k : Fin 3 => euler1 (hp.pderiv (i := k)) (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ))
    have Hm := congrArg (eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ))) hharm
    simp only [Fin.sum_univ_three, map_add, map_zero] at E1 E2 Hm
    simp only [g₂, vel, acc, cR_zero 0 1 ne01, cR_zero 0 2 ne02, cR_zero 1 2 ne12, f01, f02, f10, f12, f20, f21,
      if_true, if_false, Fin.sum_univ_three, Real.sin_zero, Real.cos_zero, pt]
    push_cast
    linear_combination eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 0 (pderiv 0 p)) * R00 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 0 (pderiv 1 p)) * R01 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 0 (pderiv 2 p)) * R02 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 1 (pderiv 0 p)) * R10 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 1 (pderiv 1 p)) * R11 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 1 (pderiv 2 p)) * R12 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 2 (pderiv 0 p)) * R20 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 2 (pderiv 1 p)) * R21 + eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) (pderiv 2 (pderiv 2 p)) * R22 + Hm - ((o 0 0 : ℝ) : ℂ) * E2 0 - ((o 1 0 : ℝ) : ℂ) * E2 1 - ((o 2 0 : ℝ) : ℂ) * E2 2 - ((((ℓ - 1 : ℕ) : ℂ)) + 2) * E1 - eval (fun a : Fin 3 => ((o a 0 : ℝ) : ℂ)) p * hcast
  · have E1 := euler1 hp (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ))
    have E2 := fun k : Fin 3 => euler1 (hp.pderiv (i := k)) (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ))
    have Hm := congrArg (eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ))) hharm
    simp only [Fin.sum_univ_three, map_add, map_zero] at E1 E2 Hm
    simp only [g₂, vel, acc, cR_zero 0 1 ne01, cR_zero 0 2 ne02, cR_zero 1 2 ne12, f01, f02, f10, f12, f20, f21,
      if_true, if_false, Fin.sum_univ_three, Real.sin_zero, Real.cos_zero, pt]
    push_cast
    linear_combination eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 0 (pderiv 0 p)) * R00 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 0 (pderiv 1 p)) * R01 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 0 (pderiv 2 p)) * R02 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 1 (pderiv 0 p)) * R10 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 1 (pderiv 1 p)) * R11 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 1 (pderiv 2 p)) * R12 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 2 (pderiv 0 p)) * R20 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 2 (pderiv 1 p)) * R21 + eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) (pderiv 2 (pderiv 2 p)) * R22 + Hm - ((o 0 1 : ℝ) : ℂ) * E2 0 - ((o 1 1 : ℝ) : ℂ) * E2 1 - ((o 2 1 : ℝ) : ℂ) * E2 2 - ((((ℓ - 1 : ℕ) : ℂ)) + 2) * E1 - eval (fun a : Fin 3 => ((o a 1 : ℝ) : ℂ)) p * hcast
  · have E1 := euler1 hp (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ))
    have E2 := fun k : Fin 3 => euler1 (hp.pderiv (i := k)) (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ))
    have Hm := congrArg (eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ))) hharm
    simp only [Fin.sum_univ_three, map_add, map_zero] at E1 E2 Hm
    simp only [g₂, vel, acc, cR_zero 0 1 ne01, cR_zero 0 2 ne02, cR_zero 1 2 ne12, f01, f02, f10, f12, f20, f21,
      if_true, if_false, Fin.sum_univ_three, Real.sin_zero, Real.cos_zero, pt]
    push_cast
    linear_combination eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 0 (pderiv 0 p)) * R00 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 0 (pderiv 1 p)) * R01 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 0 (pderiv 2 p)) * R02 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 1 (pderiv 0 p)) * R10 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 1 (pderiv 1 p)) * R11 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 1 (pderiv 2 p)) * R12 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 2 (pderiv 0 p)) * R20 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 2 (pderiv 1 p)) * R21 + eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) (pderiv 2 (pderiv 2 p)) * R22 + Hm - ((o 0 2 : ℝ) : ℂ) * E2 0 - ((o 1 2 : ℝ) : ℂ) * E2 1 - ((o 2 2 : ℝ) : ℂ) * E2 2 - ((((ℓ - 1 : ℕ) : ℂ)) + 2) * E1 - eval (fun a : Fin 3 => ((o a 2 : ℝ) : ℂ)) p * hcast

end

end WsE.O5

open MvPolynomial in
theorem solution
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) (j : Fin 3) (d : ℕ)
    (o : Fin 3 → Fin 3 → ℝ) (ho : (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ω : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun P => (act ν 0 1 (act ν 0 1 P - act ν 1 0 P) - act ν 1 0 (act ν 0 1 P - act ν 1 0 P)) +
        (act ν 0 2 (act ν 0 2 P - act ν 2 0 P) - act ν 2 0 (act ν 0 2 P - act ν 2 0 P)) +
        (act ν 1 2 (act ν 1 2 P - act ν 2 1 P) - act ν 2 1 (act ν 1 2 P - act ν 2 1 P))
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
        (Ω ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ d *
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) =
      -(((ℓ : ℂ) * ((ℓ : ℂ) + 1))) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ d *
            MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by
  intro act' Ω'
  have hact : ∀ (c e : Fin 3) (P : WsE.O5.R9),
      WsE.O5.act ν c e ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
        (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det *
          WsE.O5.act ν c e P :=
    fun c e P => LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul ν c e P
  set D : WsE.O5.R9 := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det
    with hD
  have hLop : ∀ (c e : Fin 3) (P : WsE.O5.R9), WsE.O5.Lop ν c e (D * P) = D * WsE.O5.Lop ν c e P := by
    intro c e P
    simp only [WsE.O5.Lop, hact, mul_sub]
  have hLopPow : ∀ (c e : Fin 3) (n : ℕ) (P : WsE.O5.R9),
      WsE.O5.Lop ν c e (D ^ n * P) = D ^ n * WsE.O5.Lop ν c e P := by
    intro c e n
    induction n with
    | zero => intro P; simp
    | succ n ih => intro P; rw [pow_succ, mul_assoc, ih, hLop, ← mul_assoc]
  have hΩ : WsE.O5.Omega ν (D ^ d * WsE.O5.realise j p) = D ^ d * WsE.O5.Omega ν (WsE.O5.realise j p) := by
    simp only [WsE.O5.Omega, hLopPow, mul_add]
  show MvPolynomial.eval (WsE.O5.pt o) (WsE.O5.Omega ν (D ^ d * WsE.O5.realise j p)) =
    -(((ℓ : ℂ) * ((ℓ : ℂ) + 1))) * MvPolynomial.eval (WsE.O5.pt o) (D ^ d * WsE.O5.realise j p)
  rw [hΩ, map_mul, map_mul, WsE.O5.core ν ℓ p hp hharm j o ho]
  ring

end S_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic (solution)
