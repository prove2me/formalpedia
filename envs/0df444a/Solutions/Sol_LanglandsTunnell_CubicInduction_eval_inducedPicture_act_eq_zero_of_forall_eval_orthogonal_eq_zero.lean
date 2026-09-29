-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/586d2317-ced7-5bf8-a384-4aa668818df2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero

set_option autoImplicit false

namespace WsC
namespace O6

open MvPolynomial

noncomputable section

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

theorem hasDerivAt_eval {σ : Type} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (x : ℝ → σ → ℂ) (x' : σ → ℂ) (t₀ : ℝ) (hx : ∀ k, HasDerivAt (fun t => x t k) (x' k) t₀) :
    HasDerivAt (fun t => eval (x t) P) (∑ k, eval (x t₀) (pderiv k P) * x' k) t₀ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const t₀ a
  | add p q hp hq =>
    simp only [map_add]
    refine (hp.fun_add hq).congr_deriv ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  | mul_X p k hp =>
    simp only [map_mul, eval_X]
    refine (hp.fun_mul (hx k)).congr_deriv ?_
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

def oR (i m : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a j => if a = i then Real.cos t * o i j + Real.sin t * o m j
    else if a = m then -Real.sin t * o i j + Real.cos t * o m j else o a j

theorem oR_zero (i m : Fin 3) (o : Fin 3 → Fin 3 → ℝ) : oR i m o 0 = o := by
  funext a j
  simp only [oR, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero, neg_zero, zero_add]
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2]
  · rfl

theorem oR_orth (i m : Fin 3) (him : i ≠ m) (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (t : ℝ) :
    orth (oR i m o t) := by
  intro p q
  rw [← ho p q, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hpt : ∀ a, oR i m o t a p * oR i m o t a q - o a p * o a q =
      (if a = i then (Real.cos t * o i p + Real.sin t * o m p) * (Real.cos t * o i q + Real.sin t * o m q)
        - o i p * o i q else 0) +
      (if a = m then (-Real.sin t * o i p + Real.cos t * o m p) * (-Real.sin t * o i q + Real.cos t * o m q)
        - o m p * o m q else 0) := by
    intro a
    simp only [oR]
    by_cases hai : a = i
    · have ham : a ≠ m := hai ▸ (hai.symm ▸ him)
      simp [hai, him]
    · by_cases ham : a = m
      · simp [ham, him.symm]
      · simp [hai, ham]
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  linear_combination (o i p * o i q + o m p * o m q) * Real.cos_sq_add_sin_sq t

theorem hasDerivAt_oR (i m : Fin 3) (o : Fin 3 → Fin 3 → ℝ) (a j : Fin 3) :
    HasDerivAt (fun t => ((oR i m o t a j : ℝ) : ℂ))
      (((if a = i then o m j else if a = m then -o i j else 0 : ℝ) : ℂ)) 0 := by
  apply HasDerivAt.ofReal_comp
  simp only [oR]
  split_ifs with h1 h2
  · have := ((Real.hasDerivAt_cos 0).mul_const (o i j)).fun_add ((Real.hasDerivAt_sin 0).mul_const (o m j))
    simpa using this
  · have := ((Real.hasDerivAt_sin 0).fun_neg.mul_const (o i j)).fun_add ((Real.hasDerivAt_cos 0).mul_const (o m j))
    simpa [neg_mul] using this
  · exact hasDerivAt_const 0 (o a j)

theorem tangential (P : R9)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (pt o) P = 0)
    (o : Fin 3 → Fin 3 → ℝ) (ho : orth o) (i m : Fin 3) (him : i ≠ m) :
    ∑ j : Fin 3, (((o m j : ℝ) : ℂ) * eval (pt o) (pderiv (i, j) P) -
      ((o i j : ℝ) : ℂ) * eval (pt o) (pderiv (m, j) P)) = 0 := by
  classical
  set x : ℝ → Fin 3 × Fin 3 → ℂ := fun t => pt (oR i m o t) with hx
  set x' : Fin 3 × Fin 3 → ℂ := fun aj => ((if aj.1 = i then o m aj.2 else if aj.1 = m then -o i aj.2 else 0 : ℝ) : ℂ)
    with hx'
  have hxd : ∀ k, HasDerivAt (fun t => x t k) (x' k) 0 := fun k => hasDerivAt_oR i m o k.1 k.2
  have hD := hasDerivAt_eval P x x' 0 hxd
  have hzero : (fun t => eval (x t) P) = fun _ => 0 := by
    funext t; exact hP _ (oR_orth i m him o ho t)
  rw [hzero] at hD
  have h0 := (hasDerivAt_const (0 : ℝ) (0 : ℂ)).unique hD
  have hx0 : x 0 = pt o := by simp only [hx, oR_zero]
  rw [hx0, Fintype.sum_prod_type] at h0
  have hpt : ∀ a : Fin 3, ∑ j : Fin 3, eval (pt o) (pderiv (a, j) P) * x' (a, j) =
      (if a = i then ∑ j : Fin 3, ((o m j : ℝ) : ℂ) * eval (pt o) (pderiv (i, j) P) else 0) +
      (if a = m then ∑ j : Fin 3, -(((o i j : ℝ) : ℂ) * eval (pt o) (pderiv (m, j) P)) else 0) := by
    intro a
    by_cases hai : a = i
    · rw [if_pos hai, if_neg (fun h => him (hai.symm.trans h)), add_zero, hai]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [hx', mul_comm]
    · by_cases ham : a = m
      · rw [if_neg hai, if_pos ham, zero_add, ham]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp [hx', him.symm, mul_comm]
      · rw [if_neg hai, if_neg ham, add_zero]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        simp [hx', hai, ham]
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at h0
  simp only [Finset.mem_univ, if_true, ← Finset.sum_add_distrib] at h0
  rw [h0]
  refine Finset.sum_congr rfl (fun j _ => by ring)

theorem lt01 : (0 : Fin 3) < 1 := by decide
theorem lt02 : (0 : Fin 3) < 2 := by decide
theorem lt12 : (1 : Fin 3) < 2 := by decide
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide

theorem main
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0)
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
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (act ν c d P) = 0 := by
  intro act'
  show eval (pt o) (act ν c d P) = 0
  have h0 : eval (pt o) P = 0 := hP o ho
  have D10 := tangential P hP o ho 1 0 (by decide)
  have D20 := tangential P hP o ho 2 0 (by decide)
  have D21 := tangential P hP o ho 2 1 (by decide)
  simp only [Fin.sum_univ_three] at D10 D20 D21
  simp only [act, Fin.sum_univ_three, map_add, map_mul, map_sum, map_neg, map_zero, eval_X, eval_C,
    lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false, h0, mul_zero, zero_add,
    zero_mul, add_zero]
  simp only [pt] at D10 D20 D21 ⊢
  linear_combination (((o 1 c : ℝ) : ℂ) * ((o 0 d : ℝ) : ℂ)) * D10 + (((o 2 c : ℝ) : ℂ) * ((o 0 d : ℝ) : ℂ)) * D20 +
    (((o 2 c : ℝ) : ℂ) * ((o 1 d : ℝ) : ℂ)) * D21

end

end WsC.O6

theorem solution
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0)
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
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (act ν c d P) = 0 := by
  exact WsC.O6.main ν c d P hP o ho

end S_LanglandsTunnell_CubicInduction_eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero (solution)
