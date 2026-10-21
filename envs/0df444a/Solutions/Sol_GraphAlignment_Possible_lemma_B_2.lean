-- Prove2me | solution 1 for GraphAlignment.Possible.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:03:33.182283+00:00
-- url     : https://prove2.me/submissions/7c0f38a3-bc17-4d93-90ed-95fb94c650f5

import Mathlib
import Definitions.Def_GraphAlignment_Possible_Setting

set_option autoImplicit false

open GraphAlignment.Possible

/-- weight of a path `x, τ 0, …, τ (N-1), y` in the weighted graph `F`. -/
def chainW {X : Type} (F : X → X → ℝ) : (N : ℕ) → X → (Fin N → X) → X → ℝ
  | 0, x, _, y => F x y
  | N + 1, x, τ, y => F x (τ 0) * chainW F N (τ 0) (Fin.tail τ) y

lemma chainW_sum {X : Type} [Fintype X] [DecidableEq X] (F : Matrix X X ℝ) :
    ∀ (N : ℕ) (x y : X), ∑ τ : Fin N → X, chainW (fun a b => F a b) N x τ y = (F ^ (N + 1)) x y := by
  intro N
  induction N with
  | zero => intro x y; simp [chainW]
  | succ N ih =>
    intro x y
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => X)), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, chainW, Fin.cons_zero, Fin.tail_cons]
    simp_rw [← Finset.mul_sum, ih]
    rw [pow_succ' F (N + 1), Matrix.mul_apply]

lemma chainW_cyc {X : Type} (F : X → X → ℝ) (y : X) :
    ∀ (N : ℕ) (ω : Fin (N + 1) → X), chainW F N (ω 0) (Fin.tail ω) y =
      (∏ i : Fin N, F (ω i.castSucc) (ω i.succ)) * F (ω (Fin.last N)) y := by
  intro N
  induction N with
  | zero => intro ω; simp [chainW]
  | succ N ih =>
    intro ω
    have h := ih (Fin.tail ω)
    rw [chainW, show Fin.tail ω 0 = ω 1 from rfl]
    have h' : chainW F N (ω 1) (Fin.tail (Fin.tail ω)) y = chainW F N ((Fin.tail ω) 0) (Fin.tail (Fin.tail ω)) y := rfl
    rw [h', h, Fin.prod_univ_succ]
    simp only [Fin.tail, Fin.succ_last, Fin.castSucc_zero]
    rw [show ω (Fin.succ 0) = ω 1 from rfl, mul_assoc]
    congr 1

lemma cyc_sum {X : Type} [Fintype X] [DecidableEq X] (F : Matrix X X ℝ) (N : ℕ) :
    ∑ ω : Fin (N + 1) → X, ∏ i : Fin (N + 1), F (ω i) (ω (i + 1)) = (F ^ (N + 1)).trace := by
  have h1 : ∀ ω : Fin (N + 1) → X, ∏ i : Fin (N + 1), F (ω i) (ω (i + 1)) =
      chainW (fun a b => F a b) N (ω 0) (Fin.tail ω) (ω 0) := by
    intro ω
    rw [chainW_cyc, Fin.prod_univ_castSucc]
    simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]
  simp_rw [h1]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => X)), Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.tail_cons]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [chainW_sum]
  simp

lemma trace_pow_two_state (K : Matrix Bool Bool ℝ) (T D r : ℝ)
    (hT : K true true + K false false = T)
    (hD : K false false * K true true - K false true * K true false = D)
    (hr : r ^ 2 = T ^ 2 - 4 * D) (N : ℕ) :
    (K ^ N).trace = ((T + r) / 2) ^ N + ((T - r) / 2) ^ N := by
  have hCH : K * K = T • K - D • (1 : Matrix Bool Bool ℝ) := by
    subst hT hD
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply] <;> ring
  have hsum : (T + r) / 2 + (T - r) / 2 = T := by ring
  have hprod : (T + r) / 2 * ((T - r) / 2) = D := by nlinarith [hr]
  have key : ∀ N : ℕ, (K ^ N).trace = ((T + r) / 2) ^ N + ((T - r) / 2) ^ N ∧
      (K ^ (N + 1)).trace = ((T + r) / 2) ^ (N + 1) + ((T - r) / 2) ^ (N + 1) := by
    intro N
    induction N with
    | zero =>
      refine ⟨by simp [Matrix.trace]; norm_num, ?_⟩
      simp only [pow_one, zero_add]
      rw [Matrix.trace, Fintype.sum_bool]
      simp only [Matrix.diag]
      linarith [hT]
    | succ N ih =>
      refine ⟨ih.2, ?_⟩
      have e : K ^ (N + 2) = T • K ^ (N + 1) - D • K ^ N := by
        rw [pow_add K N 2, pow_two, hCH]
        simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
        rw [pow_succ]
      rw [e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2]
      simp only [smul_eq_mul]
      generalize (T + r) / 2 = u at *
      generalize (T - r) / 2 = v at *
      rw [← hsum, ← hprod]
      ring
  exact (key N).1

theorem solution (n : ℕ) (q s t : ℝ) (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (hσ : 0 < q * (s - q)) (ht : 0 < t) :
    let T : ℝ := q * s * (Real.exp t - 1) + 1
    let D : ℝ := q * (s - q) * (Real.exp t - 1)
    let W : (Fin (n + 1) → Bool × Bool) → ℝ := fun ω =>
      ∑ i : Fin (n + 1), (if (ω i).1 && (ω (i + 1)).2 then (1 : ℝ) else 0)
    ∑ ω : Fin (n + 1) → Bool × Bool, (∏ i, pLaw q s (ω i)) * Real.exp (t * W ω) =
      ((T + Real.sqrt (T ^ 2 - 4 * D)) / 2) ^ (n + 1) +
        ((T - Real.sqrt (T ^ 2 - 4 * D)) / 2) ^ (n + 1) := by
  intro T D W
  -- the 4x4 transfer matrix
  obtain ⟨F, hFe⟩ : ∃ F : Matrix (Bool × Bool) (Bool × Bool) ℝ, ∀ x y,
      F x y = pLaw q s x * Real.exp (t * (if x.1 && y.2 then (1 : ℝ) else 0)) :=
    ⟨Matrix.of fun x y => pLaw q s x * Real.exp (t * (if x.1 && y.2 then (1 : ℝ) else 0)),
      fun _ _ => rfl⟩
  have h1 : ∀ ω : Fin (n + 1) → Bool × Bool,
      (∏ i, pLaw q s (ω i)) * Real.exp (t * W ω) = ∏ i : Fin (n + 1), F (ω i) (ω (i + 1)) := by
    intro ω
    simp only [hFe, W, Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [cyc_sum F n]
  -- factor F = U * V
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Bool × Bool) Bool ℝ, ∀ x a,
      U x a = if x.1 = a then pLaw q s x else 0 :=
    ⟨Matrix.of fun x a => if x.1 = a then pLaw q s x else 0, fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Matrix Bool (Bool × Bool) ℝ, ∀ a y,
      V a y = Real.exp (t * (if a && y.2 then (1 : ℝ) else 0)) :=
    ⟨Matrix.of fun a y => Real.exp (t * (if a && y.2 then (1 : ℝ) else 0)), fun _ _ => rfl⟩
  have hF : F = U * V := by
    ext x y
    rw [hFe, Matrix.mul_apply, Fintype.sum_bool, hU, hU, hV, hV]
    rcases hx : x.1 <;> simp
  have hpow : ∀ m : ℕ, (U * V) ^ (m + 1) = U * ((V * U) ^ m * V) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ (V * U) m]; simp only [Matrix.mul_assoc]
  have htr : (F ^ (n + 1)).trace = ((V * U) ^ (n + 1)).trace := by
    rw [hF, hpow, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]
  rw [htr]
  set K := V * U with hK
  have hKe : ∀ a b : Bool, K a b = ∑ c : Bool, V a (b, c) * pLaw q s (b, c) := by
    intro a b
    simp only [hK, Matrix.mul_apply, hV, hU, Fintype.sum_prod_type, Fintype.sum_bool]
    cases b <;> simp
  set x : ℝ := Real.exp t - 1 with hx
  have hx0 : 0 < x := by
    have : 1 < Real.exp t := by simpa using Real.exp_lt_exp.mpr ht
    linarith
  have hex : Real.exp t = x + 1 := by rw [hx]; ring
  have k_tt : K true true = q * (1 - s) + q * s * (x + 1) := by
    rw [hKe]; simp [hV, pLaw, Fintype.sum_bool, hex]; ring
  have k_ff : K false false = 1 - q := by
    rw [hKe]; simp [hV, pLaw, Fintype.sum_bool]; ring
  have k_ft : K false true = q := by
    rw [hKe]; simp [hV, pLaw, Fintype.sum_bool]; ring
  have k_tf : K true false = 1 - 2 * q + q * s + q * (1 - s) * (x + 1) := by
    rw [hKe]; simp [hV, pLaw, Fintype.sum_bool, hex]; ring
  have hT : K true true + K false false = T := by
    rw [k_tt, k_ff]; simp only [T]; ring
  have hD : K false false * K true true - K false true * K true false = D := by
    rw [k_tt, k_ff, k_ft, k_tf]; simp only [D]; ring
  have hnn : 0 ≤ T ^ 2 - 4 * D := by
    have : T ^ 2 - 4 * D = (1 - q * s * x) ^ 2 + 4 * q ^ 2 * x := by
      simp only [T, D]; ring
    rw [this]; positivity
  exact trace_pow_two_state K T D _ hT hD (Real.sq_sqrt hnn) (n + 1)
