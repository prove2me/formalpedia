-- Prove2me | solution 1 for LogSobolevMC.Entropy.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:26:05.499705+00:00
-- url     : https://prove2.me/submissions/bc242cf2-8dcf-4755-9bdb-b5f7c2e07cad

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting



namespace LogSobolevMC.Entropy

open scoped BigOperators

/-- `2(u-1)/(u+1) ≤ log u` for `u ≥ 1`. -/
lemma log_ge_two_mul_sub_div (u : ℝ) (hu : 1 ≤ u) : 2 * (u - 1) / (u + 1) ≤ Real.log u := by
  have hd : ∀ v : ℝ, 0 < v →
      HasDerivAt (fun v => Real.log v - 2 * (v - 1) / (v + 1)) (1 / v - 4 / (v + 1) ^ 2) v := by
    intro v hv
    have h1 := Real.hasDerivAt_log hv.ne'
    have h2 : HasDerivAt (fun v : ℝ => 2 * (v - 1) / (v + 1)) (4 / (v + 1) ^ 2) v := by
      have := (((hasDerivAt_id v).sub_const 1).const_mul 2).div ((hasDerivAt_id v).add_const 1)
        (by simp; linarith)
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    exact HasDerivAt.congr_deriv (h1.sub h2) (by rw [one_div])
  have hmono : MonotoneOn (fun v => Real.log v - 2 * (v - 1) / (v + 1)) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · exact Real.continuousOn_log.mono (fun v hv => by
          simp only [Set.mem_Ici] at hv; simp; linarith)
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro v hv; simp only [Set.mem_Ici] at hv; linarith
    · intro v hv
      rw [interior_Ici] at hv
      exact (hd v (by simp only [Set.mem_Ioi] at hv; linarith)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      simp only [Set.mem_Ioi] at hv
      rw [(hd v (by linarith)).deriv]
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [sq_nonneg (v - 1)]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp at this
  linarith

/-- For `s ≥ r > 0`: `2(s-r)/(s+r) ≤ log s - log r`. -/
lemma log_sub_log_ge (s r : ℝ) (hr : 0 < r) (hsr : r ≤ s) :
    2 * (s - r) / (s + r) ≤ Real.log s - Real.log r := by
  have hs : 0 < s := lt_of_lt_of_le hr hsr
  rw [← Real.log_div hs.ne' hr.ne']
  have := log_ge_two_mul_sub_div (s / r) ((le_div_iff₀ hr).2 (by linarith))
  convert this using 1
  field_simp

lemma scalar1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * ((Real.sqrt a - Real.sqrt b) * Real.sqrt a) ≤ (Real.log a - Real.log b) * a := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ a = s ^ 2 := ⟨Real.sqrt a, Real.sqrt_pos.2 ha, (Real.sq_sqrt ha.le).symm⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ b = r ^ 2 := ⟨Real.sqrt b, Real.sqrt_pos.2 hb, (Real.sq_sqrt hb.le).symm⟩
  rw [Real.sqrt_sq hs.le, Real.sqrt_sq hr.le, Real.log_pow, Real.log_pow]
  -- need: 2 (s - r) s ≤ 2 (log s - log r) s^2, i.e. (s - r)/s ≤ log s - log r
  have h1 : 1 - r / s ≤ Real.log (s / r) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hs hr)
    rwa [inv_div] at this
  rw [Real.log_div hs.ne' hr.ne'] at h1
  have h2 : (s - r) * s ≤ (Real.log s - Real.log r) * s ^ 2 := by
    have : (s - r) * s = (1 - r / s) * s ^ 2 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  push_cast
  nlinarith

lemma scalar2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4 * (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (Real.log a - Real.log b) * (a - b) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ a = s ^ 2 := ⟨Real.sqrt a, Real.sqrt_pos.2 ha, (Real.sq_sqrt ha.le).symm⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ b = r ^ 2 := ⟨Real.sqrt b, Real.sqrt_pos.2 hb, (Real.sq_sqrt hb.le).symm⟩
  rw [Real.sqrt_sq hs.le, Real.sqrt_sq hr.le, Real.log_pow, Real.log_pow]
  push_cast
  rcases le_total r s with h | h
  · have := log_sub_log_ge s r hr h
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 h)]
  · have := log_sub_log_ge r s hs h
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 h)]

lemma dirichlet_eq_double {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K) (π : V → ℝ) (g h : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π g h =
      ∑ x, ∑ y, π x * K x y * ((g x - g y) * h x) := by
  unfold LogSobolevMC.ChiSquare.dirichlet
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec, dotProduct]
  have : g x - ∑ y, K x y * g y = ∑ y, K x y * (g x - g y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hK.2 x, one_mul]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma double_sum_symm {V : Type*} [Fintype V] (w : V → V → ℝ) (hw : ∀ x y, w x y = w y x)
    (F : V → V → ℝ) :
    2 * (∑ x, ∑ y, w x y * F x y) = ∑ x, ∑ y, w x y * (F x y + F y x) := by
  have : ∑ x, ∑ y, w x y * F x y = ∑ x, ∑ y, w x y * F y x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [hw]
  rw [two_mul]
  nth_rewrite 2 [this]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _
  ring

theorem lemma_2_7_core {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    2 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
        LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f ∧
      (MarkovMixing.DetailedBalance K π →
        4 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
          LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f) := by
  have hw : ∀ x y, 0 ≤ π x * K x y := fun x y => mul_nonneg (hπpos x).le (hK.1 x y)
  rw [dirichlet_eq_double K hK, dirichlet_eq_double K hK]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro y _
    rw [← mul_assoc, mul_comm (2:ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (scalar1 (f x) (f y) (hf x) (hf y)) (hw x y)
  · intro hdb
    have hsym : ∀ x y, π x * K x y = π y * K y x := hdb
    have e1 := double_sum_symm (fun x y => π x * K x y) hsym
      (fun x y => (Real.sqrt (f x) - Real.sqrt (f y)) * Real.sqrt (f x))
    have e2 := double_sum_symm (fun x y => π x * K x y) hsym
      (fun x y => (Real.log (f x) - Real.log (f y)) * f x)
    beta_reduce at e1 e2
    have key : 4 * (∑ x, ∑ y, π x * K x y *
        ((Real.sqrt (f x) - Real.sqrt (f y)) * Real.sqrt (f x) +
          (Real.sqrt (f y) - Real.sqrt (f x)) * Real.sqrt (f y))) ≤
        ∑ x, ∑ y, π x * K x y *
        ((Real.log (f x) - Real.log (f y)) * f x + (Real.log (f y) - Real.log (f x)) * f y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro y _
      rw [← mul_assoc, mul_comm (4:ℝ), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hw x y)
      have := scalar2 (f x) (f y) (hf x) (hf y)
      nlinarith
    linarith

end LogSobolevMC.Entropy

open LogSobolevMC.Entropy


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    2 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
        LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f ∧
      (MarkovMixing.DetailedBalance K π →
        4 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
          LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f) := by
  exact lemma_2_7_core K hK π hπ hπpos f hf
