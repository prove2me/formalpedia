-- Prove2me | solution 1 for NumStochOpt.Bounds.eq_2_48_2_49_simple_recourse_separable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:29:27.694319+00:00
-- url     : https://prove2.me/submissions/ea2e6c0c-ff19-47e2-a1fe-c409e46ec446

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse

set_option autoImplicit false

namespace NumStochOpt.Bounds.P2c67119f

open Matrix

lemma W_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι ⊕ ι → ℝ) (j : ι) :
    (simpleRecourseMatrix ι *ᵥ y) j = y (Sum.inl j) - y (Sum.inr j) := by
  simp [simpleRecourseMatrix, Matrix.fromCols_mulVec, Matrix.neg_mulVec, sub_eq_add_neg]

lemma q_dot {ι : Type*} [Fintype ι] (qp qm : ι → ℝ) (y : ι ⊕ ι → ℝ) :
    Sum.elim qp qm ⬝ᵥ y = ∑ j, (qp j * y (Sum.inl j) + qm j * y (Sum.inr j)) := by
  simp [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib]

lemma one_row (qp qm χ h a b : ℝ) (hq : 0 ≤ qp + qm) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a - b = h - χ) : simpleRecourseCost qp qm χ h ≤ qp * a + qm * b := by
  unfold simpleRecourseCost
  split_ifs with hc
  · have : a = (h - χ) + b := by linarith
    subst this
    nlinarith [mul_nonneg hq hb]
  · have : b = a - (h - χ) := by linarith
    subst this
    nlinarith [mul_nonneg hq ha]

lemma one_row_eq (qp qm χ h : ℝ) :
    simpleRecourseCost qp qm χ h = qp * max (h - χ) 0 + qm * max (-(h - χ)) 0 := by
  unfold simpleRecourseCost
  split_ifs with hc
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

end NumStochOpt.Bounds.P2c67119f

open Matrix in
theorem solution {ι ν : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ν] (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j) (T : Matrix ι ν ℝ) (h : ι → ℝ)
    (x : ν → ℝ) :
    NumStochOpt.Bounds.recourseCost (NumStochOpt.Bounds.simpleRecourseMatrix ι) (Sum.elim qp qm) h T x =
      ((∑ j, NumStochOpt.Bounds.simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (h j) : ℝ) : EReal) := by
  open NumStochOpt.Bounds NumStochOpt.Bounds.P2c67119f in
  unfold recourseCost
  apply le_antisymm
  · let y : ι ⊕ ι → ℝ := Sum.elim (fun j => max (h j - (T *ᵥ x) j) 0)
      (fun j => max (-(h j - (T *ᵥ x) j)) 0)
    have hy : y ∈ {y : ι ⊕ ι → ℝ | 0 ≤ y ∧ simpleRecourseMatrix ι *ᵥ y = h - T *ᵥ x} := by
      refine ⟨?_, ?_⟩
      · intro k
        cases k with
        | inl j => simp [y]
        | inr j => simp [y]
      · funext j
        rw [W_mulVec]
        simp only [y, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
        rcases le_total 0 (h j - (T *ᵥ x) j) with hc | hc
        · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
        · rw [max_eq_right hc, max_eq_left (by linarith)]; ring
    refine (iInf₂_le y hy).trans (le_of_eq ?_)
    congr 1
    rw [q_dot]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_row_eq]
    rfl
  · refine le_iInf₂ fun y hy => ?_
    obtain ⟨hy0, hyW⟩ := hy
    rw [EReal.coe_le_coe_iff, q_dot]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := congrFun hyW j
    rw [W_mulVec] at hj
    exact one_row _ _ _ _ _ _ (hq j) (hy0 _) (hy0 _) (by simpa using hj)
