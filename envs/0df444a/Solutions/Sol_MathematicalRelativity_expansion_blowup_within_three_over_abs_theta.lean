-- Prove2me | solution 1 for MathematicalRelativity.expansion_blowup_within_three_over_abs_theta
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:16:02.693774+00:00
-- url     : https://prove2.me/submissions/bb7795c9-b4d0-4ecf-bc5b-843eb6687f5a

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem W3b_MathematicalRelativity_trace_sq_le_card_mul_trace_transpose_mul
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.trace) ^ 2 ≤ (n : ℝ) * (A.transpose * A).trace := by
  have h1 : (A.trace) ^ 2 ≤ (n : ℝ) * ∑ i, A i i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => A i i)
    simpa [Matrix.trace] using this
  have h2 : ∑ i, A i i ^ 2 ≤ (A.transpose * A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.single_le_sum (f := fun j => A j i * A j i)
      (fun j _ => mul_self_nonneg (A j i)) (Finset.mem_univ i)
    simpa [sq] using this
  calc (A.trace) ^ 2 ≤ (n : ℝ) * ∑ i, A i i ^ 2 := h1
    _ ≤ (n : ℝ) * (A.transpose * A).trace := by gcongr

theorem W3b_MathematicalRelativity_blowup (k T theta0 : ℝ) (theta : ℝ → ℝ) (hk : 0 < k)
    (hneg : theta0 < 0) (hinit : theta 0 = theta0)
    (hdiff : ∀ t ∈ Set.Ico (0:ℝ) T, DifferentiableAt ℝ theta t)
    (hode : ∀ t ∈ Set.Ico (0:ℝ) T, deriv theta t ≤ - (theta t) ^ 2 / k) :
    T ≤ k / (-theta0) := by
  by_contra hT
  push_neg at hT
  set t1 := k / (-theta0) with ht1
  have ht1pos : 0 < t1 := div_pos hk (neg_pos.mpr hneg)
  have hsub : Set.Icc 0 t1 ⊆ Set.Ico 0 T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hT⟩
  have hcont : ContinuousOn theta (Set.Icc 0 t1) := fun t ht =>
    (hdiff t (hsub ht)).continuousAt.continuousWithinAt
  have hanti : AntitoneOn theta (Set.Icc 0 t1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t1) hcont
    · intro t ht
      exact (hdiff t (hsub (interior_subset ht))).differentiableWithinAt
    · intro t ht
      have h1 := hode t (hsub (interior_subset ht))
      have h2 : 0 ≤ theta t ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
      have h3 : -theta t ^ 2 / k = -(theta t ^ 2 / k) := by ring
      linarith
  have hneg' : ∀ t ∈ Set.Icc 0 t1, theta t < 0 := fun t ht => by
    have := hanti ⟨le_refl 0, ht1pos.le⟩ ht ht.1
    rw [hinit] at this
    linarith
  have hmono : MonotoneOn (fun t => 1 / theta t - t / k) (Set.Icc 0 t1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t1)
    · exact (continuousOn_const.div hcont (fun t ht => (hneg' t ht).ne)).sub
        (continuousOn_id.div_const k)
    · intro t ht
      have hti := interior_subset ht
      have hd := (hdiff t (hsub hti)).hasDerivAt
      exact (((hasDerivAt_const t (1 : ℝ)).div hd (hneg' t hti).ne).sub
        ((hasDerivAt_id' t).div_const k)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hti := interior_subset ht
      have hd := (hdiff t (hsub hti)).hasDerivAt
      have hθ := hneg' t hti
      have hθ2 : 0 < theta t ^ 2 := by nlinarith
      have hg : HasDerivAt (fun y => 1 / theta y - y / k)
          ((0 * theta t - 1 * deriv theta t) / theta t ^ 2 - 1 / k) t :=
        ((hasDerivAt_const t (1 : ℝ)).div hd hθ.ne).sub ((hasDerivAt_id' t).div_const k)
      rw [hg.deriv]
      have key : 1 / k ≤ (0 * theta t - 1 * deriv theta t) / theta t ^ 2 := by
        rw [le_div_iff₀ hθ2]
        have h1 := hode t (hsub hti)
        have e : 1 / k * theta t ^ 2 = theta t ^ 2 / k := by ring
        have e3 : -theta t ^ 2 / k = -(theta t ^ 2 / k) := by ring
        rw [e]
        linarith
      linarith
  have hm := hmono ⟨le_refl 0, ht1pos.le⟩ ⟨ht1pos.le, le_refl t1⟩ ht1pos.le
  simp only [hinit, zero_div, sub_zero] at hm
  have hlt : 1 / theta t1 < 0 := div_neg_of_pos_of_neg one_pos (hneg' t1 ⟨ht1pos.le, le_refl t1⟩)
  have hk0 : k ≠ 0 := hk.ne'
  have h00 : theta0 ≠ 0 := hneg.ne
  have e : t1 / k = -(1 / theta0) := by
    rw [ht1]
    field_simp <;> ring_nf
  have e2 : 1 / theta0 < 0 := div_neg_of_pos_of_neg one_pos hneg
  rw [e] at hm
  linarith

theorem W3b_MathematicalRelativity_null_expansion_blowup_within_two_over_abs_theta
    (T theta0 : ℝ) (theta : ℝ → ℝ)
    (hneg : theta0 < 0) (hinit : theta 0 = theta0)
    (hdiff : ∀ t ∈ Set.Ico (0:ℝ) T, DifferentiableAt ℝ theta t)
    (hode : ∀ t ∈ Set.Ico (0:ℝ) T, deriv theta t ≤ - (theta t) ^ 2 / 2) :
    T ≤ 2 / (-theta0) :=
  W3b_MathematicalRelativity_blowup 2 T theta0 theta two_pos hneg hinit hdiff hode

theorem solution
    (T theta0 : ℝ) (theta : ℝ → ℝ)
    (hneg : theta0 < 0) (hinit : theta 0 = theta0)
    (hdiff : ∀ t ∈ Set.Ico (0:ℝ) T, DifferentiableAt ℝ theta t)
    (hode : ∀ t ∈ Set.Ico (0:ℝ) T, deriv theta t ≤ - (theta t) ^ 2 / 3) :
    T ≤ 3 / (-theta0) :=
  W3b_MathematicalRelativity_blowup 3 T theta0 theta three_pos hneg hinit hdiff hode
