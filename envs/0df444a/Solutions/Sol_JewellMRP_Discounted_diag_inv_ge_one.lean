-- Prove2me | solution 1 for JewellMRP.Discounted.diag_inv_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:09.399777+00:00
-- url     : https://prove2.me/submissions/0f66a2a5-95c2-4b43-b9b4-832c75a107fc

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

open Matrix
open MeasureTheory
open JewellMRP.Discounted

private theorem exp_int_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iic (0 : ℝ)) = 0) {s : ℝ} (hs : 0 < s) :
    0 ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) ∧
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) < 1 := by
  have hIoi : μ (Set.Ioi (0 : ℝ)) = 1 := by
    have hcompl : Set.Ioi (0 : ℝ) = (Set.Iic (0 : ℝ))ᶜ := by ext x; simp
    rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), hμ, measure_univ,
      tsub_zero]
  haveI hprob : IsProbabilityMeasure (μ.restrict (Set.Ioi (0 : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact hIoi
  have hmeas : Measurable (fun t : ℝ => Real.exp (-(s * t))) := by fun_prop
  have hle1 : ∀ t : ℝ, 0 < t → Real.exp (-(s * t)) ≤ 1 := by
    intro t ht
    have hneg : -(s * t) ≤ 0 := by nlinarith
    calc Real.exp (-(s * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hint : Integrable (fun t : ℝ => Real.exp (-(s * t)))
      (μ.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.mono' (integrable_const 1) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle1 t (Set.mem_Ioi.mp ht)
  have hnn : 0 ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) :=
    integral_nonneg fun t => (Real.exp_pos _).le
  refine ⟨hnn, ?_⟩
  have hfnn : ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))), (0 : ℝ) ≤ 1 - Real.exp (-(s * t)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have := hle1 t (Set.mem_Ioi.mp ht)
    linarith
  have hint2 : Integrable (fun t : ℝ => 1 - Real.exp (-(s * t)))
      (μ.restrict (Set.Ioi (0 : ℝ))) := (integrable_const 1).sub hint
  have hsupp : 0 < (μ.restrict (Set.Ioi (0 : ℝ)))
      (Function.support fun t : ℝ => 1 - Real.exp (-(s * t))) := by
    have hsub : Set.Ioi (0 : ℝ)
        ⊆ Function.support fun t : ℝ => 1 - Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      have hlt : Real.exp (-(s * t)) < 1 := by
        have hneg : -(s * t) < 0 := by nlinarith
        calc Real.exp (-(s * t)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
          _ = 1 := Real.exp_zero
      simp only [Function.mem_support, ne_eq]
      intro hc
      linarith
    have hmono := measure_mono (μ := μ.restrict (Set.Ioi (0 : ℝ))) hsub
    have hν0 : (μ.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) = 1 := by
      rw [Measure.restrict_apply measurableSet_Ioi, Set.inter_self]
      exact hIoi
    rw [hν0] at hmono
    exact lt_of_lt_of_le zero_lt_one hmono
  have hpos : 0 < ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hfnn hint2).mpr hsupp
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) ∂μ)
      = 1 - ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ := by
    rw [integral_sub (integrable_const 1) hint]
    simp
  rw [hsplit] at hpos
  linarith

private theorem ftilde_bounds {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : 0 ≤ ftilde M z i j s ∧ ftilde M z i j s < 1 := by
  haveI := M.F_prob z i j
  exact exp_int_bounds (M.F z i j) (M.F_Iic_zero z i j) hs

private theorem qtilde_bounds {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : 0 ≤ qtilde M s z i j ∧ qtilde M s z i j < 1 := by
  obtain ⟨hf0, hf1⟩ := ftilde_bounds M hs z i j
  have hp0 : 0 ≤ M.p z i j := M.p_nonneg z i j
  have hp1 : M.p z i j ≤ 1 := by
    have := Finset.single_le_sum (f := fun k => M.p z i k)
      (fun k _ => M.p_nonneg z i k) (Finset.mem_univ j)
    rw [M.p_sum z i] at this
    exact this
  refine ⟨mul_nonneg hp0 hf0, ?_⟩
  calc M.p z i j * ftilde M z i j s ≤ 1 * ftilde M z i j s := by
        exact mul_le_mul_of_nonneg_right hp1 hf0
    _ = ftilde M z i j s := one_mul _
    _ < 1 := hf1

private theorem expand2 {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℝ)
    (x : S → ℝ) (i : S) :
    ∑ k, ((1 - Q) i k) * x k = x i - ∑ k, Q i k * x k := by
  have h1 : ∀ k : S, ((1 - Q) i k) * x k
      = (if i = k then x k else 0) - Q i k * x k := by
    intro k
    simp only [Matrix.sub_apply, Matrix.one_apply]
    split_ifs with hik <;> ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) :
    IsUnit (1 - Matrix.of (fun i j => qtilde M α (d i) i j)) ∧
      ∀ i, 1 ≤ (1 - Matrix.of (fun i j => qtilde M α (d i) i j))⁻¹ i i := by
  set Q : Matrix S S ℝ := Matrix.of (fun i j => qtilde M α (d i) i j) with hQ
  have hQnn : ∀ i j, 0 ≤ Q i j := fun i j => (qtilde_bounds M hα (d i) i j).1
  have hrow : ∀ i : S, ∑ j, Q i j < 1 := by
    intro i
    haveI : Nonempty S := ⟨i⟩
    obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : S => ftilde M (d i) i j α)
    have hfmax : ftilde M (d i) i j0 α < 1 := (ftilde_bounds M hα (d i) i j0).2
    calc ∑ j, Q i j = ∑ j, M.p (d i) i j * ftilde M (d i) i j α := rfl
      _ ≤ ∑ j, M.p (d i) i j * ftilde M (d i) i j0 α :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hj0 j) (M.p_nonneg (d i) i j)
      _ = (∑ j, M.p (d i) i j) * ftilde M (d i) i j0 α := by rw [Finset.sum_mul]
      _ = ftilde M (d i) i j0 α := by rw [M.p_sum (d i) i, one_mul]
      _ < 1 := hfmax
  have hdet : (1 - Q).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    haveI : Nonempty S := by
      rcases isEmpty_or_nonempty S with h | h
      · exact absurd (funext fun k => (IsEmpty.false k).elim) hv0
      · exact h
    obtain ⟨i, hi⟩ := Finite.exists_max (fun k : S => |v k|)
    have hrow0 : ∑ k, ((1 - Q) i k) * v k = 0 := by
      have hz : ((1 - Q) *ᵥ v) i = 0 := by rw [hv]; simp
      rw [Matrix.mulVec_apply_eq_sum] at hz
      exact hz
    rw [expand2 Q v i] at hrow0
    have hveq : v i = ∑ k, Q i k * v k := by linarith
    have hbd : |∑ k, Q i k * v k| ≤ (∑ k, Q i k) * |v i| := by
      calc |∑ k, Q i k * v k| ≤ ∑ k, |Q i k * v k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, Q i k * |v k| := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [abs_mul, abs_of_nonneg (hQnn i k)]
        _ ≤ ∑ k, Q i k * |v i| :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hi k) (hQnn i k)
        _ = (∑ k, Q i k) * |v i| := by rw [Finset.sum_mul]
    have habs : |v i| = |∑ k, Q i k * v k| := by rw [hveq]
    have hle : |v i| ≤ (∑ k, Q i k) * |v i| :=
      calc |v i| = |∑ k, Q i k * v k| := habs
        _ ≤ (∑ k, Q i k) * |v i| := hbd
    have hri := hrow i
    have hvi0 : |v i| = 0 := by
      by_contra hc
      have hpos : 0 < |v i| := (abs_nonneg _).lt_of_ne (Ne.symm hc)
      nlinarith [hle, hpos, mul_pos (sub_pos.mpr hri) hpos]
    apply hv0
    funext k
    have h2 : |v k| ≤ 0 := by rw [← hvi0]; exact hi k
    show v k = 0
    exact abs_nonpos_iff.mp h2
  have hunit : IsUnit (1 - Q) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hmulinv : (1 - Q) * (1 - Q)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hrowid : ∀ i j : S, ((1 - Q)⁻¹ i j) - ∑ k, Q i k * ((1 - Q)⁻¹ k j)
      = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : ∑ k, (1 - Q) i k * ((1 - Q)⁻¹ k j) = (1 : Matrix S S ℝ) i j := by
      rw [← Matrix.mul_apply, hmulinv]
    rw [← expand2 Q (fun k => (1 - Q)⁻¹ k j) i, h1, Matrix.one_apply]
  have hnn : ∀ i j : S, 0 ≤ (1 - Q)⁻¹ i j := by
    intro i j
    haveI : Nonempty S := ⟨i⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_min (fun k : S => (1 - Q)⁻¹ k j)
    have hmin0 : 0 ≤ (1 - Q)⁻¹ i0 j := by
      have he := hrowid i0 j
      have hsum : (∑ k, Q i0 k) * ((1 - Q)⁻¹ i0 j) ≤ ∑ k, Q i0 k * ((1 - Q)⁻¹ k j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hi0 k) (hQnn i0 k)
      have hδ : (0 : ℝ) ≤ if i0 = j then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have hri := hrow i0
      have hkey : 0 ≤ (1 - ∑ k, Q i0 k) * ((1 - Q)⁻¹ i0 j) := by linarith
      nlinarith [hkey, hri]
    exact le_trans hmin0 (hi0 i)
  refine ⟨hunit, ?_⟩
  intro i
  have he : (1 - Q)⁻¹ i i - ∑ k, Q i k * ((1 - Q)⁻¹ k i) = 1 := by
    have h := hrowid i i
    simpa using h
  have hs : 0 ≤ ∑ k, Q i k * ((1 - Q)⁻¹ k i) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hQnn i k) (hnn k i)
  linarith
