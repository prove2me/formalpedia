-- Prove2me | solution 1 for LassoDantzig.Oracle.cone_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:49:21.348522+00:00
-- url     : https://prove2.me/submissions/c63be461-0404-49da-b4fa-c2fa1ca2aee7

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

theorem aux_cs_colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j := by
  unfold colNorm empNorm
  exact Real.sqrt_nonneg _

theorem aux_cs_cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ)
    (d : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, w i * X.mulVec d i =
      ∑ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem aux_cs_expand {n : ℕ} (a b : Fin n → ℝ) :
    empSq (fun i => a i - b i) =
      empSq a - 2 * ((1 / (n : ℝ)) * ∑ i, a i * b i) + empSq b := by
  unfold empSq
  have h : ∑ i, (a i - b i) ^ 2 = ∑ i, (a i ^ 2 - 2 * (a i * b i) + b i ^ 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem aux_cs_basic {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ) (r : ℝ)
    (hr : 0 < r) (hA : NoiseBound X (fun i => y i - f i) r) (βhat β : Fin M → ℝ)
    (hL : IsLasso X y r βhat) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
      empSq (fun i => X.mulVec β i - f i) +
        4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
  have h := hL β
  unfold lassoObj at h
  set w : Fin n → ℝ := fun i => y i - f i with hw
  have hexp : ∀ b : Fin M → ℝ, empSq (fun i => y i - X.mulVec b i) =
      empSq w - 2 * ((1 / (n : ℝ)) * ∑ i, w i * (X.mulVec b i - f i)) +
        empSq (fun i => X.mulVec b i - f i) := by
    intro b
    have := aux_cs_expand w (fun i => X.mulVec b i - f i)
    rw [← this]
    congr 1
    funext i
    simp only [hw]
    ring
  rw [hexp βhat, hexp β] at h
  -- cross term
  have hcrossEq : (1 / (n : ℝ)) * ∑ i, w i * (X.mulVec βhat i - f i) -
      (1 / (n : ℝ)) * ∑ i, w i * (X.mulVec β i - f i) =
      ∑ j, (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by
    rw [← aux_cs_cross, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  have hcrossLe : 2 * ∑ j, (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) ≤
      r * ∑ j, colNorm X j * |βhat j - β j| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := hA j
    simp only [Pi.sub_apply]
    set a := (1 / (n : ℝ)) * ∑ i, X i j * w i
    have h1 : (βhat j - β j) * a ≤ |βhat j - β j| * |a| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : 0 ≤ |βhat j - β j| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hj h2]
  -- penalty term
  have hpen : ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) ≤
      ∑ j ∈ supp β, 2 * (colNorm X j * |βhat j - β j|) := by
    rw [← Finset.sum_add_sum_compl (supp β)]
    have hc : ∑ j ∈ (supp β)ᶜ, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : β j = 0 := by
        simp only [supp, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hj
        exact hj
      rw [this]
      simp
    rw [hc, add_zero]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : |β j| - |βhat j| ≤ |βhat j - β j| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    have h2 := aux_cs_colNorm_nonneg X j
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hsplit : ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) =
      ∑ j, colNorm X j * |βhat j - β j| + ∑ j, colNorm X j * |β j| -
        ∑ j, colNorm X j * |βhat j| := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit] at hpen
  rw [← Finset.mul_sum] at hpen
  nlinarith [hcrossEq, hcrossLe, hpen]

end LassoDantzig.Oracle

open LassoDantzig.Oracle
open MeasureTheory ProbabilityTheory

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    ∑ j, colNorm X j * |βhat j - β j| ≤
        4 * (1 + 1 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j| ≤
        (3 + 4 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ConeCond ((3 + 4 / ε) * fmax X / fmin X) (supp β) (βhat - β) := by
  have hbasic := aux_cs_basic X f y r hr hA βhat β hL
  set S := ∑ j, colNorm X j * |βhat j - β j| with hS
  set SJ := ∑ j ∈ supp β, colNorm X j * |βhat j - β j| with hSJ
  set SJc := ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j| with hSJc
  set Eb := empSq (fun i => X.mulVec β i - f i) with hEb
  have hEhat : 0 ≤ empSq (fun i => X.mulVec βhat i - f i) := by
    unfold empSq
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    exact mul_nonneg this (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hSJnn : 0 ≤ SJ := Finset.sum_nonneg fun j _ =>
    mul_nonneg (aux_cs_colNorm_nonneg X j) (abs_nonneg _)
  -- first claim
  have h1 : S ≤ 4 * (1 + 1 / ε) * SJ := by
    have hrS : r * S ≤ Eb + 4 * r * SJ := by linarith
    have hεrS : ε * (r * S) ≤ ε * (Eb + 4 * r * SJ) := mul_le_mul_of_nonneg_left hrS hε.le
    have key : ε * r * S ≤ ε * r * (4 * (1 + 1 / ε) * SJ) := by
      have e : ε * r * (4 * (1 + 1 / ε) * SJ) = 4 * r * SJ + ε * (4 * r * SJ) := by
        field_simp
        ring
      rw [e]
      nlinarith
    exact le_of_mul_le_mul_left key (mul_pos hε hr)
  have hsum : S = SJ + SJc := by
    rw [hS, hSJ, hSJc, Finset.sum_add_sum_compl]
  have h2 : SJc ≤ (3 + 4 / ε) * SJ := by
    have e : 4 * (1 + 1 / ε) * SJ = (3 + 4 / ε) * SJ + SJ := by ring
    linarith
  refine ⟨h1, h2, ?_⟩
  -- third claim
  have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_min (fun j => colNorm X j)
  have hpos0 : 0 < colNorm X j0 :=
    lt_of_le_of_ne (aux_cs_colNorm_nonneg X j0) (Ne.symm (hcol j0))
  have hfmin_ge : colNorm X j0 ≤ fmin X := le_ciInf hj0
  have hfmin : 0 < fmin X := lt_of_lt_of_le hpos0 hfmin_ge
  have hle_fmin : ∀ j, fmin X ≤ colNorm X j := fun j =>
    ciInf_le (Set.finite_range _).bddBelow j
  have hle_fmax : ∀ j, colNorm X j ≤ fmax X := fun j =>
    le_ciSup (Set.finite_range _).bddAbove j
  unfold ConeCond l1On
  simp only [Pi.sub_apply]
  have hA1 : fmin X * ∑ j ∈ (supp β)ᶜ, |βhat j - β j| ≤ SJc := by
    rw [hSJc, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle_fmin j) (abs_nonneg _)
  have hA2 : SJ ≤ fmax X * ∑ j ∈ supp β, |βhat j - β j| := by
    rw [hSJ, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle_fmax j) (abs_nonneg _)
  have hc : 0 ≤ 3 + 4 / ε := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hfmin]
  have := mul_le_mul_of_nonneg_left hA2 hc
  nlinarith
