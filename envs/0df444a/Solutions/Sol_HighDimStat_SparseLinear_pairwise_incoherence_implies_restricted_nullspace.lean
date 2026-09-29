-- Prove2me | solution 1 for HighDimStat.SparseLinear.pairwise_incoherence_implies_restricted_nullspace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T06:02:33.170814+00:00
-- url     : https://prove2.me/submissions/97a708c9-076f-4524-a05f-f6539212c00b

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_PairwiseIncoherence
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty



namespace HighDimStat.SparseLinear

theorem pi_main {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ)
    (h : pairwiseIncoherence X ≤ 1 / (3 * (s : ℝ))) :
    ∀ S : Finset (Fin d), S.card ≤ s → RestrictedNullspaceProperty X S := by
  classical
  intro S hS Δ hC hX
  set δ := pairwiseIncoherence X with hδ
  set G : Fin d → Fin d → ℝ := fun j k => (∑ i, X i j * X i k) / (n : ℝ) with hG
  have hE : ∀ j k, |G j k - (if j = k then (1:ℝ) else 0)| ≤ δ := by
    intro j k
    exact le_ciSup (f := fun jk : Fin d × Fin d =>
      |(∑ i, X i jk.1 * X i jk.2) / (n : ℝ) - (if jk.1 = jk.2 then (1 : ℝ) else 0)|)
      (Set.finite_range _).bddAbove (j, k)
  have hδ0 : 0 ≤ δ := Real.iSup_nonneg fun _ => abs_nonneg _
  have hδs : δ * (S.card : ℝ) ≤ 1 / 3 := by
    have hcs : (S.card : ℝ) ≤ s := by exact_mod_cast hS
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      have : (S.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp hS
      rw [this, mul_zero]; norm_num
    · have hsR : (0:ℝ) < s := by exact_mod_cast hpos
      calc δ * (S.card : ℝ) ≤ δ * s := mul_le_mul_of_nonneg_left hcs hδ0
        _ ≤ 1 / (3 * s) * s := mul_le_mul_of_nonneg_right h hsR.le
        _ = 1 / 3 := by field_simp
  have hXΔ : ∀ i, ∑ k, X i k * Δ k = 0 := by
    intro i
    have := congrFun hX i
    simpa [Matrix.mulVec, dotProduct] using this
  have hzero : ∑ j ∈ S, ∑ k, Δ j * Δ k * G j k = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have e1 : ∀ k, Δ j * Δ k * G j k = (∑ i, Δ j * X i j * (X i k * Δ k)) / n := by
      intro k
      simp only [hG]
      rw [mul_div_assoc', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun k _ => e1 k, ← Finset.sum_div, Finset.sum_comm]
    apply div_eq_zero_iff.mpr
    left
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, hXΔ i, mul_zero]
  have hdec : ∀ j, ∑ k, Δ j * Δ k * G j k =
      Δ j ^ 2 + ∑ k, Δ j * Δ k * (G j k - if j = k then 1 else 0) := by
    intro j
    have e : ∀ k, Δ j * Δ k * G j k = Δ j * Δ k * (if j = k then 1 else 0) +
        Δ j * Δ k * (G j k - if j = k then 1 else 0) := fun k => by ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib]
    congr 1
    simp [sq]
  set Q := ∑ j ∈ S, Δ j ^ 2 with hQ
  set A1 := ∑ j ∈ S, |Δ j| with hA1
  set R := ∑ j ∈ S, ∑ k, Δ j * Δ k * (G j k - if j = k then 1 else 0) with hR
  have hQR : Q + R = 0 := by
    have hz := hzero
    rw [Finset.sum_congr rfl fun j _ => hdec j, Finset.sum_add_distrib] at hz
    exact hz
  have hRb : |R| ≤ δ * (A1 * ∑ k, |Δ k|) := by
    calc |R| ≤ ∑ j ∈ S, |∑ k, Δ j * Δ k * (G j k - if j = k then 1 else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S, ∑ k, |Δ j * Δ k * (G j k - if j = k then 1 else 0)| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S, ∑ k, δ * (|Δ j| * |Δ k|) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_mul]
          have := hE j k
          have hp : 0 ≤ |Δ j| * |Δ k| := by positivity
          nlinarith
      _ = δ * (A1 * ∑ k, |Δ k|) := by
          rw [hA1, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  have hcone : ∑ j ∈ Sᶜ, |Δ j| ≤ 1 * A1 := hC
  have hA0 : 0 ≤ A1 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have htot : ∑ k, |Δ k| ≤ 2 * A1 := by
    rw [← Finset.sum_add_sum_compl S (fun k => |Δ k|)]
    linarith
  have hcs : A1 ^ 2 ≤ (S.card : ℝ) * Q := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j => |Δ j|)
    simpa [hA1, hQ, sq_abs] using this
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQle : Q ≤ 0 := by
    have h1 : Q ≤ δ * (A1 * ∑ k, |Δ k|) := by
      have := neg_abs_le R
      linarith
    have h2 : δ * (A1 * ∑ k, |Δ k|) ≤ δ * (A1 * (2 * A1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htot hA0) hδ0
    have h3 : δ * (A1 * (2 * A1)) ≤ 2 * δ * ((S.card : ℝ) * Q) := by
      have := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 2 * δ)
      nlinarith
    have h4 : 2 * δ * ((S.card : ℝ) * Q) ≤ 2 / 3 * Q := by
      have := mul_le_mul_of_nonneg_right hδs (by positivity : (0:ℝ) ≤ 2 * Q)
      nlinarith
    linarith
  have hQz : Q = 0 := le_antisymm hQle hQ0
  have hSz : ∀ j ∈ S, Δ j = 0 := by
    intro j hj
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (Δ j))).mp hQz j hj
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hA1z : A1 = 0 := Finset.sum_eq_zero fun j hj => by rw [hSz j hj, abs_zero]
  have hScz : ∀ j ∈ Sᶜ, Δ j = 0 := by
    intro j hj
    have h0 : ∑ j ∈ Sᶜ, |Δ j| = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (Δ j))).mp h0 j hj
    exact abs_eq_zero.mp this
  funext j
  by_cases hj : j ∈ S
  · exact hSz j hj
  · exact hScz j (Finset.mem_compl.mpr hj)

end HighDimStat.SparseLinear

open HighDimStat.SparseLinear

theorem solution {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (h : pairwiseIncoherence X ≤ 1 / (3 * (s : ℝ))) :
    ∀ S : Finset (Fin d), S.card ≤ s → RestrictedNullspaceProperty X S := by
  exact pi_main X s h
