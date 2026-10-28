-- Prove2me | solution 1 for IRLSM.Convergence.eq_6_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T08:13:29.099568+00:00
-- url     : https://prove2.me/submissions/007d4007-d7a5-4f4f-8a22-69eacb85618e

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace Aux_IRLSM611

lemma ev_zero {n p : ℕ} (Θ : Matrix (Fin n) (Fin p) ℝ)
    (k : Fin (Fintype.card (Fin p))) (hk : n ≤ k.val) :
    (Matrix.posSemidef_conjTranspose_mul_self Θ).1.eigenvalues₀ k = 0 := by
  set hA := (Matrix.posSemidef_conjTranspose_mul_self Θ)
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))
  have hev : ∀ j, hA.1.eigenvalues₀ j = hA.1.eigenvalues (e j) := by
    intro j
    simp [IsHermitian.eigenvalues, e]
  have hnn : ∀ j, 0 ≤ hA.1.eigenvalues₀ j := fun j => by
    rw [hev]; exact hA.eigenvalues_nonneg _
  by_contra hne
  have hpos : ∀ j, j ≤ k → hA.1.eigenvalues₀ j ≠ 0 := by
    intro j hj
    have := hA.1.eigenvalues₀_antitone hj
    have := hnn k
    have : 0 < hA.1.eigenvalues₀ k := lt_of_le_of_ne this (Ne.symm hne)
    linarith
  have hrank := hA.1.rank_eq_card_non_zero_eigs
  rw [rank_conjTranspose_mul_self] at hrank
  have hcard : Fintype.card {i // hA.1.eigenvalues i ≠ 0} =
      Fintype.card {j // hA.1.eigenvalues₀ j ≠ 0} := by
    refine Fintype.card_congr (Equiv.subtypeEquiv e.symm ?_)
    intro i
    simp [IsHermitian.eigenvalues, e]
  have hge : k.val + 1 ≤ Fintype.card {j // hA.1.eigenvalues₀ j ≠ 0} := by
    rw [Fintype.card_subtype, ← Fin.card_Iic]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpos j (Finset.mem_Iic.mp hj)
  have hle := Θ.rank_le_height
  omega

lemma sv_zero {n p : ℕ} (Θ : Matrix (Fin n) (Fin p) ℝ) (i : ℕ) (hi : n ≤ i) :
    IRLSM.Convergence.sv Θ i = 0 := by
  unfold IRLSM.Convergence.sv
  split_ifs with h
  · unfold singularValues
    rw [ev_zero Θ _ (by simpa using hi), Real.sqrt_zero]
  · rfl

lemma sv_nonneg {n p : ℕ} (Θ : Matrix (Fin n) (Fin p) ℝ) (i : ℕ) :
    0 ≤ IRLSM.Convergence.sv Θ i := by
  unfold IRLSM.Convergence.sv
  split_ifs with h
  · unfold singularValues; exact Real.sqrt_nonneg _
  · exact le_rfl

lemma nuclear_eq {n p : ℕ} (hnp : n ≤ p) (Θ : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm Θ = ∑ i ∈ Finset.range n, IRLSM.Convergence.sv Θ i := by
  have h1 : nuclearNorm Θ = ∑ i ∈ Finset.range p, IRLSM.Convergence.sv Θ i := by
    unfold nuclearNorm
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold IRLSM.Convergence.sv
    rw [dif_pos j.isLt]
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hnp]
  have h2 : ∑ i ∈ Finset.Ico n p, IRLSM.Convergence.sv Θ i = 0 :=
    Finset.sum_eq_zero fun i hi => sv_zero Θ i (Finset.mem_Ico.mp hi).1
  rw [h2, add_zero]

lemma j_bounds (ε u : ℝ) (hε : 0 < ε) (hu : 0 ≤ u) :
    u ≤ IRLSM.Convergence.jε ε u ∧ IRLSM.Convergence.jε ε u ≤ u + ε := by
  unfold IRLSM.Convergence.jε
  rw [abs_of_nonneg hu]
  split_ifs with h
  · constructor <;> linarith
  · push Not at h
    constructor
    · rw [le_div_iff₀ (by linarith)]; nlinarith [sq_nonneg (u - ε)]
    · rw [div_le_iff₀ (by linarith)]; nlinarith

end Aux_IRLSM611

open IRLSM.Convergence Aux_IRLSM611 in
theorem solution {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (ε : ℝ)
    (hnp : n ≤ p) (hε : 0 < ε) :
    (∀ Y : Matrix (Fin n) (Fin p) ℝ,
      nuclearNorm Y ≤ Jeps ε Y ∧ Jeps ε Y ≤ nuclearNorm Y + n * ε) ∧
    ∀ Xbar X : Matrix (Fin n) (Fin p) ℝ, observationOp A Xbar = M →
      (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps ε Xbar ≤ Jeps ε Y) →
      observationOp A X = M → nuclearNorm Xbar - nuclearNorm X ≤ n * ε := by
  have part1 : ∀ Y : Matrix (Fin n) (Fin p) ℝ,
      nuclearNorm Y ≤ Jeps ε Y ∧ Jeps ε Y ≤ nuclearNorm Y + n * ε := by
    intro Y
    rw [nuclear_eq hnp Y]
    unfold Jeps
    constructor
    · exact Finset.sum_le_sum fun i _ => (j_bounds ε _ hε (sv_nonneg Y i)).1
    · calc ∑ i ∈ Finset.range n, jε ε (sv Y i)
          ≤ ∑ i ∈ Finset.range n, (sv Y i + ε) :=
            Finset.sum_le_sum fun i _ => (j_bounds ε _ hε (sv_nonneg Y i)).2
        _ = ∑ i ∈ Finset.range n, sv Y i + n * ε := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨part1, fun Xbar X hXbar hmin hX => ?_⟩
  have h1 := (part1 Xbar).1
  have h2 := hmin X hX
  have h3 := (part1 X).2
  linarith

