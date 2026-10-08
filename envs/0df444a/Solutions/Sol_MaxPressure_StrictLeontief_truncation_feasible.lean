-- Prove2me | solution 1 for MaxPressure.StrictLeontief.truncation_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:58:13.639918+00:00
-- url     : https://prove2.me/submissions/e6600a93-26f6-47a2-b79f-8b8dd54b7b98

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

open MaxPressure.StrictLeontief in
lemma mp31_trunc_mem {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ)
    (a : Fin J → ℝ) (j : Fin J) (h : j ∈ J0 N z) : truncate N z a j = 0 := by
  unfold truncate
  exact Set.indicator_of_notMem (by simpa using h) _

open MaxPressure.StrictLeontief in
lemma mp31_trunc_notMem {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ)
    (a : Fin J → ℝ) (j : Fin J) (h : j ∉ J0 N z) : truncate N z a j = a j := by
  unfold truncate
  exact Set.indicator_of_mem (by simpa using h) _

open MaxPressure.StrictLeontief in
lemma mp31_pressure_eq {I J K : ℕ} (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * ∑ i, z i * R N i j := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

open MaxPressure.StrictLeontief in
lemma mp31_coef_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (j : Fin J) (hj : j ∈ J0 N z) : ∑ i, z i * R N i j ≤ 0 := by
  obtain ⟨-, hB01, -, -, -, -, -, -, hm, hP, -⟩ := hN
  obtain ⟨hserv, i0, hBi0, hz0⟩ := hj
  obtain ⟨u, hu, huniq⟩ := hSL j hserv
  have hmu : 0 < mu N j := by unfold mu; exact one_div_pos.mpr (hm j)
  have hBnn : ∀ i', 0 ≤ N.B j i' := fun i' => by
    rcases hB01 j i' with h | h <;> rw [h] <;> norm_num
  have hzB : ∀ i : Fin I, z i * N.B j i.succ = 0 := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hz0, zero_mul]
    · have : N.B j i.succ ≠ 1 := by
        intro h1
        have e1 := huniq _ h1
        have e2 := huniq _ hBi0
        exact hi (Fin.succ_injective _ (e1.trans e2.symm))
      rcases hB01 j i.succ with h | h
      · rw [h, mul_zero]
      · exact absurd h this
  apply Finset.sum_nonpos
  intro i _
  have hS : 0 ≤ ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ :=
    Finset.sum_nonneg fun i' _ => mul_nonneg (hBnn i') (hP j i' i.succ)
  have hzS := mul_nonneg (hz i) hS
  have key : z i * R N i j
      = mu N j * (z i * N.B j i.succ)
        - mu N j * (z i * ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ) := by
    unfold R; ring
  rw [key, hzB i, mul_zero, zero_sub, neg_nonpos]
  exact mul_nonneg hmu.le hzS

open MaxPressure.StrictLeontief in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (a : Fin J → ℝ) (ha : a ∈ allocSet N) :
    truncate N z a ∈ allocSet N ∧ pressure N a z ≤ pressure N (truncate N z a) z := by
  obtain ⟨ha0, haLe, haEq⟩ := ha
  have hN' := hN
  obtain ⟨hA, -, -, -, -, hIP, -, -, -, -, -⟩ := hN'
  have hAnn : ∀ k j, 0 ≤ N.A k j := fun k j => by
    rcases hA k j with h | h <;> rw [h] <;> norm_num
  have hTle : ∀ j, truncate N z a j ≤ a j := fun j => by
    by_cases hj : j ∈ J0 N z
    · rw [mp31_trunc_mem N z a j hj]; exact ha0 j
    · rw [mp31_trunc_notMem N z a j hj]
  have hTnn : ∀ j, 0 ≤ truncate N z a j := fun j => by
    by_cases hj : j ∈ J0 N z
    · rw [mp31_trunc_mem N z a j hj]
    · rw [mp31_trunc_notMem N z a j hj]; exact ha0 j
  refine ⟨⟨hTnn, fun k => ?_, fun k hk => ?_⟩, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun j _ => ?_) (haLe k)
    exact mul_le_mul_of_nonneg_left (hTle j) (hAnn k j)
  · rw [← haEq k hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases hA k j with h | h
    · rw [h, zero_mul, zero_mul]
    · have hin : IsInputActivity N j := (hIP k j h).mp hk
      have hnot : j ∉ J0 N z := by
        rintro ⟨hs, -⟩
        have h1 := hin.1
        unfold IsServiceActivity at hs
        rw [hs] at h1
        norm_num at h1
      rw [mp31_trunc_notMem N z a j hnot]
  · rw [mp31_pressure_eq, mp31_pressure_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ J0 N z
    · rw [mp31_trunc_mem N z a j hj, zero_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (ha0 j) (mp31_coef_nonpos N hN hSL z hz j hj)
    · rw [mp31_trunc_notMem N z a j hj]
