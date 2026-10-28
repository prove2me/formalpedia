-- Prove2me | solution 2 for MaxPressure.StrictLeontief.strict_leontief_eaa
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:24.147847+00:00
-- url     : https://prove2.me/submissions/520b9492-edb3-47fb-b0c5-41c876d9e170

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network
import Theorems.Thm_MaxPressure_StrictLeontief_truncation_feasible

-- carved verbatim out of submission 3c3302a3-730b-4213-8036-98896ee728f8, lines 208-234

section
set_option autoImplicit false

open MaxPressure.StrictLeontief Matrix in
noncomputable def mp6fe_pressureLin {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := pressure N a z
  map_add' a b := by simp [pressure, Matrix.mulVec_add, dotProduct_add]
  map_smul' c a := by simp [pressure, Matrix.mulVec_smul, dotProduct_smul]

noncomputable def mp6fe_negSumLin {J : ℕ} (c : Fin J → ℝ) : (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := -∑ j, c j * a j
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' r a := by
    simp [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

open MaxPressure.StrictLeontief Matrix in
lemma mp6fe_allocSet_isCompact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  have hcl : IsClosed (allocSet N) := by
    have h1 : IsClosed {a : Fin J → ℝ | ∀ j, 0 ≤ a j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have h3 : IsClosed {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have : allocSet N = {a : Fin J → ℝ | ∀ j, 0 ≤ a j} ∩
        {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} ∩
        {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      ext a; simp [allocSet, and_assoc]
    rw [this]; exact (h1.inter h2).inter h3
  refine (isCompact_Icc (a := (0 : Fin J → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro a ha
  obtain ⟨hpos, hle, -⟩ := ha
  refine ⟨fun j => hpos j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := hAk j
  have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)), 0 ≤ N.A k j' * a j' := by
    intro j' _
    rcases hA01 k j' with h | h <;> simp [h, hpos j']
  have := Finset.single_le_sum hnn (Finset.mem_univ j)
  simp only [hk, one_mul] at this
  simpa using this.trans (hle k)

open MaxPressure.StrictLeontief in
lemma mp6fe_trunc_mem {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ)
    (a : Fin J → ℝ) (j : Fin J) (h : j ∈ J0 N z) : truncate N z a j = 0 := by
  unfold truncate
  exact Set.indicator_of_notMem (by simpa using h) _

open MaxPressure.StrictLeontief in
lemma mp6fe_extreme_vanishing {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hA : (allocSet N).Nonempty) (hSL : IsStrictLeontief N) (z : Fin I → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0 := by
  classical
  have hc := mp6fe_allocSet_isCompact N hN
  let l : StrongDual ℝ (Fin J → ℝ) := LinearMap.toContinuousLinearMap (mp6fe_pressureLin N z)
  have hl : ∀ a, l a = pressure N a z := fun a => rfl
  let c : Fin J → ℝ := fun j => if j ∈ J0 N z then 1 else 0
  let m : StrongDual ℝ (Fin J → ℝ) := LinearMap.toContinuousLinearMap (mp6fe_negSumLin c)
  have hm : ∀ a, m a = -∑ j, c j * a j := fun a => rfl
  set F1 := l.toExposed (allocSet N) with hF1
  set F2 := m.toExposed F1 with hF2
  have hexp1 : IsExposed ℝ (allocSet N) F1 := ContinuousLinearMap.toExposed.isExposed
  have hexp2 : IsExposed ℝ F1 F2 := ContinuousLinearMap.toExposed.isExposed
  have hF1c : IsCompact F1 := hexp1.isCompact hc
  have hF2c : IsCompact F2 := hexp2.isCompact hF1c
  -- a maximizer and its truncation
  obtain ⟨x, hx, hxmax⟩ := hc.exists_isMaxOn hA l.continuous.continuousOn
  obtain ⟨htA, hle⟩ := MaxPressure.StrictLeontief.truncation_feasible N hN hSL z hz x hx
  set t := truncate N z x with ht
  have htF1 : t ∈ F1 := ⟨htA, fun y hy => by
    rw [hl, hl]; exact (show pressure N y z ≤ pressure N x z from hxmax hy).trans hle⟩
  have hcnn : ∀ j, 0 ≤ c j := fun j => by
    simp only [c]; split_ifs <;> norm_num
  have hct : ∑ j, c j * t j = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ J0 N z
    · rw [ht, mp6fe_trunc_mem N z x j hj, mul_zero]
    · simp [c, hj]
  have hmle : ∀ y ∈ F1, m y ≤ m t := by
    intro y hy
    rw [hm, hm, hct, neg_zero, neg_nonpos]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hcnn j) (hy.1.1 j)
  have htF2 : t ∈ F2 := ⟨htF1, hmle⟩
  obtain ⟨e, he⟩ := hF2c.extremePoints_nonempty ⟨t, htF2⟩
  have heF2 : e ∈ F2 := he.1
  have heF1 : e ∈ F1 := heF2.1
  have heA : e ∈ allocSet N := heF1.1
  have hext : IsExtreme ℝ (allocSet N) F2 := hexp1.isExtreme.trans hexp2.isExtreme
  refine ⟨e, hext.extremePoints_subset_extremePoints he, fun a' ha' => ?_, fun j hj => ?_⟩
  · have := heF1.2 a' ha'
    simpa [hl] using this
  · have h1 : m t ≤ m e := heF2.2 t htF1
    rw [hm, hm, hct, neg_zero, le_neg, neg_zero] at h1
    have h0 : ∑ j, c j * e j = 0 :=
      le_antisymm h1 (Finset.sum_nonneg fun j _ => mul_nonneg (hcnn j) (heA.1 j))
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hcnn j) (heA.1 j))).mp h0 j (Finset.mem_univ j)
    simpa [c, hj] using hall

open MaxPressure.StrictLeontief in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hA : (allocSet N).Nonempty) (hSL : IsStrictLeontief N) : EAA N := by
  intro z hz
  obtain ⟨a, haE, hamax, havan⟩ := mp6fe_extreme_vanishing N hN hA hSL z hz
  refine ⟨a, haE, fun a' ha' => hamax a' (extremePoints_subset ha'), ?_⟩
  have haA : a ∈ allocSet N := extremePoints_subset haE
  obtain ⟨-, hB01, -, hIS, -⟩ := hN
  intro i hi
  have hi' : 0 < ∑ j, a j * N.B j i.succ := hi
  obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset (Fin J)), 0 < a j * N.B j i.succ := by
    by_contra hcon
    push_neg at hcon
    exact absurd hi' (not_lt.mpr (Finset.sum_nonpos hcon))
  have hBj : N.B j i.succ = 1 := by
    rcases hB01 j i.succ with h | h
    · rw [h, mul_zero] at hj; exact absurd hj (lt_irrefl 0)
    · exact h
  have hserv : IsServiceActivity N j := by
    rcases hIS j with h | h
    · rw [h.2 i] at hBj; norm_num at hBj
    · exact h
  rcases (hz i).lt_or_eq with h | h
  · exact h
  · have hJ0 : j ∈ J0 N z := ⟨hserv, i, hBj, h.symm⟩
    rw [havan j hJ0, zero_mul] at hj
    exact absurd hj (lt_irrefl 0)

end
