-- Prove2me | solution 1 for MaxPressure.StrictLeontief.strict_leontief_eaa
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T03:40:53.204184+00:00
-- url     : https://prove2.me/submissions/3c3302a3-730b-4213-8036-98896ee728f8

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

set_option autoImplicit false

open MaxPressure.StrictLeontief Matrix in
/-- The pressure as a linear map in the allocation. -/
noncomputable def mp6fe_pressureLin {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := pressure N a z
  map_add' a b := by simp [pressure, Matrix.mulVec_add, dotProduct_add]
  map_smul' c a := by simp [pressure, Matrix.mulVec_smul, dotProduct_smul]

/-- Minus a weighted coordinate sum, as a linear map. -/
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
lemma mp6fe_trunc_notMem {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ)
    (a : Fin J → ℝ) (j : Fin J) (h : j ∉ J0 N z) : truncate N z a j = a j := by
  unfold truncate
  exact Set.indicator_of_mem (by simpa using h) _

open MaxPressure.StrictLeontief in
lemma mp6fe_pressure_eq {I J K : ℕ} (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * ∑ i, z i * R N i j := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

open MaxPressure.StrictLeontief in
lemma mp6fe_coef_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
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
lemma mp6fe_truncation {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
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
    · rw [mp6fe_trunc_mem N z a j hj]; exact ha0 j
    · rw [mp6fe_trunc_notMem N z a j hj]
  have hTnn : ∀ j, 0 ≤ truncate N z a j := fun j => by
    by_cases hj : j ∈ J0 N z
    · rw [mp6fe_trunc_mem N z a j hj]
    · rw [mp6fe_trunc_notMem N z a j hj]; exact ha0 j
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
      rw [mp6fe_trunc_notMem N z a j hnot]
  · rw [mp6fe_pressure_eq, mp6fe_pressure_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ J0 N z
    · rw [mp6fe_trunc_mem N z a j hj, zero_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (ha0 j) (mp6fe_coef_nonpos N hN hSL z hz j hj)
    · rw [mp6fe_trunc_notMem N z a j hj]

open MaxPressure.StrictLeontief in
/-- Some extreme allocation maximizes the pressure over `𝒜` and vanishes on `J0`. -/
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
  obtain ⟨htA, hle⟩ := mp6fe_truncation N hN hSL z hz x hx
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
