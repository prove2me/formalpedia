-- Prove2me | solution 1 for GreedWorks.OnlineList.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:47.226474+00:00
-- url     : https://prove2.me/submissions/7e01a114-928c-4b14-a545-41b930add91d

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy
import Definitions.Def_GreedWorks_OnlineList_LP

open GreedWorks.OnlineList MeasureTheory

noncomputable section

namespace Lemma5Helper

variable {M : Type*} [Fintype M] [DecidableEq M] {n : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]

private lemma mem_high_iff (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n) :
    k ∈ high I j i ↔
      I.weight j / mean I i j < I.weight k / mean I i k ∨
        (k ≤ j ∧ I.weight k / mean I i k = I.weight j / mean I i j) := by
  unfold high
  simp

private lemma mem_low_iff (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n) :
    k ∈ low I j i ↔ k ∉ high I j i := by
  unfold low
  simp

private lemma high_refl (I : StochasticInstance M n Ω) (j : Fin n) (i : M) :
    j ∈ high I j i := by
  rw [mem_high_iff]
  exact Or.inr ⟨le_refl j, rfl⟩

private lemma high_trans (I : StochasticInstance M n Ω) (i : M) {k₁ k₂ k₃ : Fin n}
    (h12 : k₁ ∈ high I k₂ i) (h23 : k₂ ∈ high I k₃ i) :
    k₁ ∈ high I k₃ i := by
  rw [mem_high_iff] at h12 h23 ⊢
  rcases h12 with hlt12 | ⟨hle12, heq12⟩ <;> rcases h23 with hlt23 | ⟨hle23, heq23⟩
  · exact Or.inl (lt_trans hlt23 hlt12)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨le_trans hle12 hle23, by linarith⟩

private lemma high_total (I : StochasticInstance M n Ω) (i : M) (k₁ k₂ : Fin n) :
    k₁ ∈ high I k₂ i ∨ k₂ ∈ high I k₁ i := by
  rw [mem_high_iff, mem_high_iff]
  rcases lt_trichotomy (I.weight k₁ / mean I i k₁) (I.weight k₂ / mean I i k₂) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · rcases le_total k₁ k₂ with hle | hle
    · exact Or.inl (Or.inr ⟨hle, heq⟩)
    · exact Or.inr (Or.inr ⟨hle, heq.symm⟩)
  · exact Or.inl (Or.inl hgt)

private lemma exists_min_high (I : StochasticInstance M n Ω) (i : M)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ k₀ ∈ S, ∀ k ∈ S, k ∈ high I k₀ i := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, Finset.mem_singleton_self a, fun k hk => by
      rw [Finset.mem_singleton.mp hk]
      exact high_refl I a i⟩
  | cons a s ha hs ih =>
    obtain ⟨k₀, hk₀, hmin⟩ := ih
    rcases high_total I i a k₀ with hak₀ | hk₀a
    · refine ⟨k₀, Finset.mem_cons_of_mem hk₀, fun k hk => ?_⟩
      rcases Finset.mem_cons.mp hk with rfl | hks
      · exact hak₀
      · exact hmin k hks
    · refine ⟨a, Finset.mem_cons_self a s, fun k hk => ?_⟩
      rcases Finset.mem_cons.mp hk with rfl | hks
      · exact high_refl I k i
      · exact high_trans I i (hmin k hks) hk₀a

private lemma ratio_le_of_mem_high (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n)
    (hk : k ∈ high I j i) :
    I.weight j / mean I i j ≤ I.weight k / mean I i k := by
  rw [mem_high_iff] at hk
  rcases hk with hlt | ⟨_, heq⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq.symm

private lemma ratio_le_of_not_mem_high (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n)
    (hk : k ∉ high I j i) :
    I.weight k / mean I i k ≤ I.weight j / mean I i j := by
  rcases high_total I i k j with hkj | hjk
  · exact False.elim (hk hkj)
  · exact ratio_le_of_mem_high I k i j hjk

private lemma mean_pos_of_eligible (I : StochasticInstance M n Ω) {i : M} {j : Fin n}
    (h : I.eligible i j) : 0 < mean I i j := by
  have h1 : 1 ≤ mean I i j := I.meanAtLeastOne i j h
  linarith

private lemma sum_mean_le_of_nominalCompletion_le (I : StochasticInstance M n Ω)
    (m : Fin n → M) (hm : IsGreedy I m) (i : M) (t : ℝ) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t),
      mean I i k) ≤ t := by
  let A := Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t)
  by_cases hA : A.Nonempty
  · obtain ⟨k₀, hk₀A, hmin⟩ := exists_min_high I i A hA
    have hk₀_m : m k₀ = i := (Finset.mem_filter.mp hk₀A).2.1
    have hk₀_t : nominalCompletion I m k₀ ≤ t := (Finset.mem_filter.mp hk₀A).2.2
    have hsub : A ⊆ Finset.univ.filter (fun k : Fin n => m k = m k₀ ∧ k ∈ high I k₀ (m k₀)) := by
      intro k hk
      have hkm : m k = i := (Finset.mem_filter.mp hk).2.1
      have hkh : k ∈ high I k₀ i := hmin k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hk₀_m]
      exact ⟨hkm, hkh⟩
    have hle : (∑ k ∈ A, mean I (m k₀) k) ≤ nominalCompletion I m k₀ := by
      unfold nominalCompletion
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => ?_)
      have hkm : m k = m k₀ := (Finset.mem_filter.mp hk).2.1
      rw [← hkm]
      exact le_of_lt (mean_pos_of_eligible I (hm k).1)
    have heq : (∑ k ∈ A, mean I i k) = ∑ k ∈ A, mean I (m k₀) k := by
      rw [hk₀_m]
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    change (∑ k ∈ A, mean I i k) ≤ t
    rw [hA, Finset.sum_empty]
    exact ht

private def jobTerm (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n) : ℝ :=
  if k ∈ high I j i then (I.weight j / mean I i j) * mean I i k else I.weight k

private lemma jobTerm_nonneg (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (j : Fin n) (i : M) (hi : I.eligible i j) (k : Fin n) (hmk : m k = i) :
    0 ≤ jobTerm I j i k := by
  unfold jobTerm
  split_ifs
  · have h1 : 0 ≤ I.weight j := I.weight_nonneg j
    have h2 : 0 < mean I i j := mean_pos_of_eligible I hi
    have h3 : 0 < mean I i k := by rw [← hmk]; exact mean_pos_of_eligible I (hm k).1
    positivity
  · exact I.weight_nonneg k

private lemma jobTerm_le_mean_mul (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (j : Fin n) (i : M) (k : Fin n) (hmk : m k = i) :
    jobTerm I j i k ≤ (I.weight j / mean I i j) * mean I i k := by
  unfold jobTerm
  split_ifs with hkh
  · exact le_refl _
  · have hr := ratio_le_of_not_mem_high I j i k hkh
    have hmk_pos : 0 < mean I i k := by rw [← hmk]; exact mean_pos_of_eligible I (hm k).1
    exact (div_le_iff₀ hmk_pos).mp hr

private lemma jobTerm_le_weight (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (j : Fin n) (i : M) (k : Fin n) (hmk : m k = i) :
    jobTerm I j i k ≤ I.weight k := by
  unfold jobTerm
  split_ifs with hkh
  · have hr := ratio_le_of_mem_high I j i k hkh
    have hmk_pos : 0 < mean I i k := by rw [← hmk]; exact mean_pos_of_eligible I (hm k).1
    exact (le_div_iff₀ hmk_pos).mp hr
  · exact le_refl _

private lemma incrementalCost_div_mean (I : StochasticInstance M n Ω) (m : Fin n → M)
    (j : Fin n) (i : M) (hi : I.eligible i j) :
    incrementalCost I m j i / mean I i j =
      I.weight j + ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i), jobTerm I j i k := by
  classical
  let S := Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i)
  have hsplit := (Finset.sum_filter_add_sum_filter_not S (fun k => k ∈ high I j i)
    (jobTerm I j i)).symm
  have h1 : S.filter (fun k => k ∈ high I j i) =
      Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i ∧ k ∈ high I j i) := by
    ext k; simp [S, and_assoc]
  have h2 : S.filter (fun k => ¬ k ∈ high I j i) =
      Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i ∧ k ∈ low I j i) := by
    ext k; simp [S, mem_low_iff, and_assoc]
  have hsum1 : ∑ x ∈ S.filter (fun k => k ∈ high I j i), jobTerm I j i x =
      (I.weight j / mean I i j) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i ∧ k ∈ high I j i),
          mean I i k := by
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkh : k ∈ high I j i := (Finset.mem_filter.mp hk).2.2.2
    simp [jobTerm, hkh]
  have hsum2 : ∑ x ∈ S.filter (fun k => ¬ k ∈ high I j i), jobTerm I j i x =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i ∧ k ∈ low I j i),
        I.weight k := by
    rw [h2]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkl : k ∈ low I j i := (Finset.mem_filter.mp hk).2.2.2
    have hkh : k ∉ high I j i := (mem_low_iff I j i k).mp hkl
    simp [jobTerm, hkh]
  change incrementalCost I m j i / mean I i j = I.weight j + ∑ k ∈ S, jobTerm I j i k
  rw [hsplit, hsum1, hsum2]
  unfold incrementalCost
  have hm_ne : mean I i j ≠ 0 := ne_of_gt (mean_pos_of_eligible I hi)
  field_simp [hm_ne]
  ring

private lemma alpha_div_mean_le (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (i : M) (j : Fin n) (hi : I.eligible i j) (t : ℝ) (ht : 0 ≤ t) :
    alpha I m j / mean I i j ≤
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ t < nominalCompletion I m k),
        I.weight k) +
      I.weight j * (t / mean I i j + 1) := by
  have hm_pos : 0 < mean I i j := mean_pos_of_eligible I hi
  have hgreedy : alpha I m j ≤ incrementalCost I m j i := (hm j).2 i hi
  have hdiv_le : alpha I m j / mean I i j ≤ incrementalCost I m j i / mean I i j :=
    div_le_div_of_nonneg_right hgreedy (le_of_lt hm_pos)
  rw [incrementalCost_div_mean I m j i hi] at hdiv_le
  let M_i := Finset.univ.filter (fun k : Fin n => m k = i)
  have hsub : Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i) ⊆ M_i := by
    intro k hk
    simp only [M_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.2
  have hle_M : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i), jobTerm I j i k ≤
      ∑ k ∈ M_i, jobTerm I j i k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => ?_)
    exact jobTerm_nonneg I m hm j i hi k (Finset.mem_filter.mp hk).2
  have hpart := (Finset.sum_filter_add_sum_filter_not M_i
    (fun k => nominalCompletion I m k ≤ t) (jobTerm I j i)).symm
  have hA_eq : M_i.filter (fun k => nominalCompletion I m k ≤ t) =
      Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t) := by
    ext k; simp [M_i]
  have hB_eq : M_i.filter (fun k => ¬ nominalCompletion I m k ≤ t) =
      Finset.univ.filter (fun k : Fin n => m k = i ∧ t < nominalCompletion I m k) := by
    ext k; simp [M_i, not_le]
  have hA_le : ∑ k ∈ M_i.filter (fun k => nominalCompletion I m k ≤ t), jobTerm I j i k ≤
      (I.weight j / mean I i j) * t := by
    rw [hA_eq]
    calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t),
          jobTerm I j i k
        ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t),
            ((I.weight j / mean I i j) * mean I i k) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          exact jobTerm_le_mean_mul I m hm j i k (Finset.mem_filter.mp hk).2.1
      _ = (I.weight j / mean I i j) *
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ nominalCompletion I m k ≤ t),
              mean I i k := by rw [← Finset.mul_sum]
      _ ≤ (I.weight j / mean I i j) * t := by
          refine mul_le_mul_of_nonneg_left (sum_mean_le_of_nominalCompletion_le I m hm i t ht) ?_
          exact div_nonneg (I.weight_nonneg j) (le_of_lt hm_pos)
  have hB_le : ∑ k ∈ M_i.filter (fun k => ¬ nominalCompletion I m k ≤ t), jobTerm I j i k ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ t < nominalCompletion I m k),
        I.weight k := by
    rw [hB_eq]
    refine Finset.sum_le_sum (fun k hk => ?_)
    exact jobTerm_le_weight I m hm j i k (Finset.mem_filter.mp hk).2.1
  have htot : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i), jobTerm I j i k ≤
      (I.weight j / mean I i j) * t +
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ t < nominalCompletion I m k),
          I.weight k := by
    calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j ∧ m k = i), jobTerm I j i k
        ≤ ∑ k ∈ M_i, jobTerm I j i k := hle_M
      _ = ∑ k ∈ M_i.filter (fun k => nominalCompletion I m k ≤ t), jobTerm I j i k +
            ∑ k ∈ M_i.filter (fun k => ¬ nominalCompletion I m k ≤ t), jobTerm I j i k := hpart
      _ ≤ (I.weight j / mean I i j) * t +
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ t < nominalCompletion I m k),
              I.weight k := add_le_add hA_le hB_le
  have hring : I.weight j + (I.weight j / mean I i j) * t =
      I.weight j * (t / mean I i j + 1) := by ring
  linarith

private lemma div_fastMean_eq (I : StochasticInstance M n Ω) (f : ℕ) (i : M) (k : Fin n) :
    I.weight k / fastMean I f i k = (I.weight k / mean I i k) * (f : ℝ) := by
  unfold fastMean
  rw [div_div_eq_mul_div, mul_div_right_comm]

private lemma highFast_eq_high (I : StochasticInstance M n Ω) {f : ℕ} (hf : 2 ≤ f)
    (j : Fin n) (i : M) :
    highFast I f j i = high I j i := by
  have hf_pos : (0 : ℝ) < (f : ℝ) := by
    have : 0 < f := by omega
    exact Nat.cast_pos.mpr this
  have hf_ne : (f : ℝ) ≠ 0 := ne_of_gt hf_pos
  unfold highFast high
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, div_fastMean_eq,
    mul_lt_mul_iff_left₀ hf_pos, mul_left_inj' hf_ne]

private lemma lowFast_eq_low (I : StochasticInstance M n Ω) {f : ℕ} (hf : 2 ≤ f)
    (j : Fin n) (i : M) :
    lowFast I f j i = low I j i := by
  unfold lowFast low
  rw [highFast_eq_high I hf j i]

private lemma incrementalCostFast_eq (I : StochasticInstance M n Ω) (m : Fin n → M)
    {f : ℕ} (hf : 2 ≤ f) (j : Fin n) (i : M) :
    incrementalCostFast I m f j i = incrementalCost I m j i / (f : ℝ) := by
  unfold incrementalCostFast incrementalCost
  simp only [highFast_eq_high I hf j i, lowFast_eq_low I hf j i, fastMean]
  rw [← Finset.sum_div]
  ring

private lemma alphaFast_eq (I : StochasticInstance M n Ω) (m : Fin n → M)
    {f : ℕ} (hf : 2 ≤ f) (j : Fin n) :
    alphaFast I m f j = alpha I m j / (f : ℝ) := by
  unfold alphaFast alpha
  exact incrementalCostFast_eq I m hf j (m j)

private lemma nominalCompletionFast_eq (I : StochasticInstance M n Ω) (m : Fin n → M)
    {f : ℕ} (hf : 2 ≤ f) (j : Fin n) :
    nominalCompletionFast I m f j = nominalCompletion I m j / (f : ℝ) := by
  unfold nominalCompletionFast nominalCompletion
  simp only [highFast_eq_high I hf j (m j), fastMean]
  rw [← Finset.sum_div]

private lemma betaFast_eq (I : StochasticInstance M n Ω) (m : Fin n → M)
    {f : ℕ} (hf : 2 ≤ f) (i : M) (s : ℕ) :
    betaFast I m f i s =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => m k = i ∧ (f : ℝ) * (s : ℝ) < nominalCompletion I m k),
        I.weight k := by
  have hf_pos : (0 : ℝ) < (f : ℝ) := by
    have : 0 < f := by omega
    exact Nat.cast_pos.mpr this
  unfold betaFast
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, nominalCompletionFast_eq I m hf k]
  refine and_congr_right (fun _ => ?_)
  rw [lt_div_iff₀ hf_pos, mul_comm]

private lemma summable_betaFast_div (I : StochasticInstance M n Ω) (m : Fin n → M)
    (f : ℕ) (i : M) :
    Summable (fun s : ℕ => betaFast I m f i s / (f : ℝ)) := by
  let B : ℕ := Finset.univ.sup (fun k : Fin n => ⌈nominalCompletionFast I m f k⌉₊)
  refine summable_of_ne_finset_zero (s := Finset.range B) (fun s hs => ?_)
  have hge : B ≤ s := Nat.le_of_not_lt (Finset.mem_range.not.mp hs)
  have hbeta0 : betaFast I m f i s = 0 := by
    unfold betaFast
    refine Finset.sum_eq_zero (fun k hk => ?_)
    exfalso
    have hlt : (s : ℝ) < nominalCompletionFast I m f k := (Finset.mem_filter.mp hk).2.2
    have hleB : ⌈nominalCompletionFast I m f k⌉₊ ≤ B :=
      Finset.le_sup (f := fun k : Fin n => ⌈nominalCompletionFast I m f k⌉₊) (Finset.mem_univ k)
    have hle_s : ⌈nominalCompletionFast I m f k⌉₊ ≤ s := le_trans hleB hge
    have h1 : nominalCompletionFast I m f k ≤ (⌈nominalCompletionFast I m f k⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈nominalCompletionFast I m f k⌉₊ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hle_s
    linarith
  rw [hbeta0, zero_div]

end Lemma5Helper

open Lemma5Helper

theorem solution {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (f : ℕ) (hf : 2 ≤ f) :
    IsDualFeasible I (alphaFast I m f) (fun i s => betaFast I m f i s / (f : ℝ)) := by
  have hf_pos : (0 : ℝ) < (f : ℝ) := by
    have : 0 < f := by omega
    exact Nat.cast_pos.mpr this
  have hf_ge_two : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    unfold betaFast
    exact div_nonneg (Finset.sum_nonneg (fun k _ => I.weight_nonneg k)) (le_of_lt hf_pos)
  · intro i
    exact summable_betaFast_div I m f i
  · intro i j s hi
    have hmain := alpha_div_mean_le I m hm i j hi ((f : ℝ) * (s : ℝ)) (by positivity)
    rw [← betaFast_eq I m hf i s] at hmain
    have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hf_pos)
    have hm_pos : 0 < mean I i j := mean_pos_of_eligible I hi
    have hm_ne : mean I i j ≠ 0 := ne_of_gt hm_pos
    have hf_ne : (f : ℝ) ≠ 0 := ne_of_gt hf_pos
    have hLHS : alphaFast I m f j / mean I i j = (alpha I m j / mean I i j) / (f : ℝ) := by
      rw [alphaFast_eq I m hf j]
      ring
    have hRHS1 : (betaFast I m f i s + I.weight j * ((f : ℝ) * (s : ℝ) / mean I i j + 1)) / (f : ℝ) =
        betaFast I m f i s / (f : ℝ) + I.weight j * ((s : ℝ) / mean I i j + (f : ℝ)⁻¹) := by
      field_simp [hm_ne, hf_ne]
    have hinv_le : (f : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hf_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    have hs_le : (s : ℝ) / mean I i j ≤ ((s : ℝ) + 1 / 2) / mean I i j := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hm_pos)
      linarith
    have hmul_le : I.weight j * ((s : ℝ) / mean I i j + (f : ℝ)⁻¹) ≤
        I.weight j * (((s : ℝ) + 1 / 2) / mean I i j + 1 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hs_le hinv_le) (I.weight_nonneg j)
    linarith
