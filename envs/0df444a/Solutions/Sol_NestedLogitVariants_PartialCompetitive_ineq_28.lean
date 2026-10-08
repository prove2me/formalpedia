-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.ineq_28
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:32:30.750852+00:00
-- url     : https://prove2.me/submissions/bad5dec0-817e-4579-a875-fd6e97b05887

import Theorems.Thm_NestedLogitVariants_PartialCompetitive_zhat_optimal
import Theorems.Thm_NestedLogitVariants_PartialCompetitive_knapsack_relaxation
import Theorems.Thm_NestedLogitVariants_PartialCompetitive_xh_nonneg
open NestedLogitVariants.PartialCompetitive
open Finset
set_option maxHeartbeats 1000000
private lemma v_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ V I i S := by
  exact add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg (fun j _ => (hI.v_pos i j).le))

private lemma num_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ ∑ j ∈ S, I.r i j * I.v i j := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le)

private lemma r_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ R I i S :=
  div_nonneg (num_nonneg I hI i S) (v_nonneg I hI i S)

private lemma num_zero {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) (h : V I i S = 0) : ∑ j ∈ S, I.r i j * I.v i j = 0 := by
  have he : S = ∅ := by
    by_contra hn
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    have hv := Finset.single_le_sum (fun k (_ : k ∈ S) => (hI.v_pos i k).le) hj
    have hvn := hI.vnp_nonneg i
    have hvp := hI.v_pos i j
    unfold V at h
    linarith
  simp [he]

private lemma scaled_mono (a b N x g : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hN : 0 ≤ N) (hx : 0 ≤ x) (hg : 0 < g) (hg1 : g ≤ 1)
    (hzero : a = 0 → N = 0) :
    b ^ g * (N / b - x) ≤ a ^ g * (N / a - x) := by
  by_cases ha0 : a = 0
  · have hn := hzero ha0
    simp only [ha0, hn, zero_div, zero_sub, Real.zero_rpow (ne_of_gt hg), zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) (neg_nonpos.mpr hx)
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbp : 0 < b := lt_of_lt_of_le hap hab
    have hp := Real.rpow_le_rpow ha hab hg.le
    have hq := Real.rpow_le_rpow_of_nonpos hap hab (show g - 1 ≤ 0 by linarith)
    have hN' := mul_le_mul_of_nonneg_right hq hN
    have hx' := mul_le_mul_of_nonneg_right hp hx
    rw [Real.rpow_sub_one (ne_of_gt hap), Real.rpow_sub_one (ne_of_gt hbp)] at hN'
    have ea : a ^ g * (N / a - x) = (a ^ g / a) * N - a ^ g * x := by ring
    have eb : b ^ g * (N / b - x) = (b ^ g / b) * N - b ^ g * x := by ring
    rw [ea, eb]
    linarith

private lemma kval_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ)
    (hε : 0 ≤ ε) : 0 ≤ Kval I i ε := by
  unfold Kval
  rw [dif_pos hε]
  exact le_trans (by simp) (Finset.le_sup' (fun S => ∑ j ∈ S, I.r i j * I.v i j)
    (show ∅ ∈ knapFeasible I i ε by simp [knapFeasible, hε]))

private lemma kval_ge {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ)
    (hε : 0 ≤ ε) (S : Finset (Fin n)) (hS : ∑ j ∈ S, I.v i j ≤ ε) :
    (∑ j ∈ S, I.r i j * I.v i j) ≤ Kval I i ε := by
  unfold Kval
  rw [dif_pos hε]
  exact Finset.le_sup' (fun S => ∑ j ∈ S, I.r i j * I.v i j) (by simp [knapFeasible, hS])

private lemma kval_attained {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ)
    (hε : 0 ≤ ε) : ∃ S : Finset (Fin n),
      (∑ j ∈ S, I.v i j) ≤ ε ∧ Kval I i ε = ∑ j ∈ S, I.r i j * I.v i j := by
  have hne : (knapFeasible I i ε).Nonempty := ⟨∅, by simp [knapFeasible, hε]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup' hne (fun S => ∑ j ∈ S, I.r i j * I.v i j)
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  simpa only [Kval, dif_pos hε] using hmax

private lemma greedy_load_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    ∑ j ∈ Shat I i ε, I.v i j ≤ ε := by
  have hg := (zhat_optimal I hI i ε hε).1
  calc
    ∑ j ∈ Shat I i ε, I.v i j = ∑ j ∈ Shat I i ε, I.v i j * zhat I i ε j := by
      apply sum_congr rfl
      intro j hj
      rw [(mem_filter.mp hj).2, mul_one]
    _ ≤ ∑ j, I.v i j * zhat I i ε j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ =>
        mul_nonneg (hI.v_pos i j).le (hg.2 j).1)
    _ ≤ ε := hg.1

private lemma kval_le_greedy {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    Kval I i ε ≤ ∑ j, I.r i j * I.v i j * zhat I i ε j := by
  obtain ⟨z, hz, hK⟩ := (knapsack_relaxation I hI i ε hε).2
  exact hK.trans ((zhat_optimal I hI i ε hε).2.1 z hz)

private lemma candidate_scaled_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (hγ : ∀ i, I.γ i ≤ 1)
    (x : ℝ) (y : ι → ℝ) (hx : 0 ≤ x) (hf : LP4Feasible I (candidates I) x y)
    (i : ι) (ε : ℝ) (S : Finset (Fin n)) (hS : S ∈ candidates I i)
    (hload : ∑ j ∈ S, I.v i j ≤ ε) :
    (I.vnp i + ε) ^ I.γ i * ((∑ j ∈ S, I.r i j * I.v i j) / (I.vnp i + ε) - x) ≤ y i := by
  have hm := scaled_mono (V I i S) (I.vnp i + ε) (∑ j ∈ S, I.r i j * I.v i j)
    x (I.γ i) (v_nonneg I hI i S) (by unfold V; linarith)
    (num_nonneg I hI i S) hx (hI.γ_pos i) (hγ i) (num_zero I hI i S)
  exact hm.trans (hf.2 i S hS)

private lemma greedy_zero_or_one {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (i : ι) (ε : ℝ) (hε : 0 ≤ ε)
    (j : Fin n) (hnf : zhat I i ε j ∉ Set.Ioo (0 : ℝ) 1) :
    zhat I i ε j = 0 ∨ zhat I i ε j = 1 := by
  have hg := (zhat_optimal I hI i ε hε).1.2 j
  have hle : zhat I i ε j ≤ 1 := by
    exact hg.2.trans (by split_ifs <;> norm_num)
  by_cases hz : zhat I i ε j = 0
  · exact Or.inl hz
  · right
    by_contra hne
    exact hnf ⟨lt_of_le_of_ne hg.1 (Ne.symm hz), lt_of_le_of_ne hle hne⟩

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) (k : Fin n) (hk : zhat I i ε k ∈ Set.Ioo (0 : ℝ) 1) :
    (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - 2 * xh) ≤ 2 * yh i := by
  classical
  have hg := zhat_optimal I hI i ε hε
  have hke : I.v i k ≤ ε := by
    by_contra h
    have := (hg.1.2 k).2
    simp only [h, if_false] at this
    linarith [hk.1]
  have hx := xh_nonneg I hI hγ hn xh yh hopt
  have hA := candidate_scaled_bound I hI hγ xh yh hx hopt.1 i ε (Shat I i ε)
    (Or.inl ⟨ε, hε, rfl⟩) (greedy_load_bound I hI i ε hε)
  have hB := candidate_scaled_bound I hI hγ xh yh hx hopt.1 i ε {k}
    (Or.inr ⟨k, rfl⟩) (by simpa using hke)
  simp only [sum_singleton] at hB
  have hobj : (∑ j, I.r i j * I.v i j * zhat I i ε j) ≤
      (∑ j ∈ Shat I i ε, I.r i j * I.v i j) + I.r i k * I.v i k := by
    calc
      _ ≤ ∑ j, ((if j ∈ Shat I i ε then I.r i j * I.v i j else 0) +
          (if j = k then I.r i k * I.v i k else 0)) := by
        apply sum_le_sum
        intro j _
        by_cases hjk : j = k
        · subst j
          have hn : k ∉ Shat I i ε := by
            simp only [Shat, mem_filter, mem_univ, true_and]
            exact ne_of_lt hk.2
          simp only [hn, if_false, if_true, zero_add]
          exact mul_le_of_le_one_right (mul_nonneg (hI.r_nonneg i k) (hI.v_pos i k).le) hk.2.le
        · have hnf : zhat I i ε j ∉ Set.Ioo (0 : ℝ) 1 := fun hj => hjk (hg.2.2 j k hj hk)
          rcases greedy_zero_or_one I hI i ε hε j hnf with hz | hz
          · have hn : j ∉ Shat I i ε := by simp [Shat, hz]
            simp [hjk, hn, hz]
          · have hm : j ∈ Shat I i ε := by simp [Shat, hz]
            simp [hjk, hm, hz]
      _ = _ := by
        rw [sum_add_distrib]
        simp only [sum_ite_mem, univ_inter, sum_ite_eq', mem_univ, if_true]
  have hK := (kval_le_greedy I hI i ε hε).trans hobj
  have hb : 0 ≤ I.vnp i + ε := add_nonneg (hI.vnp_nonneg i) hε
  have hdiv := div_le_div_of_nonneg_right hK hb
  have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hdiv (2 * xh))
    (Real.rpow_nonneg hb (I.γ i))
  have heq : (I.vnp i + ε) ^ I.γ i *
      (((∑ j ∈ Shat I i ε, I.r i j * I.v i j) + I.r i k * I.v i k) / (I.vnp i + ε) - 2 * xh) =
      (I.vnp i + ε) ^ I.γ i * ((∑ j ∈ Shat I i ε, I.r i j * I.v i j) / (I.vnp i + ε) - xh) +
      (I.vnp i + ε) ^ I.γ i * (I.r i k * I.v i k / (I.vnp i + ε) - xh) := by ring
  rw [heq] at hp
  linarith

#print axioms solution

