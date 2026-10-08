-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:32:27.787976+00:00
-- url     : https://prove2.me/submissions/b1583b8d-9533-40ff-b46b-3fe80415b5f0

import Theorems.Thm_NestedLogitVariants_PartialCompetitive_nest_max_eq_knapsack_max
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

private lemma lp3_feas_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (hn : 0 < n) (x : ℝ) (y : ι → ℝ)
    (hf : LP3Feasible I x y) : 0 ≤ x := by
  by_contra hx
  have hx : x < 0 := lt_of_not_ge hx
  let j : Fin n := ⟨0, hn⟩
  have hy : ∀ i, 0 < y i := by
    intro i
    have hv : 0 < V I i {j} := by simp only [V, sum_singleton]; linarith [hI.vnp_nonneg i, hI.v_pos i j]
    have hw : 0 < nestWeight I i {j} := Real.rpow_pos_of_pos hv _
    exact lt_of_lt_of_le (mul_pos hw (by linarith [r_nonneg I hI i {j}])) (hf.2 i {j})
  have hs : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => hy i) Finset.univ_nonempty
  have hvx : I.v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hI.v0_nonneg hx.le
  linarith [hf.1]

private lemma lp10_feas_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (hn : 0 < n) (x : ℝ) (y : ι → ℝ)
    (hf : LP10Feasible I x y) : 0 ≤ x := by
  by_contra hx
  have hx : x < 0 := lt_of_not_ge hx
  let j : Fin n := ⟨0, hn⟩
  have hy : ∀ i, 0 < y i := by
    intro i
    have he : 0 ≤ I.v i j := (hI.v_pos i j).le
    have hv : 0 < I.vnp i + I.v i j := by linarith [hI.vnp_nonneg i, hI.v_pos i j]
    have hr : 0 ≤ Kval I i (I.v i j) / (I.vnp i + I.v i j) :=
      div_nonneg (kval_nonneg I i _ he) hv.le
    exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hv _) (by linarith)) (hf.2 i _ he)
  have hs : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => hy i) Finset.univ_nonempty
  have hvx : I.v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hI.v0_nonneg hx.le
  linarith [hf.1]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n) (x : ℝ) (y : ι → ℝ) :
    LP3Optimal I x y ↔ LP10Optimal I x y := by
  classical
  have he : ∀ (a : ℝ) (b : ι → ℝ), LP3Feasible I a b ↔ LP10Feasible I a b := by
    intro a b
    rcases isEmpty_or_nonempty ι with hi | hi
    · letI := hi
      simp [LP3Feasible, LP10Feasible]
    · letI := hi
      constructor
      · intro hf
        have hx := lp3_feas_nonneg I hI hn a b hf
        exact ⟨hf.1, fun i => (nest_max_eq_knapsack_max I hI hγ i a hx (b i)).mp (hf.2 i)⟩
      · intro hf
        have hx := lp10_feas_nonneg I hI hn a b hf
        exact ⟨hf.1, fun i => (nest_max_eq_knapsack_max I hI hγ i a hx (b i)).mpr (hf.2 i)⟩
  constructor
  · rintro ⟨hf, ho⟩
    exact ⟨(he x y).mp hf, fun a b hab => ho a b ((he a b).mpr hab)⟩
  · rintro ⟨hf, ho⟩
    exact ⟨(he x y).mpr hf, fun a b hab => ho a b ((he a b).mp hab)⟩

#print axioms solution

