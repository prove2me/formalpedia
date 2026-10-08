-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.xh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:29:31.593981+00:00
-- url     : https://prove2.me/submissions/9190e1d5-55a4-4a73-9a09-535eb7d6d85e

import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack
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

private lemma lp4_opt_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (A : ι → Set (Finset (Fin n))) (x : ℝ) (y : ι → ℝ)
    (ho : LP4Optimal I A x y) : 0 ≤ x := by
  have hf : LP4Feasible I A (2 * x) (fun i => 2 * y i) := by
    constructor
    · rw [← Finset.mul_sum]
      nlinarith [ho.1.1]
    · intro i S hS
      have h := ho.1.2 i S hS
      have hw : 0 ≤ nestWeight I i S := Real.rpow_nonneg (v_nonneg I hI i S) _
      have hr := r_nonneg I hI i S
      nlinarith [mul_nonneg hw hr]
  have h := ho.2 (2 * x) (fun i => 2 * y i) hf
  linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    0 ≤ xh := by
  exact lp4_opt_nonneg I hI (candidates I) xh yh hopt

#print axioms solution

