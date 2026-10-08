-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.nest_max_eq_knapsack_max
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:28:45.453446+00:00
-- url     : https://prove2.me/submissions/debf7d01-c98e-4092-9541-200bb5462b18

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

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (i : ι) (x : ℝ) (hx : 0 ≤ x) (y : ℝ) :
    (∀ S : Finset (Fin n), nestWeight I i S * (R I i S - x) ≤ y) ↔
      (∀ ε : ℝ, 0 ≤ ε → (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - x) ≤ y) := by
  constructor
  · intro hall ε hε
    obtain ⟨S, hS, hK⟩ := kval_attained I i ε hε
    rw [hK]
    have hm := scaled_mono (V I i S) (I.vnp i + ε) (∑ j ∈ S, I.r i j * I.v i j)
      x (I.γ i) (v_nonneg I hI i S) (by unfold V; linarith)
      (num_nonneg I hI i S) hx (hI.γ_pos i) (hγ i) (num_zero I hI i S)
    exact hm.trans (hall S)
  · intro hall S
    let ε := ∑ j ∈ S, I.v i j
    have hε : 0 ≤ ε := Finset.sum_nonneg (fun j _ => (hI.v_pos i j).le)
    have hK := kval_ge I i ε hε S (le_refl _)
    have hb : 0 ≤ I.vnp i + ε := add_nonneg (hI.vnp_nonneg i) hε
    have hdiv := div_le_div_of_nonneg_right hK hb
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hdiv x) (Real.rpow_nonneg hb (I.γ i))
    exact hp.trans (hall ε hε)

#print axioms solution

