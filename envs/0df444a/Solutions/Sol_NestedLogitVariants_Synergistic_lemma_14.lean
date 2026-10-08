-- Prove2me | solution 1 for NestedLogitVariants.Synergistic.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:42:32.074116+00:00
-- url     : https://prove2.me/submissions/cb0229ae-1b68-421d-8945-bc93c6a0d233

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation
import Definitions.Def_NestedLogitVariants_Synergistic_Factor
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NestedLogitVariants.Synergistic

theorem prep_V_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

theorem prep_R_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ R I i S :=
  div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le) (prep_V_nonneg I hI i S)

theorem prep_lp4_opt_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ)
    (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hfeas : LP4Feasible I A (2 * xh) (fun i => 2 * yh i) := by
    constructor
    · rw [← Finset.mul_sum]
      nlinarith [hopt.1.1]
    · intro i S hS
      have hc := hopt.1.2 i S hS
      have hwr : 0 ≤ nestWeight I i S * R I i S :=
        mul_nonneg (Real.rpow_nonneg (prep_V_nonneg I hI i S) _) (prep_R_nonneg I hI i S)
      nlinarith
  have hm := hopt.2 (2 * xh) (fun i => 2 * yh i) hfeas
  linarith

theorem xh_yh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    (∀ i, 0 ≤ yh i) ∧ 0 ≤ xh := by
  constructor
  · intro i
    have h := hopt.1.2 i (nbr n 0) ⟨0, Nat.zero_le _, rfl⟩
    simpa [nbr, nestWeight, V, hfc i, Real.zero_rpow (hI.γ_pos i).ne'] using h
  · exact prep_lp4_opt_nonneg I hI _ xh yh hopt

theorem lp7_feasible_lp3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i) :
    ∀ x (y : ι → ℝ), LP7Feasible I x y → LP3Feasible I x y := by
  intro x y h
  refine ⟨h.1, ?_⟩
  intro i S
  let z : Fin n → ℝ := fun j => if j ∈ S then 1 else 0
  have hz : z ∈ NestedLogitVariants.LP.box n := by
    intro j _
    dsimp [z]
    split_ifs <;> norm_num
  have hbound := h.2 i z hz
  simpa [F8, z, nestWeight, R, V, hfc i, mul_ite, Finset.sum_ite] using hbound

theorem prep_nbr_succ {n k : ℕ} (hk : k < n) :
    nbr n (k + 1) = insert ⟨k, hk⟩ (nbr n k) := by
  ext j
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem prep_nbr_weight_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    0 < ∑ j ∈ nbr n k, I.v i j := by
  have hn : 0 < n := hk.trans_le hkn
  have hmem : (⟨0, hn⟩ : Fin n) ∈ nbr n k := by simp [nbr, hk]
  exact (hI.v_pos i ⟨0, hn⟩).trans_le
    (Finset.single_le_sum (fun j _ => (hI.v_pos i j).le) hmem)

theorem R_nbr_antitone {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (i : ι) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) :
    R I i (nbr n j) ≤ R I i (nbr n (j - 1)) := by
  let k : Fin n := ⟨j - 1, by omega⟩
  have hins : nbr n j = insert k (nbr n (j - 1)) := by
    simpa only [k, Nat.sub_add_cancel (by omega : 1 ≤ j)] using
      prep_nbr_succ (n := n) (k := j - 1) (by omega)
  have hnot : k ∉ nbr n (j - 1) := by simp [nbr, k]
  have hq := prep_nbr_weight_pos I hI i (j - 1) (by omega) (by omega)
  have hq' : 0 < I.v i k + ∑ a ∈ nbr n (j - 1), I.v i a :=
    add_pos (hI.v_pos i k) hq
  have hrw : I.r i k * (∑ a ∈ nbr n (j - 1), I.v i a) ≤
      ∑ a ∈ nbr n (j - 1), I.r i a * I.v i a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hak : a ≤ k := by
      have hv := (Finset.mem_filter.mp ha).2
      change a.val ≤ j - 1
      omega
    exact mul_le_mul_of_nonneg_right (hI.r_antitone i hak) (hI.v_pos i a).le
  simp only [R, V, hfc i, zero_add, hins, Finset.sum_insert hnot]
  apply (div_le_div_iff₀ hq' hq).mpr
  nlinarith [mul_le_mul_of_nonneg_left hrw (hI.v_pos i k).le]



theorem qsum_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : ℕ) : 0 ≤ qsum I i k :=
  Finset.sum_nonneg fun j _ => (hI.v_pos i j).le

theorem Rsum_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : ℕ) : 0 ≤ Rsum I i k :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le

theorem Rsum_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hr : ∀ i j, 0 < I.r i j) (i : ι) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    0 < Rsum I i k := by
  have hn : 0 < n := hk.trans_le hkn
  exact (mul_pos (hr i ⟨0, hn⟩) (hI.v_pos i ⟨0, hn⟩)).trans_le
    (Finset.single_le_sum (fun j _ => mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le)
      (by simp [nbr, hk] : (⟨0, hn⟩ : Fin n) ∈ nbr n k))

theorem R_nbr_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hfc : ∀ i, I.vnp i = 0) (hr : ∀ i j, 0 < I.r i j)
    (i : ι) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : 0 < R I i (nbr n k) := by
  simpa [R, V, Rsum, hfc] using
    div_pos (Rsum_pos I hI hr i k hk hkn) (prep_nbr_weight_pos I hI i k hk hkn)

theorem qsum_succ {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (k : ℕ) (hk : k < n) :
    qsum I i (k + 1) = qsum I i k + I.v i ⟨k, hk⟩ := by
  have hnot : (⟨k, hk⟩ : Fin n) ∉ nbr n k := by simp [nbr]
  simp only [qsum, prep_nbr_succ hk, Finset.sum_insert hnot]
  ring

theorem Rsum_succ {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (k : ℕ) (hk : k < n) :
    Rsum I i (k + 1) = Rsum I i k + I.r i ⟨k, hk⟩ * I.v i ⟨k, hk⟩ := by
  have hnot : (⟨k, hk⟩ : Fin n) ∉ nbr n k := by simp [nbr]
  simp only [Rsum, prep_nbr_succ hk, Finset.sum_insert hnot]
  ring

theorem qsum_mono {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) : Monotone (qsum I i) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro j _ _
    exact (hI.v_pos i j).le

theorem Rsum_mono {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) : Monotone (Rsum I i) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro j _ _
    exact mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le

theorem R_nbr_eq {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hfc : ∀ i, I.vnp i = 0) (i : ι) (k : ℕ) : R I i (nbr n k) = Rsum I i k / qsum I i k := by
  simp [R, V, Rsum, qsum, hfc]

theorem weight_nbr_eq {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hfc : ∀ i, I.vnp i = 0) (i : ι) (k : ℕ) : nestWeight I i (nbr n k) = qsum I i k ^ I.γ i := by
  simp [nestWeight, V, qsum, hfc]

theorem revenue_weight_mono {a b c d g : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) (hg : 1 ≤ g) :
    c / a * a ^ g ≤ d / b * b ^ g := by
  have hb : 0 < b := ha.trans_le hab
  have hm := Real.rpow_le_rpow ha.le hab (sub_nonneg.mpr hg)
  have hc' : c / a * a ^ g = c * a ^ (g - 1) := by
    rw [Real.rpow_sub_one ha.ne']; ring
  have hd' : d / b * b ^ g = d * b ^ (g - 1) := by
    rw [Real.rpow_sub_one hb.ne']; ring
  rw [hc', hd']
  exact mul_le_mul hcd hm (Real.rpow_nonneg ha.le _) (hc.trans hcd)


end NestedLogitVariants.Synergistic

open NestedLogitVariants.Synergistic

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (hn : 2 ≤ n)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α) :
    1 ≤ α := by
  obtain ⟨i, hi⟩ := hsyn
  have h1 := R_nbr_pos I hI hfc hr i 1 (by omega) (by omega)
  have h2 := R_nbr_pos I hI hfc hr i 2 (by omega) hn
  have hw1 : 0 < nestWeight I i (nbr n 1) := by
    rw [weight_nbr_eq I hfc]
    exact Real.rpow_pos_of_pos (prep_nbr_weight_pos I hI i 1 (by omega) (by omega)) _
  have ha : 1 ≤ R I i (nbr n 1) / R I i (nbr n 2) := by
    rw [le_div_iff₀ h2, one_mul]
    exact R_nbr_antitone I hI hfc ⟨i, hi⟩ i 2 (by omega) hn
  have hb : 1 ≤ R I i (nbr n 2) / R I i (nbr n 1) *
      (nestWeight I i (nbr n 2) / nestWeight I i (nbr n 1)) := by
    rw [div_mul_div_comm, le_div_iff₀ (mul_pos h1 hw1), one_mul]
    simp only [R_nbr_eq I hfc, weight_nbr_eq I hfc]
    apply revenue_weight_mono
    · exact prep_nbr_weight_pos I hI i 1 (by omega) (by omega)
    · exact Rsum_nonneg I hI i 1
    · exact qsum_mono I hI i (by omega : 1 ≤ 2)
    · exact Rsum_mono I hI i (by omega : 1 ≤ 2)
    · exact hi.le
  have ht : 1 ≤ alphaTerm I i 2 := by
    simpa [alphaTerm] using le_min ha hb
  exact ht.trans (hα.2 ⟨i, 2, by simp [hn], rfl⟩)
