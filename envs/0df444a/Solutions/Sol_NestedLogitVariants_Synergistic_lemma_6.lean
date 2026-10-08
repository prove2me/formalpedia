-- Prove2me | solution 1 for NestedLogitVariants.Synergistic.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:42:47.46151+00:00
-- url     : https://prove2.me/submissions/bd79b7a6-d8f8-4ac6-a30c-d6765ca163b4

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

theorem lemma_14 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
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

end NestedLogitVariants.Synergistic





set_option autoImplicit false
set_option linter.unusedVariables false
namespace NestedLogitVariants.Synergistic

noncomputable def fracPrefix {n : ℕ} (k : Fin n) (ρ : ℝ) (j : Fin n) : ℝ :=
  if j < k then 1 else if j = k then ρ else 0

theorem fracPrefix_shape {n : ℕ} (k : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsFracPrefix (fracPrefix k ρ) k := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj; simp [fracPrefix, hj]
  · simpa [fracPrefix] using hρ
  · intro j hj; simp [fracPrefix, not_lt.mpr hj.le, ne_of_gt hj]

theorem fracPrefix_box {n : ℕ} (k : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    fracPrefix k ρ ∈ NestedLogitVariants.LP.box n := by
  intro j _
  dsimp [fracPrefix]
  split_ifs <;> simp_all

theorem fracPrefix_sum {n : ℕ} (f : Fin n → ℝ) (k : Fin n) (ρ : ℝ) :
    (∑ j, f j * fracPrefix k ρ j) = (∑ j ∈ nbr n k.val, f j) + f k * ρ := by
  have he : ∀ j, f j * fracPrefix k ρ j =
      (if j.val < k.val then f j else 0) + (if j = k then f k * ρ else 0) := by
    intro j
    by_cases hj : j < k
    · have hjn : j ≠ k := ne_of_lt hj
      simp [fracPrefix, hj, hjn, show j.val < k.val from hj]
    · by_cases heq : j = k
      · subst j; simp [fracPrefix]
      · simp [fracPrefix, hj, heq, show ¬j.val < k.val from hj]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp [nbr, Finset.sum_filter]

theorem qsum_zero {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) : qsum I i 0 = 0 := by
  simp [qsum, nbr]

theorem Rsum_zero {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) : Rsum I i 0 = 0 := by
  simp [Rsum, nbr]

theorem qsum_all {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) :
    qsum I i n = ∑ j, I.v i j := by
  simp [qsum, nbr]

theorem capacity_prefix {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hn : 0 < n) (i : ι) (C : ℝ) (hC0 : 0 ≤ C) (hCn : C ≤ qsum I i n) :
    ∃ k : Fin n, ∃ ρ ∈ Set.Icc (0 : ℝ) 1,
      (∑ j, I.v i j * fracPrefix k ρ j) = C := by
  have hex : ∃ k : ℕ, k < n ∧ C ≤ qsum I i (k + 1) := by
    refine ⟨n - 1, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel hn] using hCn
  let k := Nat.find hex
  have hk : k < n ∧ C ≤ qsum I i (k + 1) := Nat.find_spec hex
  have hqC : qsum I i k ≤ C := by
    by_cases hk0 : k = 0
    · simpa [hk0, qsum_zero] using hC0
    · by_contra! h
      have hkp : k - 1 < n ∧ C ≤ qsum I i (k - 1 + 1) := by
        refine ⟨by omega, ?_⟩
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using h.le
      have hmin := Nat.find_min' hex hkp
      change k ≤ k - 1 at hmin
      omega
  let j : Fin n := ⟨k, hk.1⟩
  let ρ := (C - qsum I i k) / I.v i j
  have hρ0 : 0 ≤ ρ := div_nonneg (sub_nonneg.mpr hqC) (hI.v_pos i j).le
  have hρ1 : ρ ≤ 1 := by
    apply (div_le_iff₀ (hI.v_pos i j)).mpr
    have hstep := qsum_succ I i k hk.1
    dsimp [j] at *
    linarith [hk.2]
  refine ⟨j, ρ, ⟨hρ0, hρ1⟩, ?_⟩
  rw [fracPrefix_sum]
  change qsum I i k + I.v i j * ((C - qsum I i k) / I.v i j) = C
  field_simp [(hI.v_pos i j).ne']
  <;> ring

theorem greedy_revenue {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (z : Fin n → ℝ) (hz : z ∈ NestedLogitVariants.LP.box n)
    (k : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hmass : (∑ j, I.v i j * fracPrefix k ρ j) = ∑ j, I.v i j * z j) :
    (∑ j, I.r i j * I.v i j * z j) ≤ ∑ j, I.r i j * I.v i j * fracPrefix k ρ j := by
  have hp : ∀ j, I.r i j * (I.v i j * (z j - fracPrefix k ρ j)) ≤
      I.r i k * (I.v i j * (z j - fracPrefix k ρ j)) := by
    intro j
    rcases lt_trichotomy j k with hj | rfl | hj
    · have hd : I.v i j * (z j - fracPrefix k ρ j) ≤ 0 := by
        simp only [fracPrefix, if_pos hj]
        exact mul_nonpos_of_nonneg_of_nonpos (hI.v_pos i j).le (sub_nonpos.mpr (hz j (Set.mem_univ j)).2)
      exact mul_le_mul_of_nonpos_right (hI.r_antitone i hj.le) hd
    · exact le_rfl
    · have hg : fracPrefix k ρ j = 0 := (fracPrefix_shape k ρ hρ).2.2 j hj
      have hd : 0 ≤ I.v i j * (z j - fracPrefix k ρ j) := by
        rw [hg, sub_zero]
        exact mul_nonneg (hI.v_pos i j).le (hz j (Set.mem_univ j)).1
      exact mul_le_mul_of_nonneg_right (hI.r_antitone i hj.le) hd
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp j)
  have hm : (∑ j, I.v i j * (z j - fracPrefix k ρ j)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hmass, sub_self]
  rw [← Finset.mul_sum, hm, mul_zero] at hs
  simp only [mul_sub, ← mul_assoc, Finset.sum_sub_distrib] at hs
  linarith

theorem greedy_F8 {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hn : 0 < n) (i : ι) (x : ℝ) (z : Fin n → ℝ) (hz : z ∈ NestedLogitVariants.LP.box n) :
    ∃ k : Fin n, ∃ ρ ∈ Set.Icc (0 : ℝ) 1, F8 I i z x ≤ F8 I i (fracPrefix k ρ) x := by
  have hC0 : 0 ≤ ∑ j, I.v i j * z j := Finset.sum_nonneg fun j _ =>
    mul_nonneg (hI.v_pos i j).le (hz j (Set.mem_univ j)).1
  have hCn : (∑ j, I.v i j * z j) ≤ qsum I i n := by
    rw [qsum_all]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hz j (Set.mem_univ j)).2 (hI.v_pos i j).le
  obtain ⟨k, ρ, hρ, hm⟩ := capacity_prefix I hI hn i _ hC0 hCn
  refine ⟨k, ρ, hρ, ?_⟩
  dsimp [F8]
  rw [hm]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC0 _)
  apply sub_le_sub_right
  exact div_le_div_of_nonneg_right (greedy_revenue I hI i z hz k ρ hρ hm) hC0

end NestedLogitVariants.Synergistic



set_option autoImplicit false
set_option linter.unusedVariables false
namespace NestedLogitVariants.Synergistic

theorem F8_fracPrefix_eq {ι : Type*} {n : ℕ} (I : Instance ι n)
    (i : ι) (k : Fin n) (ρ x : ℝ) :
    F8 I i (fracPrefix k ρ) x =
      (qsum I i k.val + I.v i k * ρ) ^ I.γ i *
        ((Rsum I i k.val + I.r i k * I.v i k * ρ) / (qsum I i k.val + I.v i k * ρ) - x) := by
  simp only [F8, fracPrefix_sum, qsum, Rsum]

theorem F8_fracPrefix_continuousOn {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : Fin n) (x : ℝ) :
    ContinuousOn (fun ρ => F8 I i (fracPrefix k ρ) x) (Set.Icc 0 1) := by
  simp_rw [F8_fracPrefix_eq]
  by_cases hk0 : k.val = 0
  · simp only [hk0, qsum_zero, Rsum_zero, zero_add]
    have hc : Continuous (fun ρ : ℝ => (I.v i k * ρ) ^ I.γ i * (I.r i k - x)) :=
      ((continuous_const.mul continuous_id).rpow_const (fun _ => Or.inr (hI.γ_pos i).le)).mul continuous_const
    apply hc.continuousOn.congr
    intro ρ hρ
    by_cases hρ0 : ρ = 0
    · simp [hρ0, Real.zero_rpow (hI.γ_pos i).ne']
    · have hd : I.v i k * ρ ≠ 0 := mul_ne_zero (hI.v_pos i k).ne' hρ0
      dsimp only
      rw [mul_assoc (I.r i k), mul_div_cancel_right₀ _ hd]
  · have hq : 0 < qsum I i k.val := prep_nbr_weight_pos I hI i k.val (by omega) k.isLt.le
    have hden : ContinuousOn (fun ρ : ℝ => qsum I i k.val + I.v i k * ρ) (Set.Icc 0 1) :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    have hnum : ContinuousOn (fun ρ : ℝ => Rsum I i k.val + I.r i k * I.v i k * ρ) (Set.Icc 0 1) :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    exact (hden.rpow_const (fun _ _ => Or.inr (hI.γ_pos i).le)).mul
      ((hnum.div hden (fun ρ hρ =>
        (add_pos_of_pos_of_nonneg hq (mul_nonneg (hI.v_pos i k).le hρ.1)).ne')).sub continuousOn_const)


end NestedLogitVariants.Synergistic

open NestedLogitVariants.Synergistic

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hn1 : 0 < n) (i : ι) (x : ℝ) :
    ∃ z ∈ NestedLogitVariants.LP.box n, (∀ z' ∈ NestedLogitVariants.LP.box n, F8 I i z' x ≤ F8 I i z x) ∧ ∃ k : Fin n, IsFracPrefix z k := by
  classical
  have hmax : ∀ k : Fin n, ∃ ρ ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F8 I i (fracPrefix k t) x ≤ F8 I i (fracPrefix k ρ) x := by
    intro k
    obtain ⟨ρ, hρ, hm⟩ := isCompact_Icc.exists_isMaxOn
      (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
      (F8_fracPrefix_continuousOn I hI i k x)
    exact ⟨ρ, hρ, hm⟩
  choose ρ hρ hm using hmax
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin n => F8 I i (fracPrefix k (ρ k)) x)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn1⟩, Finset.mem_univ _⟩)
  refine ⟨fracPrefix k (ρ k), fracPrefix_box k (ρ k) (hρ k), ?_, k, fracPrefix_shape k (ρ k) (hρ k)⟩
  intro z hz
  obtain ⟨j, t, ht, hg⟩ := greedy_F8 I hI hn1 i x z hz
  exact hg.trans ((hm j t ht).trans (hk j (Finset.mem_univ _)))
