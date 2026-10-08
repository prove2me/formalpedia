-- Prove2me | solution 1 for NestedLogitVariants.Synergistic.ineq_25
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:42:44.614823+00:00
-- url     : https://prove2.me/submissions/5dbddefa-5323-4017-9469-6131efed0cc9

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

theorem revenue_power_eq {q : ℝ} (hq : 0 < q) (A g : ℝ) :
    q ^ g * (A / q) = A / q ^ (1 - g) := by
  rw [Real.rpow_sub hq, Real.rpow_one]
  field_simp

theorem endpoint_revenue_bound {q v A B g ρ : ℝ}
    (hq : 0 < q) (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg : 0 < g) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (q + v * ρ) ^ g * ((A + B * ρ) / (q + v * ρ)) ≤
      max (q ^ g * (A / q)) ((q + v) ^ g * ((A + B) / (q + v))) := by
  have hqρ : 0 < q + v * ρ := add_pos_of_pos_of_nonneg hq (mul_nonneg hv hρ.1)
  have hq1 : 0 < q + v := add_pos_of_pos_of_nonneg hq hv
  have hqq1 : q + v * ρ ≤ q + v := by nlinarith [hρ.2]
  have hAA1 : A + B * ρ ≤ A + B := by nlinarith [hρ.2]
  by_cases hg1 : 1 ≤ g
  · apply le_trans _ (le_max_right _ _)
    simpa only [mul_comm] using revenue_weight_mono hqρ
      (add_nonneg hA (mul_nonneg hB hρ.1)) hqq1 hAA1 hg1
  · have hp0 : 0 ≤ 1 - g := by linarith
    have hp1 : 1 - g ≤ 1 := by linarith
    rw [revenue_power_eq hqρ, revenue_power_eq hq, revenue_power_eq hq1]
    let M := max (A / q ^ (1 - g)) ((A + B) / (q + v) ^ (1 - g))
    have hM : 0 ≤ M := (div_nonneg hA (Real.rpow_nonneg hq.le _)).trans (le_max_left _ _)
    have he0 : A ≤ M * q ^ (1 - g) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hq _)).mp (le_max_left _ _)
    have he1 : A + B ≤ M * (q + v) ^ (1 - g) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hq1 _)).mp (le_max_right _ _)
    have hc := (Real.concaveOn_rpow hp0 hp1).2 hq.le hq1.le
      (sub_nonneg.mpr hρ.2) hρ.1 (by ring : (1 - ρ) + ρ = 1)
    have heq : (1 - ρ) * q + ρ * (q + v) = q + v * ρ := by ring
    simp only [smul_eq_mul, heq] at hc
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hqρ _)).mpr
    change A + B * ρ ≤ M * (q + v * ρ) ^ (1 - g)
    have hh0 := mul_le_mul_of_nonneg_left he0 (sub_nonneg.mpr hρ.2)
    have hh1 := mul_le_mul_of_nonneg_left he1 hρ.1
    have hhc := mul_le_mul_of_nonneg_left hc hM
    nlinarith only [hh0, hh1, hhc]

theorem scaled_bound_mono {w R x y a b : ℝ}
    (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) (hab : a ≤ b)
    (ha : w * (R - a * x) ≤ a * y) : w * (R - b * x) ≤ b * y := by
  calc
    w * (R - b * x) ≤ w * (R - a * x) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (mul_le_mul_of_nonneg_right hab hx) R) hw
    _ ≤ a * y := ha
    _ ≤ b * y := mul_le_mul_of_nonneg_right hab hy

theorem shrink_weight_bound {w W z a : ℝ}
    (hw : 0 ≤ w) (hW : w ≤ W) (ha : 0 ≤ a) (h : W * z ≤ a) : w * z ≤ a := by
  by_cases hz : 0 ≤ z
  · exact (mul_le_mul_of_nonneg_right hW hz).trans h
  · exact (mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_ge hz)).trans ha

end NestedLogitVariants.Synergistic


set_option autoImplicit false
set_option linter.unusedVariables false
namespace NestedLogitVariants.Synergistic

theorem last_revenue_le_sum {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : Fin n) : I.r i k * qsum I i k.val ≤ Rsum I i k.val := by
  rw [qsum, Rsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := by
    have h := (Finset.mem_filter.mp hj).2
    exact le_of_lt h
  exact mul_le_mul_of_nonneg_right (hI.r_antitone i hjk) (hI.v_pos i j).le

theorem fractional_R_le {q v A r ρ : ℝ} (hq : 0 < q) (hv : 0 ≤ v)
    (hρ : 0 ≤ ρ) (hr : r * q ≤ A) :
    (A + r * v * ρ) / (q + v * ρ) ≤ A / q := by
  have hqρ := add_pos_of_pos_of_nonneg hq (mul_nonneg hv hρ)
  apply (div_le_div_iff₀ hqρ hq).mpr
  nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hv hρ)]

theorem ineq_20 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (R I i (nbr n (k - 1)) / R I i (nbr n k)) * yh i ≥
      (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i *
        ((Rsum I i (k - 1) + I.r i ⟨k - 1, by omega⟩ * I.v i ⟨k - 1, by omega⟩ * ρ) / (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) -
          (R I i (nbr n (k - 1)) / R I i (nbr n k)) * xh) := by
  let j : Fin n := ⟨k - 1, by omega⟩
  let q := qsum I i (k - 1)
  let A := Rsum I i (k - 1)
  let a := R I i (nbr n (k - 1)) / R I i (nbr n k)
  let Q := q + I.v i j * ρ
  let Z := (A + I.r i j * I.v i j * ρ) / Q
  have hq : 0 < q := prep_nbr_weight_pos I hI i (k - 1) (by omega) (by omega)
  have hQ : 0 < Q := add_pos_of_pos_of_nonneg hq (mul_nonneg (hI.v_pos i j).le hρ.1)
  have hRk := R_nbr_pos I hI hfc hr i k (by omega) hkn
  have ha : 0 ≤ a := div_nonneg (prep_R_nonneg I hI i _) hRk.le
  have haR : a * R I i (nbr n k) = R I i (nbr n (k - 1)) := div_mul_cancel₀ _ hRk.ne'
  have hZ : Z ≤ R I i (nbr n (k - 1)) := by
    rw [R_nbr_eq I hfc]
    exact fractional_R_le hq (hI.v_pos i j).le hρ.1 (last_revenue_le_sum I hI i j)
  have hQk : Q ≤ qsum I i k := by
    have hstep := qsum_succ I i (k - 1) (by omega)
    have hnat : k - 1 + 1 = k := by omega
    rw [hnat] at hstep
    dsimp [Q, q, j]
    rw [hstep]
    nlinarith [hρ.2, hI.v_pos i j]
  have hw : Q ^ I.γ i ≤ nestWeight I i (nbr n k) := by
    rw [weight_nbr_eq I hfc]
    exact Real.rpow_le_rpow hQ.le hQk (hI.γ_pos i).le
  have hy := (xh_yh_nonneg I hI hfc hsyn xh yh hopt).1 i
  have hb := hopt.1.2 i (nbr n k) ⟨k, hkn, rfl⟩
  have hW : 0 ≤ nestWeight I i (nbr n k) := Real.rpow_nonneg (prep_V_nonneg I hI i _) _
  have hbound : nestWeight I i (nbr n k) * (Z - a * xh) ≤ a * yh i := by
    calc
      _ ≤ nestWeight I i (nbr n k) * (R I i (nbr n (k - 1)) - a * xh) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hZ _) hW
      _ = a * (nestWeight I i (nbr n k) * (R I i (nbr n k) - xh)) := by
        rw [← haR]; ring
      _ ≤ a * yh i := mul_le_mul_of_nonneg_left hb ha
  exact shrink_weight_bound (Real.rpow_nonneg hQ.le _) hw (mul_nonneg ha hy) hbound

theorem ineq_22 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    max 1 (R I i (nbr n k) / R I i (nbr n (k - 1)) * (nestWeight I i (nbr n k) / nestWeight I i (nbr n (k - 1)))) * yh i ≥
      (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i *
        ((Rsum I i (k - 1) + I.r i ⟨k - 1, by omega⟩ * I.v i ⟨k - 1, by omega⟩ * ρ) / (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) -
          max 1 (R I i (nbr n k) / R I i (nbr n (k - 1)) * (nestWeight I i (nbr n k) / nestWeight I i (nbr n (k - 1)))) * xh) := by
  let j : Fin n := ⟨k - 1, by omega⟩
  let q := qsum I i (k - 1)
  let A := Rsum I i (k - 1)
  let Q := q + I.v i j * ρ
  let Z := (A + I.r i j * I.v i j * ρ) / Q
  let R0 := R I i (nbr n (k - 1))
  let R1 := R I i (nbr n k)
  let W0 := nestWeight I i (nbr n (k - 1))
  let W1 := nestWeight I i (nbr n k)
  let a := R1 / R0 * (W1 / W0)
  let c := max 1 a
  have hq : 0 < q := prep_nbr_weight_pos I hI i (k - 1) (by omega) (by omega)
  have hQ : 0 < Q := add_pos_of_pos_of_nonneg hq (mul_nonneg (hI.v_pos i j).le hρ.1)
  have hR0 : 0 < R0 := R_nbr_pos I hI hfc hr i (k - 1) (by omega) (by omega)
  have hW0 : 0 < W0 := by
    dsimp [W0]; rw [weight_nbr_eq I hfc]
    exact Real.rpow_pos_of_pos hq _
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc0 : 0 ≤ c := le_trans zero_le_one hc1
  have haeq : a * (W0 * R0) = W1 * R1 := by
    dsimp [a]
    field_simp
  have he : Q ^ I.γ i * Z ≤ max (W0 * R0) (W1 * R1) := by
    have hb := endpoint_revenue_bound hq (hI.v_pos i j).le (Rsum_nonneg I hI i (k - 1))
      (mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le) (hI.γ_pos i) hρ
    have hstep := qsum_succ I i (k - 1) (by omega)
    have hstepR := Rsum_succ I i (k - 1) (by omega)
    have hnat : k - 1 + 1 = k := by omega
    rw [hnat] at hstep hstepR
    dsimp [W0, W1, R0, R1]
    simp only [weight_nbr_eq I hfc, R_nbr_eq I hfc, hstep, hstepR]
    exact hb
  have he' : Q ^ I.γ i * Z ≤ c * (W0 * R0) := by
    apply he.trans
    apply max_le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (mul_pos hW0 hR0).le
    · rw [← haeq]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_pos hW0 hR0).le
  have hw : W0 ≤ Q ^ I.γ i := by
    dsimp [W0]; rw [weight_nbr_eq I hfc]
    exact Real.rpow_le_rpow hq.le (le_add_of_nonneg_right (mul_nonneg (hI.v_pos i j).le hρ.1))
      (hI.γ_pos i).le
  have hx := (xh_yh_nonneg I hI hfc hsyn xh yh hopt).2
  have hb := mul_le_mul_of_nonneg_left
    (hopt.1.2 i (nbr n (k - 1)) ⟨k - 1, by omega, rfl⟩) hc0
  have hcost := mul_le_mul_of_nonneg_right hw (mul_nonneg hc0 hx)
  change Q ^ I.γ i * (Z - c * xh) ≤ c * yh i
  change c * (W0 * (R0 - xh)) ≤ c * yh i at hb
  nlinarith only [he', hb, hcost]

end NestedLogitVariants.Synergistic


set_option autoImplicit false
set_option linter.unusedVariables false
namespace NestedLogitVariants.Synergistic

theorem ineq_24 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    α * yh i ≥
      (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i *
        ((Rsum I i (k - 1) + I.r i ⟨k - 1, by omega⟩ * I.v i ⟨k - 1, by omega⟩ * ρ) / (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) -
          α * xh) := by
  have hα1 := lemma_14 I hI hfc hsyn hr (by omega) α hα
  have hn := xh_yh_nonneg I hI hfc hsyn xh yh hopt
  have hw : 0 ≤ (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i :=
    Real.rpow_nonneg (add_nonneg (qsum_nonneg I hI i _) (mul_nonneg (hI.v_pos i _).le hρ.1)) _
  have hm : alphaTerm I i k ≤ α := hα.2 ⟨i, k, by simp [hk2, hkn], rfl⟩
  dsimp [alphaTerm] at hm
  by_cases hab : R I i (nbr n (k - 1)) / R I i (nbr n k) ≤
      R I i (nbr n k) / R I i (nbr n (k - 1)) *
        (nestWeight I i (nbr n k) / nestWeight I i (nbr n (k - 1)))
  · rw [min_eq_left hab] at hm
    exact scaled_bound_mono hw hn.2 (hn.1 i) hm (ineq_20 I hI hfc hsyn hr xh yh hopt i k hk2 hkn ρ hρ)
  · rw [min_eq_right (le_of_not_ge hab)] at hm
    exact scaled_bound_mono hw hn.2 (hn.1 i) (max_le hα1 hm)
      (ineq_22 I hI hfc hsyn hr xh yh hopt i k hk2 hkn ρ hρ)


end NestedLogitVariants.Synergistic

open NestedLogitVariants.Synergistic

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (hn : 2 ≤ n)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    α * yh i ≥ (I.v i ⟨0, by omega⟩ * ρ) ^ I.γ i * (I.r i ⟨0, by omega⟩ * I.v i ⟨0, by omega⟩ * ρ / (I.v i ⟨0, by omega⟩ * ρ) - α * xh) := by
  let j : Fin n := ⟨0, by omega⟩
  have hα1 := lemma_14 I hI hfc hsyn hr hn α hα
  have hα0 : 0 ≤ α := le_trans zero_le_one hα1
  have hnn := xh_yh_nonneg I hI hfc hsyn xh yh hopt
  have hy : 0 ≤ α * yh i := mul_nonneg hα0 (hnn.1 i)
  by_cases hρ0 : ρ = 0
  · simpa [hρ0, Real.zero_rpow (hI.γ_pos i).ne'] using hy
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ.1 (Ne.symm hρ0)
  have hvρ : 0 < I.v i j * ρ := mul_pos (hI.v_pos i j) hρpos
  have hs : nbr n 1 = {j} := by
    simpa [nbr, j] using prep_nbr_succ (n := n) (k := 0) (by omega)
  have hb := hopt.1.2 i (nbr n 1) ⟨1, by omega, rfl⟩
  have hR : I.r i j * I.v i j / I.v i j = I.r i j := mul_div_cancel_right₀ _ (hI.v_pos i j).ne'
  have hRv : I.r i j * I.v i j * ρ / (I.v i j * ρ) = I.r i j := by
    rw [mul_assoc, mul_div_cancel_right₀ _ hvρ.ne']
  simp only [hs, nestWeight, V, R, hfc, zero_add, Finset.sum_singleton, hR] at hb
  have hscl : I.v i j ^ I.γ i * (I.r i j - α * xh) ≤ α * yh i :=
    scaled_bound_mono (Real.rpow_nonneg (hI.v_pos i j).le _) hnn.2 (hnn.1 i) hα1
      (by simpa only [one_mul] using hb)
  have hw : (I.v i j * ρ) ^ I.γ i ≤ I.v i j ^ I.γ i := by
    apply Real.rpow_le_rpow hvρ.le _ (hI.γ_pos i).le
    nlinarith [hI.v_pos i j, hρ.2]
  change (I.v i j * ρ) ^ I.γ i * (_ - α * xh) ≤ α * yh i
  rw [hRv]
  exact shrink_weight_bound (Real.rpow_nonneg hvρ.le _) hw hy hscl
