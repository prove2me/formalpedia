-- Prove2me | solution 1 for MultiPurchase.Hardness.compare_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:23:42.948407+00:00
-- url     : https://prove2.me/submissions/8b177634-5af1-454b-bbe9-5bf9421c1955

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace Aux_MultiPurchase_Hardness_compare_step
open MultiPurchase.Hardness

theorem sum_C {n : ℕ} (C : Finset (Fin n)) (F : Fin n → ℚ) :
    ∑ i ∈ C, F i = ∑ i, xC C i * F i := by
  simp only [xC, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_C2 {n : ℕ} (C : Finset (Fin n)) (g : Fin n → Fin n → ℚ) :
    ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), g i j =
      ∑ i, ∑ j, if i < j then xC C i * xC C j * g i j else 0 := by
  rw [sum_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, sum_C, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem xx {n : ℕ} (C : Finset (Fin n)) (i : Fin n) : xC C i * xC C i = xC C i := by
  unfold xC; split_ifs <;> norm_num

theorem symm_split {n : ℕ} (T : Fin n → Fin n → ℚ) (hT : ∀ i j, T i j = T j i) :
    ∑ i, ∑ j, T i j = ∑ i, T i i + 2 * ∑ i, ∑ j, if i < j then T i j else 0 := by
  have h1 : ∀ i j, T i j = (if j = i then T i j else 0) + (if i < j then T i j else 0) +
      (if j < i then T i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  have h2 : ∀ i, ∑ j, T i j = T i i + (∑ j, if i < j then T i j else 0) +
      ∑ j, if j < i then T i j else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => h1 i j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  have h3 : ∑ i, ∑ j, (if j < i then T i j else 0) = ∑ i, ∑ j, (if i < j then T i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hT]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_add_distrib, h3]
  ring

end Aux_MultiPurchase_Hardness_compare_step

open MultiPurchase.Hardness Aux_MultiPurchase_Hardness_compare_step in
theorem solution (I : Instance) (hI : I.WellFormed) (kappa : ℚ) :
    (∃ C : Finset (Fin I.n), kappa ≤ I.R2 C) ↔
      ∃ C : Finset (Fin I.n),
        kappa * I.v0 ≤ ∑ i, ∑ j, I.theta i j * xC C i * xC C j * (I.rhat i j - kappa) := by
  have key : ∀ C : Finset (Fin I.n), kappa ≤ I.R2 C ↔
      kappa * I.v0 ≤ ∑ i, ∑ j, I.theta i j * xC C i * xC C j * (I.rhat i j - kappa) := by
    intro C
    obtain ⟨hr, hV1, hV2, hv0⟩ := hI
    have hS3 : 0 ≤ ∑ i ∈ C, I.V1 i := Finset.sum_nonneg fun i _ => hV1 i
    have hS4 : 0 ≤ ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj =>
        hV2 i j (Finset.mem_filter.mp hj).2
    have hD : 0 < I.v0 + ∑ i ∈ C, I.V1 i + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j := by
      linarith
    have hT : ∀ i j, I.theta i j * xC C i * xC C j * (I.rhat i j - kappa) =
        I.theta j i * xC C j * xC C i * (I.rhat j i - kappa) := by
      intro i j
      unfold Instance.theta Instance.rhat
      by_cases h : i = j
      · subst h; ring
      · rw [if_neg h, if_neg h, if_neg (Ne.symm h), if_neg (Ne.symm h), min_comm, max_comm]
        ring
    have hRHS : ∑ i, ∑ j, I.theta i j * xC C i * xC C j * (I.rhat i j - kappa) =
        (∑ i ∈ C, I.r i * I.V1 i + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j),
          (I.r i + I.r j) * I.V2 i j) -
        kappa * (∑ i ∈ C, I.V1 i + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j) := by
      have hdiag : ∀ i, I.theta i i * xC C i * xC C i * (I.rhat i i - kappa) =
          xC C i * (I.r i * I.V1 i) - kappa * (xC C i * I.V1 i) := by
        intro i
        unfold Instance.theta Instance.rhat
        rw [if_pos rfl, if_pos rfl, mul_assoc (I.V1 i), xx]
        ring
      have hoff : ∀ i, 2 * ∑ j, (if i < j then I.theta i j * xC C i * xC C j *
            (I.rhat i j - kappa) else 0) =
          (∑ j, if i < j then xC C i * xC C j * ((I.r i + I.r j) * I.V2 i j) else 0) -
            kappa * ∑ j, if i < j then xC C i * xC C j * I.V2 i j else 0 := by
        intro i
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : i < j
        · rw [if_pos h, if_pos h, if_pos h]
          unfold Instance.theta Instance.rhat
          rw [if_neg (ne_of_lt h), if_neg (ne_of_lt h), min_eq_left h.le, max_eq_right h.le]
          ring
        · rw [if_neg h, if_neg h, if_neg h]
          ring
      have A1 : ∑ i, I.theta i i * xC C i * xC C i * (I.rhat i i - kappa) =
          ∑ i, xC C i * (I.r i * I.V1 i) - kappa * ∑ i, xC C i * I.V1 i := by
        rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_sub_distrib, Finset.mul_sum]
      have A2 : 2 * ∑ i, ∑ j, (if i < j then I.theta i j * xC C i * xC C j *
            (I.rhat i j - kappa) else 0) =
          (∑ i, ∑ j, if i < j then xC C i * xC C j * ((I.r i + I.r j) * I.V2 i j) else 0) -
            kappa * ∑ i, ∑ j, if i < j then xC C i * xC C j * I.V2 i j else 0 := by
        rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => hoff i, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      rw [symm_split _ hT, sum_C2, sum_C2, sum_C C (fun i => I.r i * I.V1 i), sum_C C I.V1, A1, A2]
      ring
    unfold Instance.R2
    rw [le_div_iff₀ hD, hRHS]
    constructor <;> intro h <;> linarith
  exact ⟨fun ⟨C, hC⟩ => ⟨C, (key C).mp hC⟩, fun ⟨C, hC⟩ => ⟨C, (key C).mpr hC⟩⟩
