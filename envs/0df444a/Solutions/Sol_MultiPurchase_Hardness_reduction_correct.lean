-- Prove2me | solution 1 for MultiPurchase.Hardness.reduction_correct
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:30:25.181995+00:00
-- url     : https://prove2.me/submissions/4b853f27-3ad2-4a35-aceb-57e1ee4f74b1

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
theorem AuxR40_compare_step (I : Instance) (hI : I.WellFormed) (kappa : ℚ) :
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


namespace Aux_MultiPurchase_Hardness_eq_7_maxcut
open MultiPurchase.Hardness ProjSchedTW.Complexity

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

theorem xC_01 {n : ℕ} (C : Finset (Fin n)) (i : Fin n) : xC C i = 0 ∨ xC C i = 1 := by
  unfold xC; split_ifs <;> simp

noncomputable def val {m : ℕ} (G : SimpleGraph (Fin m)) (C : Finset (Fin (m + 1))) : ℚ :=
  ∑ i, ∑ j, hubQ G i j * xC C i * xC C j

open Classical in
noncomputable def adjQ {m : ℕ} (G : SimpleGraph (Fin m)) (i j : Fin m) : ℚ :=
  if G.Adj i j then 1 else 0

theorem val_eq {m : ℕ} (G : SimpleGraph (Fin m)) (C : Finset (Fin (m + 1))) :
    val G C = xC C 0 * ∑ j, (nodeDeg G j : ℚ) * xC C j.succ -
      ∑ i, ∑ j, adjQ G i j * xC C i.succ * xC C j.succ := by
  classical
  unfold val
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, hubQ, Fin.cases_zero, Fin.cases_succ]
  have e1 : ∀ i : Fin m, (∑ j : Fin m, (if G.Adj i j then (-1 : ℚ) else 0) * xC C i.succ *
      xC C j.succ) = -∑ j, adjQ G i j * xC C i.succ * xC C j.succ := by
    intro i
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold adjQ
    split_ifs <;> ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [Finset.mul_sum]
  have e2 : ∑ x : Fin m, (nodeDeg G x : ℚ) / 2 * xC C 0 * xC C x.succ +
      ∑ x : Fin m, (nodeDeg G x : ℚ) / 2 * xC C x.succ * xC C 0 =
      ∑ i : Fin m, xC C 0 * ((nodeDeg G i : ℚ) * xC C i.succ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith [e2]

theorem nodes_mem {m : ℕ} (C : Finset (Fin (m + 1))) (j : Fin m) :
    j ∈ nodesOf C ↔ j.succ ∈ C := by
  simp [nodesOf]

theorem xC_nodes {m : ℕ} (C : Finset (Fin (m + 1))) (j : Fin m) :
    xC (nodesOf C) j = xC C j.succ := by
  unfold xC
  simp only [nodes_mem]

theorem deg_eq {m : ℕ} (G : SimpleGraph (Fin m)) (j : Fin m) :
    (nodeDeg G j : ℚ) = ∑ k, adjQ G j k := by
  classical
  unfold nodeDeg adjQ
  rw [Finset.card_filter]
  push_cast
  rfl

theorem cut_eq {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    (cutSize G A : ℚ) = ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
  classical
  -- symmetric kernel
  set T : Fin m → Fin m → ℚ := fun a b =>
    adjQ G a b * (xC A a * (1 - xC A b) + xC A b * (1 - xC A a)) with hTdef
  have hadj : ∀ a b, adjQ G a b = adjQ G b a := by
    intro a b; unfold adjQ; simp only [G.adj_comm]
  have hT : ∀ a b, T a b = T b a := by
    intro a b; simp only [hTdef, hadj a b]; ring
  have hdiag : ∀ a, T a a = 0 := by
    intro a; simp [hTdef, adjQ]
  have hsplit := symm_split T hT
  simp only [hdiag, Finset.sum_const_zero, zero_add] at hsplit
  have hfull : ∑ a, ∑ b, T a b = 2 * ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
    have : ∑ a, ∑ b, T a b = ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) +
        ∑ a, ∑ b, adjQ G a b * xC A b * (1 - xC A a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hTdef]; ring
    rw [this]
    have h2 : ∑ a, ∑ b, adjQ G a b * xC A b * (1 - xC A a) =
        ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hadj]
    rw [h2]; ring
  have hcut : (cutSize G A : ℚ) = ∑ a, ∑ b, if a < b then T a b else 0 := by
    unfold cutSize
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hTdef, adjQ, xC]
    by_cases hab : a < b
    · by_cases hadjab : G.Adj a b
      · by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [hab, hadjab, ha, hb]
      · simp [hab, hadjab]
    · simp [hab]
  rw [hcut]
  linarith

end Aux_MultiPurchase_Hardness_eq_7_maxcut

open MultiPurchase.Hardness ProjSchedTW.Complexity Aux_MultiPurchase_Hardness_eq_7_maxcut in
theorem AuxR40_eq_7_maxcut {m : ℕ} (G : SimpleGraph (Fin m)) :
    (∀ C : Finset (Fin (m + 1)),
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j ≤
        ∑ i, ∑ j, hubQ G i j * xC (insert 0 C) i * xC (insert 0 C) j) ∧
    (∀ C : Finset (Fin (m + 1)), 0 ∈ C →
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j = (cutSize G (nodesOf C) : ℚ)) ∧
    (∀ M : ℕ, (∃ C : Finset (Fin (m + 1)), (M : ℚ) ≤ ∑ i, ∑ j, hubQ G i j * xC C i * xC C j) ↔
      MaxCutYes G M) := by
  have hins : ∀ (C : Finset (Fin (m + 1))) (j : Fin m), xC (insert 0 C) j.succ = xC C j.succ := by
    intro C j
    unfold xC
    simp [Fin.succ_ne_zero]
  have hins0 : ∀ C : Finset (Fin (m + 1)), xC (insert 0 C) 0 = 1 := by
    intro C; simp [xC]
  have P1 : ∀ C : Finset (Fin (m + 1)), val G C ≤ val G (insert 0 C) := by
    intro C
    rw [val_eq, val_eq, hins0]
    simp only [hins]
    have hnn : 0 ≤ ∑ j, (nodeDeg G j : ℚ) * xC C j.succ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
        (by rcases xC_01 C j.succ with h | h <;> rw [h] <;> norm_num)
    have hx : xC C 0 ≤ 1 := by rcases xC_01 C 0 with h | h <;> rw [h] <;> norm_num
    nlinarith
  have P2 : ∀ C : Finset (Fin (m + 1)), 0 ∈ C → val G C = (cutSize G (nodesOf C) : ℚ) := by
    intro C h0
    rw [val_eq, cut_eq]
    have hx0 : xC C 0 = 1 := by simp [xC, h0]
    rw [hx0, one_mul]
    simp only [xC_nodes, deg_eq, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨P1, P2, ?_⟩
  intro M
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨nodesOf (insert 0 C), ?_⟩
    have := P2 (insert 0 C) (Finset.mem_insert_self _ _)
    have h2 : (M : ℚ) ≤ (cutSize G (nodesOf (insert 0 C)) : ℚ) := by
      rw [← this]; exact hC.trans (P1 C)
    exact_mod_cast h2
  · rintro ⟨A, hA⟩
    refine ⟨insert 0 (A.map (Fin.succEmb m)), ?_⟩
    have hN : nodesOf (insert 0 (A.map (Fin.succEmb m))) = A := by
      ext j
      rw [nodes_mem]
      simp [Fin.succ_ne_zero]
    show (M : ℚ) ≤ val G _
    rw [P2 _ (Finset.mem_insert_self _ _), hN]
    exact_mod_cast hA


open MultiPurchase.Hardness in
theorem AuxR40_theta_transformation {m : ℕ} (G : SimpleGraph (Fin m)) (kappa : ℚ) (r : Fin (m + 1) → ℚ)
    (h0 : kappa < r 0) (hhalf : ∀ i : Fin m, r i.succ < kappa / 2)
    (hpos : ∀ i : Fin m, 0 < r i.succ) (hanti : StrictAnti fun i : Fin m => r i.succ) :
    (∀ i j, 0 ≤ redTheta G kappa r i j) ∧ (∀ i, redTheta G kappa r i i = 0) ∧
    (∀ i j, i ≠ j → redTheta G kappa r i j * (r i + r j - kappa) = hubQ G i j) := by
  have hdeg : ∀ i : Fin m, (0 : ℚ) ≤ (nodeDeg G i : ℚ) / 2 := fun i => by positivity
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · simp
    · have := hpos j'
      exact div_nonneg (hdeg j') (by linarith)
    · have := hpos i'
      exact div_nonneg (hdeg i') (by linarith)
    · have h1 := hhalf i'
      have h2 := hhalf j'
      split_ifs
      · exact div_nonneg_of_nonpos (by norm_num) (by linarith)
      · simp
  · refine Fin.cases ?_ (fun i' => ?_) i <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · simp
    · simp [G.irrefl]
  · revert hij
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · exact absurd rfl hij
    · have := hpos j'
      exact div_mul_cancel₀ _ (by linarith)
    · have := hpos i'
      exact div_mul_cancel₀ _ (by linarith)
    · have h1 := hhalf i'
      have h2 := hhalf j'
      exact div_mul_cancel₀ _ (by linarith)


open MultiPurchase.Hardness ProjSchedTW.Complexity in
theorem solution {m : ℕ} (G : SimpleGraph (Fin m)) (M : ℕ) (hM : 1 ≤ M) :
    MaxCutYes G M ↔ Yes (reductionInstance G M) 1 := by
  have hr0 : redRev m 0 = 2 := rfl
  have hrs : ∀ i : Fin m, redRev m i.succ = 1 / 4 - ((i : ℚ) + 1) / (8 * ((m : ℚ) + 1)) := fun i => rfl
  have hmpos : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have hrs_lo : ∀ i : Fin m, 1 / 8 < redRev m i.succ := by
    intro i
    rw [hrs]
    have hi : ((i : ℕ) : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast i.isLt
    have : ((i : ℚ) + 1) / (8 * ((m : ℚ) + 1)) < 1 / 8 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hrs_hi : ∀ i : Fin m, redRev m i.succ < 1 / 4 := by
    intro i
    rw [hrs]
    have : 0 < ((i : ℚ) + 1) / (8 * ((m : ℚ) + 1)) := by positivity
    linarith
  have hanti : StrictAnti fun i : Fin m => redRev m i.succ := by
    intro i j hij
    simp only [hrs]
    have : (i : ℚ) < (j : ℚ) := by exact_mod_cast hij
    have h8 : (0 : ℚ) < 8 * ((m : ℚ) + 1) := by positivity
    have := div_lt_div_of_pos_right (show (i : ℚ) + 1 < (j : ℚ) + 1 by linarith) h8
    linarith
  obtain ⟨hθnn, hθdiag, hθmul⟩ := AuxR40_theta_transformation G 1 (redRev m) (by rw [hr0]; norm_num)
    (fun i => by have := hrs_hi i; linarith) (fun i => by have := hrs_lo i; linarith) hanti
  have hWF : (reductionInstance G M).WellFormed := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      show 0 < redRev m i
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [hr0]; norm_num
      · have := hrs_lo i'; linarith
    · intro i; show (0 : ℚ) ≤ 0; exact le_rfl
    · intro i j _
      show 0 ≤ 2 * redTheta G 1 (redRev m) i j
      have := hθnn i j
      linarith
    · show (0 : ℚ) < (M : ℚ)
      exact_mod_cast hM
  have hsymm : ∀ i j : Fin (m + 1), hubQ G i j = hubQ G j i := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp only [hubQ, Fin.cases_zero, Fin.cases_succ]
    by_cases h : G.Adj i' j'
    · rw [if_pos h, if_pos (G.adj_symm h)]
    · rw [if_neg h, if_neg (fun h' => h (G.adj_symm h'))]
  have hterm : ∀ i j : Fin (m + 1), (reductionInstance G M).theta i j *
      ((reductionInstance G M).rhat i j - 1) = hubQ G i j := by
    intro i j
    have hQ : ∀ i : Fin (m + 1), hubQ G i i = 0 := by
      intro i
      refine Fin.cases ?_ (fun i' => ?_) i <;> simp [hubQ]
    show (if i = j then (0 : ℚ) else 2 * redTheta G 1 (redRev m) (min i j) (max i j) / 2) *
      ((if i = j then redRev m i else redRev m i + redRev m j) - 1) = hubQ G i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, zero_mul, hQ]
    · rw [if_neg h, if_neg h]
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le]
        have := hθmul i j h
        linarith
      · rw [min_eq_right hgt.le, max_eq_left hgt.le]
        have := hθmul j i (Ne.symm h)
        rw [hsymm i j]
        linarith
  have hsum : ∀ C : Finset (Fin (m + 1)),
      ∑ i, ∑ j, (reductionInstance G M).theta i j * xC C i * xC C j *
        ((reductionInstance G M).rhat i j - 1) =
        ∑ i, ∑ j, hubQ G i j * xC C i * xC C j := by
    intro C
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hterm i j]
    ring
  have hv0 : (reductionInstance G M).v0 = (M : ℚ) := rfl
  rw [(AuxR40_eq_7_maxcut G).2.2 M |>.symm]
  unfold Yes
  rw [and_iff_right hWF, AuxR40_compare_step _ hWF 1, hv0, one_mul]
  exact ⟨fun ⟨C, hC⟩ => ⟨C, hC.trans_eq (hsum C).symm⟩, fun ⟨C, hC⟩ => ⟨C, hC.trans_eq (hsum C)⟩⟩
