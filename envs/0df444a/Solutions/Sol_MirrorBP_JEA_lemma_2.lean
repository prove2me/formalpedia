-- Prove2me | solution 1 for MirrorBP.JEA.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:23:19.492381+00:00
-- url     : https://prove2.me/submissions/cd839c6f-0760-4072-88b8-824caff57465

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

set_option linter.unusedSectionVars false

namespace MirrorBP.JEA.Lemma2Aux

open Finset MirrorBP.JEA

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- the per-type maximum in the dual function -/
noncomputable def Gt (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (y : V → ℝ) (τ : Ty) : ℝ :=
  if h : (P τ ×ˢ D τ).Nonempty then
      (P τ ×ˢ D τ).sup' h (fun p => max 0 (w p.1 τ p.2 + y p.1 - y p.2)) else 0

theorem gDual_eq (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (y : V → ℝ) :
    gDual P D w φ y = ∑ τ, φ τ * Gt P D w y τ := rfl

theorem Gt_nonneg (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (y : V → ℝ) (τ : Ty) :
    0 ≤ Gt P D w y τ := by
  unfold Gt
  split_ifs with h
  · obtain ⟨p, hp⟩ := h
    exact le_trans (le_max_left _ _) (Finset.le_sup' (fun p => max 0 (w p.1 τ p.2 + y p.1 - y p.2)) hp)
  · exact le_rfl

theorem le_Gt (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (y : V → ℝ) (τ : Ty)
    (j k : V) (hj : j ∈ P τ) (hk : k ∈ D τ) : w j τ k + y j - y k ≤ Gt P D w y τ := by
  unfold Gt
  have hp : (j, k) ∈ P τ ×ˢ D τ := Finset.mem_product.mpr ⟨hj, hk⟩
  rw [dif_pos ⟨_, hp⟩]
  exact le_trans (le_max_right _ _) (Finset.le_sup' (fun p => max 0 (w p.1 τ p.2 + y p.1 - y p.2)) hp)

theorem Gt_le (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (y : V → ℝ) (τ : Ty) (b : ℝ)
    (hne : (P τ).Nonempty ∧ (D τ).Nonempty)
    (h : ∀ j ∈ P τ, ∀ k ∈ D τ, max 0 (w j τ k + y j - y k) ≤ b) : Gt P D w y τ ≤ b := by
  unfold Gt
  rw [dif_pos (Finset.Nonempty.product hne.1 hne.2)]
  apply Finset.sup'_le
  intro p hp
  rw [Finset.mem_product] at hp
  exact h p.1 hp.1 p.2 hp.2

theorem pot_identity (P D : Ty → Finset V) (z : V → Ty → V → ℝ) (y : V → ℝ) :
    ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k * (y j - y k) = ∑ i, y i * netOut P D z {i} := by
  unfold netOut
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∀ i, y i * (z a τ b * ((if a ∈ ({i} : Finset V) then (1 : ℝ) else 0) -
      (if b ∈ ({i} : Finset V) then 1 else 0)))
      = z a τ b * ((if a = i then y i else 0) - (if b = i then y i else 0)) := by
    intro i
    simp only [Finset.mem_singleton]
    split_ifs <;> ring
  simp only [this, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- weak duality -/
theorem weak_duality (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ)
    (hφ : ∀ τ, 0 ≤ φ τ) (y : V → ℝ) : Wspp P D w φ ≤ gDual P D w φ y := by
  have hne : (sppObjX P D w φ '' {x | sppFeasX P D φ x}).Nonempty := by
    refine ⟨_, 0, ⟨fun i => ?_, fun τ => ?_, fun τ j _ k _ => le_rfl⟩, rfl⟩
    · simp [netOut]
    · simp
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  have hpot := pot_identity P D (fun j τ k => φ τ * x j τ k) y
  have hzero : ∑ i, y i * netOut P D (fun j τ k => φ τ * x j τ k) {i} = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hx.1 i, mul_zero]
  rw [hzero] at hpot
  have e : sppObjX P D w φ x = ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
      φ τ * x j τ k * (w j τ k + y j - y k) := by
    unfold sppObjX
    have : ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, φ τ * x j τ k * (w j τ k + y j - y k)
        = ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, w j τ k * φ τ * x j τ k
          + ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, φ τ * x j τ k * (y j - y k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [this, hpot, add_zero]
  rw [e, gDual_eq]
  refine Finset.sum_le_sum fun τ _ => ?_
  calc ∑ j ∈ P τ, ∑ k ∈ D τ, φ τ * x j τ k * (w j τ k + y j - y k)
      ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, φ τ * x j τ k * Gt P D w y τ := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_of_nonneg_left (le_Gt P D w y τ j k hj hk)
          (mul_nonneg (hφ τ) (hx.2.2 τ j hj k hk))
    _ = φ τ * Gt P D w y τ * ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ φ τ * Gt P D w y τ * 1 :=
        mul_le_mul_of_nonneg_left (hx.2.1 τ) (mul_nonneg (hφ τ) (Gt_nonneg P D w y τ))
    _ = φ τ * Gt P D w y τ := mul_one _


/-- crossing indicator sum for a cut `S` -/
noncomputable def cross (P D : Ty → Finset V) (φ : Ty → ℝ) (S : Finset V) : ℝ :=
  ∑ τ ∈ univ.filter (fun τ => (P τ ∩ S).Nonempty ∧ (D τ \ S).Nonempty), φ τ

/-- the shifted dual variable -/
def shift (S : Finset V) (c : ℝ) (y : V → ℝ) : V → ℝ := fun i => if i ∈ S then y i - c else y i

theorem one_step_Gt (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (y : V → ℝ) (S : Finset V) (c : ℝ) (hc : 0 ≤ c)
    (hgap : ∀ j ∈ S, ∀ k, k ∉ S → c + 2 ≤ y j - y k) (τ : Ty) :
    Gt P D w (shift S c y) τ +
        c * (if (P τ ∩ S).Nonempty ∧ (D τ \ S).Nonempty then 1 else 0)
      ≤ Gt P D w y τ := by
  have hwle : ∀ j ∈ P τ, ∀ k ∈ D τ, w j τ k ≤ 1 := fun j hj k hk =>
    (le_abs_self _).trans (hw τ j hj k hk)
  have hwge : ∀ j ∈ P τ, ∀ k ∈ D τ, -1 ≤ w j τ k := fun j hj k hk => by
    have := hw τ j hj k hk; rw [abs_le] at this; exact this.1
  have hG0 := Gt_nonneg P D w y τ
  split_ifs with hcr
  · obtain ⟨⟨j0, hj0⟩, ⟨k0, hk0⟩⟩ := hcr
    rw [Finset.mem_inter] at hj0
    rw [Finset.mem_sdiff] at hk0
    have hbase := le_Gt P D w y τ j0 k0 hj0.1 hk0.1
    have hg0 := hgap j0 hj0.2 k0 hk0.2
    have hw0 := hwge j0 hj0.1 k0 hk0.1
    rw [mul_one]
    suffices Gt P D w (shift S c y) τ ≤ Gt P D w y τ - c by linarith
    apply Gt_le P D w _ τ _ ⟨hP τ, hD τ⟩
    intro j hj k hk
    apply max_le
    · linarith
    simp only [shift]
    by_cases hjS : j ∈ S <;> by_cases hkS : k ∈ S
    · simp only [hjS, hkS, if_true]
      have h1 := le_Gt P D w y τ j k0 hj hk0.1
      have h2 := hgap k hkS k0 hk0.2
      have h3 := hwle j hj k hk
      have h4 := hwge j hj k0 hk0.1
      linarith
    · simp only [hjS, hkS, if_true, if_false]
      have h1 := le_Gt P D w y τ j k hj hk
      linarith
    · simp only [hjS, hkS, if_true, if_false]
      have h2 := hgap k hkS j hjS
      have h3 := hwle j hj k hk
      linarith
    · simp only [hjS, hkS, if_false]
      have h1 := le_Gt P D w y τ j0 k hj0.1 hk
      have h2 := hgap j0 hj0.2 j hjS
      have h3 := hwle j hj k hk
      have h4 := hwge j0 hj0.1 k hk
      linarith
  · rw [mul_zero, add_zero]
    apply Gt_le P D w _ τ _ ⟨hP τ, hD τ⟩
    intro j hj k hk
    apply max_le hG0
    simp only [shift]
    by_cases hjS : j ∈ S <;> by_cases hkS : k ∈ S
    · simp only [hjS, hkS, if_true]
      have h1 := le_Gt P D w y τ j k hj hk
      linarith
    · simp only [hjS, hkS, if_true, if_false]
      have h1 := le_Gt P D w y τ j k hj hk
      linarith
    · simp only [hjS, hkS, if_true, if_false]
      have h2 := hgap k hkS j hjS
      have h3 := hwle j hj k hk
      linarith
    · simp only [hjS, hkS, if_false]
      exact le_Gt P D w y τ j k hj hk

theorem one_step (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (hφ : ∀ τ, 0 ≤ φ τ)
    (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (y : V → ℝ) (S : Finset V) (hS : S ∈ cuts V) (c : ℝ) (hc : 0 ≤ c)
    (hgap : ∀ j ∈ S, ∀ k, k ∉ S → c + 2 ≤ y j - y k) :
    gDual P D w φ (shift S c y) + c * alphaConn P D φ ≤ gDual P D w φ y := by
  have hα : alphaConn P D φ ≤ cross P D φ S := by
    unfold alphaConn
    rw [dif_pos ⟨S, hS⟩]
    exact Finset.inf'_le _ hS
  have hcross : gDual P D w φ (shift S c y) + c * cross P D φ S ≤ gDual P D w φ y := by
    rw [gDual_eq, gDual_eq]
    unfold cross
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    have h := one_step_Gt P D w hP hD hw y S c hc hgap τ
    have h' := mul_le_mul_of_nonneg_left h (hφ τ)
    split_ifs at h' ⊢ with hh
    · nlinarith
    · nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hα hc]


theorem ymin_le [Nonempty V] (y : V → ℝ) (i : V) : ymin y ≤ y i := by
  unfold ymin
  rw [dif_pos Finset.univ_nonempty]
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_ymax [Nonempty V] (y : V → ℝ) (i : V) : y i ≤ ymax y := by
  unfold ymax
  rw [dif_pos Finset.univ_nonempty]
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem exists_ymin [Nonempty V] (y : V → ℝ) : ∃ i, y i = ymin y := by
  unfold ymin
  rw [dif_pos Finset.univ_nonempty]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  exact ⟨i, hi.symm⟩

theorem exists_ymax [Nonempty V] (y : V → ℝ) : ∃ i, y i = ymax y := by
  unfold ymax
  rw [dif_pos Finset.univ_nonempty]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty y
  exact ⟨i, hi.symm⟩

/-- nodes whose value has a gap larger than `2` below it -/
noncomputable def NG (y : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun j => (∃ i, y i < y j) ∧ ∀ i, y i < y j → y i < y j - 2)

theorem mem_NG (y : V → ℝ) (j : V) :
    j ∈ NG y ↔ (∃ i, y i < y j) ∧ ∀ i, y i < y j → y i < y j - 2 := by
  classical
  unfold NG
  simp

theorem spread_of_NG_empty [Nonempty V] (y : V → ℝ) (h : NG y = ∅) :
    ymax y - ymin y ≤ 2 * ((Fintype.card V : ℝ) - 1) := by
  classical
  have key : ∀ k : ℕ, ∀ j, (univ.filter (fun i => y i < y j)).card = k → y j - ymin y ≤ 2 * k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hk
      by_cases hex : ∃ i, y i < y j
      · have hj : j ∉ NG y := by rw [h]; simp
        rw [mem_NG] at hj
        push_neg at hj
        obtain ⟨i, hi1, hi2⟩ := hj hex
        have hsub : univ.filter (fun i' => y i' < y i) ⊂ univ.filter (fun i' => y i' < y j) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨i, by simp [hi1], by simp⟩
          · intro i' hi'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
            linarith
        have hlt := Finset.card_lt_card hsub
        rw [hk] at hlt
        have := ih _ hlt i rfl
        have hc : ((univ.filter (fun i' => y i' < y i)).card : ℝ) + 1 ≤ k := by
          exact_mod_cast hlt
        linarith
      · push_neg at hex
        obtain ⟨i, hi⟩ := exists_ymin y
        have := hex i
        have : (0 : ℝ) ≤ 2 * k := by positivity
        linarith
  obtain ⟨j, hj⟩ := exists_ymax y
  have := key _ j rfl
  have hcard : (univ.filter (fun i => y i < y j)).card ≤ Fintype.card V - 1 := by
    have hsub : univ.filter (fun i => y i < y j) ⊆ univ.erase j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl; exact lt_irrefl _ hi
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have hcR : ((univ.filter (fun i => y i < y j)).card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
    have : ((univ.filter (fun i => y i < y j)).card : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [Nat.cast_sub h1] at this
    simpa using this
  rw [← hj]
  linarith

theorem alpha_nonneg (P D : Ty → Finset V) (φ : Ty → ℝ) (hφ : ∀ τ, 0 ≤ φ τ) :
    0 ≤ alphaConn P D φ := by
  unfold alphaConn
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro S _
    exact Finset.sum_nonneg fun τ _ => hφ τ
  · exact le_rfl

theorem main_ind (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (hφ : ∀ τ, 0 ≤ φ τ)
    (hm : 1 < Fintype.card V)
    (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) :
    ∀ n : ℕ, ∀ y : V → ℝ, (NG y).card = n →
      Wspp P D w φ ≤ gDual P D w φ y -
        alphaConn P D φ * max 0 (ymax y - ymin y - 2 * ((Fintype.card V : ℝ) - 1)) := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hα := alpha_nonneg P D φ hφ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hn
    by_cases hNG : NG y = ∅
    · have hsp := spread_of_NG_empty y hNG
      rw [max_eq_left (by linarith), mul_zero, sub_zero]
      exact weak_duality P D w φ hφ y
    · obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hNG
      have hj0' := (mem_NG y j0).mp hj0
      set v := y j0 with hv
      let L := univ.filter (fun i => y i < v)
      have hLne : L.Nonempty := by
        obtain ⟨i, hi⟩ := hj0'.1
        exact ⟨i, by simp [L, hi]⟩
      obtain ⟨ks, hksL, hks⟩ := Finset.exists_mem_eq_sup' hLne y
      set u := L.sup' hLne y with hu
      have hksv : y ks < v := by simpa [L] using hksL
      have huv : u < v - 2 := by rw [hks]; exact hj0'.2 ks hksv
      have hle_u : ∀ i, y i < v → y i ≤ u := fun i hi =>
        Finset.le_sup' y (by simp [L, hi])
      let S := univ.filter (fun i => v ≤ y i)
      have hmemS : ∀ i, i ∈ S ↔ v ≤ y i := fun i => by simp [S]
      set c := v - u - 2 with hc
      have hc0 : 0 < c := by linarith
      have hS : S ∈ cuts V := by
        unfold cuts
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨j0, (hmemS j0).mpr le_rfl⟩, ?_⟩
        intro hSu
        have : ks ∈ S := by rw [hSu]; exact Finset.mem_univ _
        rw [hmemS] at this
        linarith
      have hgap : ∀ j ∈ S, ∀ k, k ∉ S → c + 2 ≤ y j - y k := by
        intro j hj k hk
        rw [hmemS] at hj hk
        push_neg at hk
        have := hle_u k hk
        linarith
      have hstep := one_step P D w φ hφ hP hD hw y S hS c hc0.le hgap
      set y' := shift S c y with hy'
      have hy'S : ∀ i, i ∈ S → y' i = y i - c := fun i hi => by simp [hy', shift, hi]
      have hy'N : ∀ i, i ∉ S → y' i = y i := fun i hi => by simp [hy', shift, hi]
      -- the measure decreases
      have hsub : NG y' ⊂ NG y := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j0, hj0, ?_⟩
          rw [mem_NG]
          intro hcon
          have hks' : ks ∉ S := by rw [hmemS]; linarith
          have h1 : y' ks < y' j0 := by
            rw [hy'N ks hks', hy'S j0 ((hmemS j0).mpr le_rfl)]
            linarith
          have h2 := hcon.2 ks h1
          rw [hy'N ks hks', hy'S j0 ((hmemS j0).mpr le_rfl)] at h2
          linarith
        · intro j hj
          rw [mem_NG] at hj ⊢
          by_cases hjS : j ∈ S
          · have hjv := (hmemS j).mp hjS
            refine ⟨⟨ks, by linarith⟩, ?_⟩
            intro i hi
            by_cases hiS : i ∈ S
            · have := hj.2 i (by rw [hy'S i hiS, hy'S j hjS]; linarith)
              rw [hy'S i hiS, hy'S j hjS] at this
              linarith
            · have hiv : y i < v := by rw [hmemS] at hiS; push_neg at hiS; exact hiS
              have := hle_u i hiv
              linarith
          · have hjv : y j < v := by rw [hmemS] at hjS; push_neg at hjS; exact hjS
            have hju := hle_u j hjv
            refine ⟨?_, ?_⟩
            · obtain ⟨i, hi⟩ := hj.1
              by_cases hiS : i ∈ S
              · rw [hy'S i hiS, hy'N j hjS] at hi
                have := (hmemS i).mp hiS
                linarith
              · rw [hy'N i hiS, hy'N j hjS] at hi
                exact ⟨i, hi⟩
            · intro i hi
              have hiS : i ∉ S := by rw [hmemS]; linarith
              have := hj.2 i (by rw [hy'N i hiS, hy'N j hjS]; exact hi)
              rw [hy'N i hiS, hy'N j hjS] at this
              exact this
      have hlt := Finset.card_lt_card hsub
      rw [hn] at hlt
      have hih := ih _ hlt y' rfl
      -- spread of y'
      have hmax' : ymax y - c ≤ ymax y' := by
        obtain ⟨i, hi⟩ := exists_ymax y
        have := le_ymax y' i
        by_cases hiS : i ∈ S
        · rw [hy'S i hiS] at this; linarith
        · rw [hy'N i hiS] at this; linarith
      have hmin' : ymin y' ≤ ymin y := by
        obtain ⟨i, hi⟩ := exists_ymin y
        have hiS : i ∉ S := by
          rw [hmemS]; have := ymin_le y ks; linarith
        have := ymin_le y' i
        rw [hy'N i hiS] at this; linarith
      set X := ymax y - ymin y - 2 * ((Fintype.card V : ℝ) - 1) with hX
      have hmono : max 0 (X - c) ≤ max 0 (ymax y' - ymin y' - 2 * ((Fintype.card V : ℝ) - 1)) :=
        max_le_max le_rfl (by linarith)
      have hcomb : max 0 X ≤ c + max 0 (X - c) := by
        apply max_le
        · have := le_max_left 0 (X - c); linarith
        · have := le_max_right 0 (X - c); linarith
      have h1 := mul_le_mul_of_nonneg_left hmono hα
      have h2 := mul_le_mul_of_nonneg_left hcomb hα
      nlinarith

end MirrorBP.JEA.Lemma2Aux

open MirrorBP.JEA MirrorBP.JEA.Lemma2Aux Finset

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : IsRate φ) (y : V → ℝ) :
    Wspp P D w φ - gDual P D w φ y
      ≤ -(alphaConn P D φ) * max 0 (ymax y - ymin y - 2 * (Fintype.card V : ℝ)) := by
  have h := main_ind P D w φ hφ.1 hm hP hD hw _ y rfl
  have hα := alpha_nonneg P D φ hφ.1
  have hmono : max 0 (ymax y - ymin y - 2 * (Fintype.card V : ℝ))
      ≤ max 0 (ymax y - ymin y - 2 * ((Fintype.card V : ℝ) - 1)) :=
    max_le_max le_rfl (by linarith)
  have := mul_le_mul_of_nonneg_left hmono hα
  nlinarith
