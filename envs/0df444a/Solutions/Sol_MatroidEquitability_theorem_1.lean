-- Prove2me | solution 1 for MatroidEquitability.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:48.604258+00:00
-- url     : https://prove2.me/submissions/d4b629dc-5120-4443-82b3-ac962e6ab63b

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_maxWeight
import Definitions.Def_MatroidEquitability_IsBasePartition
import Definitions.Def_MatroidEquitability_IsBlock
import Theorems.Thm_MatroidEquitability_proof_theorem_1_block_balance
import Theorems.Thm_MatroidEquitability_proof_theorem_1_rebalance

section
set_option autoImplicit false

namespace MatroidEquitability.Dev.T1

open MatroidEquitability

theorem part_sub {α : Type*} {M : Matroid α} {k : ℕ} {B : Fin k → Set α}
    (hB : IsBasePartition M B) (i : Fin k) : B i ⊆ M.E := by
  rw [← hB.2.2]; exact Set.subset_iUnion B i

theorem setWeight_scale {α : Type*} (w : α → ℝ) (m : ℝ) (A : Set α) :
    setWeight (fun e => w e / m) A = setWeight w A / m := by
  unfold setWeight
  simp only [div_eq_mul_inv]
  rw [finsum_mem_mul]

theorem sum_parts {α : Type*} {M : Matroid α} [M.Finite] {k : ℕ} {B : Fin k → Set α}
    (hB : IsBasePartition M B) (w : α → ℝ) :
    setWeight w M.E = ∑ j, setWeight w (B j) := by
  unfold setWeight
  rw [← hB.2.2, finsum_mem_iUnion hB.2.1 (fun i => M.ground_finite.subset (part_sub hB i)),
    finsum_eq_sum_of_fintype]

/-- (1) implies (2). -/
theorem two_of_one {α : Type*} {M : Matroid α} [M.Finite] {k : ℕ} {B : Fin k → Set α}
    (hB : IsBasePartition M B) (w : α → ℝ) (m : ℝ)
    (h1 : ∀ i j, |setWeight w (B i) - setWeight w (B j)| ≤ m) (i : Fin k) :
    |setWeight w (B i) - setWeight w M.E / k| ≤ (1 - 1 / (k : ℝ)) * m := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Fin.pos i
  have hm : 0 ≤ m := (abs_nonneg _).trans (h1 i i)
  have hS := sum_parts hB w
  have key : setWeight w (B i) - setWeight w M.E / k
      = (∑ j, (setWeight w (B i) - setWeight w (B j))) / k := by
    rw [hS, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hup : ∑ j, (setWeight w (B i) - setWeight w (B j)) ≤ ((k : ℝ) - 1) * m := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, (setWeight w (B i) - setWeight w (B j))
        ≤ ∑ j ∈ Finset.univ.erase i, m :=
      Finset.sum_le_sum fun j _ => (le_abs_self _).trans (h1 i j)
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos i))]; simp
    simp only [sub_self, zero_add]
    rw [hc] at this; exact this
  have hlo : -(((k : ℝ) - 1) * m) ≤ ∑ j, (setWeight w (B i) - setWeight w (B j)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, (-m)
        ≤ ∑ j ∈ Finset.univ.erase i, (setWeight w (B i) - setWeight w (B j)) :=
      Finset.sum_le_sum fun j _ => (neg_le_of_abs_le (h1 i j))
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos i))]; simp
    simp only [sub_self, zero_add]
    rw [hc] at this; linarith
  rw [key, abs_le]
  have e : (1 - 1 / (k : ℝ)) * m = ((k : ℝ) - 1) * m / k := by field_simp
  rw [e]
  constructor
  · rw [← neg_div]; exact div_le_div_of_nonneg_right hlo hk.le
  · exact div_le_div_of_nonneg_right hup hk.le

/-- Measure on partitions: (max weight, number of bases attaining it), lexicographic. -/
noncomputable def meas {α : Type*} {k : ℕ} (w : α → ℝ) (B : Fin k → Set α) : ℝ ×ₗ ℕ :=
  toLex (⨆ t, setWeight w (B t), {t | setWeight w (B t) = ⨆ s, setWeight w (B s)}.ncard)

/-- Core: weights in `[0,1]` give a partition with all gaps `≤ 1`. -/
theorem core {α : Type*} (M : Matroid α) [M.Finite] {k : ℕ} (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e ∧ w e ≤ 1) (hpart : ∃ B₀ : Fin k → Set α, IsBasePartition M B₀) :
    ∃ B : Fin k → Set α, IsBasePartition M B ∧
      ∀ i j, setWeight w (B i) - setWeight w (B j) ≤ 1 := by
  classical
  set P : Set (Fin k → Set α) := {B | IsBasePartition M B} with hP
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin k => 𝒫 M.E) (fun _ => M.ground_finite.powerset)).subset ?_
    intro B hB i _
    exact part_sub hB i
  obtain ⟨B₀, hB₀⟩ := hpart
  obtain ⟨B, hBP, hmin⟩ := Set.exists_min_image P (meas w) hPfin ⟨B₀, hB₀⟩
  refine ⟨B, hBP, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hij0⟩ := hcon
  have hBP' : IsBasePartition M B := hBP
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun t => setWeight w (B t)) hne
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun t => setWeight w (B t)) hne
  have hi' : ∀ t, setWeight w (B t) ≤ setWeight w (B i) := fun t => hi t (Finset.mem_univ _)
  have hj' : ∀ t, setWeight w (B j) ≤ setWeight w (B t) := fun t => hj t (Finset.mem_univ _)
  have hgap : 1 < setWeight w (B i) - setWeight w (B j) :=
    lt_of_lt_of_le hij0 (sub_le_sub (hi' i0) (hj' j0))
  have hij : i ≠ j := by
    rintro rfl; simp at hgap; linarith
  have hdisj : Disjoint (B i) (B j) := hBP'.2.1 hij
  have hfin : (B i ∪ B j).Finite :=
    ((M.ground_finite.subset (part_sub hBP' i)).union (M.ground_finite.subset (part_sub hBP' j)))
  haveI : (M.restrict (B i ∪ B j)).Finite := Matroid.restrict_finite hfin
  have hsub : B i ∪ B j ⊆ M.E := Set.union_subset (part_sub hBP' i) (part_sub hBP' j)
  have hblock : IsBlock (M.restrict (B i ∪ B j)) (B i) := by
    refine ⟨?_, ?_⟩
    · rw [Matroid.isBase_restrict_iff hsub]
      exact (hBP'.1 i).isBasis_of_subset hsub Set.subset_union_left
    · rw [Matroid.restrict_ground_eq, Matroid.isBase_restrict_iff hsub]
      have : (B i ∪ B j) \ B i = B j := by
        rw [Set.union_sdiff_left, sdiff_eq_left.2 hdisj.symm]
      rw [this]
      exact (hBP'.1 j).isBasis_of_subset hsub Set.subset_union_right
  obtain ⟨B', hB'blk, hB'bal⟩ := proof_theorem_1_block_balance (M.restrict (B i ∪ B j)) w
    (fun e he => hw e (hsub he)) ⟨_, hblock⟩
  obtain ⟨-, hnew, m', hm', hlt⟩ := proof_theorem_1_rebalance M w B hBP' i j hi' hj' hgap B'
    hB'blk hB'bal
  have hmax : (⨆ t, setWeight w (B t)) = setWeight w (B i) :=
    (IsGreatest.csSup_eq ⟨⟨i, rfl⟩, by rintro _ ⟨t, rfl⟩; exact hi' t⟩)
  set B2 := Function.update (Function.update B i B') j ((B i ∪ B j) \ B') with hB2
  have hmax2 : (⨆ t, setWeight w (B2 t)) = m' := IsGreatest.csSup_eq hm'
  have hlex : meas w B2 < meas w B := by
    unfold meas
    rw [hmax, hmax2, Prod.Lex.lt_iff]
    simp only [ofLex_toLex]
    rcases hlt with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      rw [h1] at *
      simpa [h1] using h2
  exact absurd (hmin B2 hnew) (not_le.2 hlex)

/-- Main assembly. -/
theorem main {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e) (hpart : ∃ B₀ : Fin k → Set α, IsBasePartition M B₀) :
    ∃ B : Fin k → Set α, IsBasePartition M B ∧
      (∀ i j, |setWeight w (B i) - setWeight w (B j)| ≤ maxWeight M w) ∧
      ∀ i, |setWeight w (B i) - setWeight w M.E / k| ≤ (1 - 1 / (k : ℝ)) * maxWeight M w := by
  classical
  have h1 : ∃ B : Fin k → Set α, IsBasePartition M B ∧
      (∀ i j, |setWeight w (B i) - setWeight w (B j)| ≤ maxWeight M w) := by
    have hbdd : BddAbove (w '' M.E) := (M.ground_finite.image w).bddAbove
    have hle : ∀ e ∈ M.E, w e ≤ maxWeight M w := fun e he => le_csSup hbdd ⟨e, he, rfl⟩
    by_cases hm : maxWeight M w = 0
    · obtain ⟨B₀, hB₀⟩ := hpart
      refine ⟨B₀, hB₀, fun i j => ?_⟩
      have h0 : ∀ A ⊆ M.E, setWeight w A = 0 := by
        intro A hA
        unfold setWeight
        rw [finsum_mem_eq_zero_of_forall_eq_zero]
        intro e he
        exact le_antisymm (hm ▸ hle e (hA he)) (hw e (hA he))
      rw [h0 _ (part_sub hB₀ i), h0 _ (part_sub hB₀ j), hm]; simp
    · have hmpos : 0 < maxWeight M w := by
        by_cases hE : M.E.Nonempty
        · obtain ⟨e, he⟩ := hE
          exact lt_of_le_of_ne ((hw e he).trans (hle e he)) (Ne.symm hm)
        · exfalso; apply hm
          have : M.E = ∅ := Set.not_nonempty_iff_eq_empty.1 hE
          simp [maxWeight, this]
      obtain ⟨B, hB, hgap⟩ := core M (fun e => w e / maxWeight M w)
        (fun e he => ⟨div_nonneg (hw e he) hmpos.le, (div_le_one hmpos).2 (hle e he)⟩) hpart
      refine ⟨B, hB, fun i j => ?_⟩
      have g := hgap i j
      have g' := hgap j i
      rw [setWeight_scale, setWeight_scale, ← sub_div, div_le_one hmpos] at g g'
      rw [abs_le]; constructor <;> linarith
  obtain ⟨B, hB, hB1⟩ := h1
  exact ⟨B, hB, hB1, two_of_one hB w _ hB1⟩

end MatroidEquitability.Dev.T1

namespace MatroidEquitability

theorem chk_theorem_1 {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e) (hpart : ∃ B₀ : Fin k → Set α, IsBasePartition M B₀) :
    ∃ B : Fin k → Set α, IsBasePartition M B ∧
      (∀ i j, |setWeight w (B i) - setWeight w (B j)| ≤ maxWeight M w) ∧
      ∀ i, |setWeight w (B i) - setWeight w M.E / k| ≤ (1 - 1 / (k : ℝ)) * maxWeight M w :=
  Dev.T1.main M k w hw hpart

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_theorem_1 := @MatroidEquitability.chk_theorem_1
