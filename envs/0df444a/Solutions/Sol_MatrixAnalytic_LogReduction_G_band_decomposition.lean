-- Prove2me | solution 1 for MatrixAnalytic.LogReduction.G_band_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:02:13.197681+00:00
-- url     : https://prove2.me/submissions/90e5135f-d407-4475-ba38-a31116510a2b

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal
open MatrixAnalytic.LogReduction

lemma g72ma_ivt {V : Type*} (lv : V → ℕ) {t : ℕ} (ω : Fin (t + 2) → V)
    (hstep : ∀ m : Fin (t + 1), lv (ω m.succ) ≤ lv (ω m.castSucc) + 1) (n : ℕ)
    (h0 : lv (ω 0) ≤ n) : ∀ s : Fin (t + 2), n ≤ lv (ω s) → ∃ s' ≤ s, lv (ω s') = n := by
  intro s
  induction s using Fin.induction with
  | zero => intro h; exact ⟨0, le_rfl, le_antisymm h0 h⟩
  | succ m ih =>
    intro h
    by_cases hm : n ≤ lv (ω m.castSucc)
    · obtain ⟨s', hs', hl⟩ := ih hm
      exact ⟨s', hs'.trans (Fin.castSucc_lt_succ (i := m)).le, hl⟩
    · have := hstep m
      exact ⟨m.succ, le_rfl, by omega⟩

/-- the pointwise band identity -/
lemma g72ma_band_pt {V : Type*} (lv : V → ℕ) {t : ℕ} (ω : Fin (t + 2) → V)
    (hstep : ∀ m : Fin (t + 1), lv (ω m.succ) ≤ lv (ω m.castSucc) + 1)
    (h0 : lv (ω 0) = 1) (c : ℝ≥0∞) :
    ∑' k : ℕ, (if (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
        ¬ (lv (ω m) = 0 ∨ lv (ω m) = 2 ^ (k + 1))) ∧
        ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ lv (ω s) = 2 ^ k then c else 0) =
      if (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ¬ lv (ω m) = 0) then c else 0 := by
  classical
  set Q : ℕ → Prop := fun n => ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ n ≤ lv (ω s) with hQ
  have hl0 : (0 : Fin (t + 2)) ≠ Fin.last (t + 1) := by simp [Fin.ext_iff]
  -- characterize the two conditions
  have hA : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      ¬ (lv (ω m) = 0 ∨ lv (ω m) = 2 ^ (k + 1))) ↔
      ((∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ¬ lv (ω m) = 0) ∧ ¬ Q (2 ^ (k + 1))) := by
    intro k
    constructor
    · intro h
      refine ⟨fun m h1 h2 => fun h' => h m h1 h2 (Or.inl h'), ?_⟩
      rintro ⟨s, hs, hle⟩
      obtain ⟨s', hs', hl⟩ := g72ma_ivt lv ω hstep (2 ^ (k + 1))
        (by rw [h0]; exact Nat.one_le_two_pow) s hle
      have hs'0 : s' ≠ 0 := by
        rintro rfl; rw [h0] at hl
        have : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hs'l : s' ≠ Fin.last (t + 1) := by
        intro h'; rw [h'] at hs'; exact hs (le_antisymm (Fin.le_last s) hs')
      exact h s' hs'0 hs'l (Or.inr hl)
    · rintro ⟨h1, h2⟩ m hm0 hml
      rintro (h' | h')
      · exact h1 m hm0 hml h'
      · exact h2 ⟨m, hml, h'.ge⟩
  have hB : ∀ k, (∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ lv (ω s) = 2 ^ k) ↔ Q (2 ^ k) := by
    intro k
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h.ge⟩
    · rintro ⟨s, hs, hle⟩
      obtain ⟨s', hs', hl⟩ := g72ma_ivt lv ω hstep (2 ^ k)
        (by rw [h0]; exact Nat.one_le_two_pow) s hle
      refine ⟨s', ?_, hl⟩
      intro h'; rw [h'] at hs'; exact hs (le_antisymm (Fin.le_last s) hs')
  have hAB : ∀ k, ((∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
        ¬ (lv (ω m) = 0 ∨ lv (ω m) = 2 ^ (k + 1))) ∧
        ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ lv (ω s) = 2 ^ k) ↔
      ((∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ¬ lv (ω m) = 0) ∧ ¬ Q (2 ^ (k + 1))) ∧
        Q (2 ^ k) := fun k => by rw [hA, hB]
  simp_rw [hAB]
  by_cases hC : ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ¬ lv (ω m) = 0
  · rw [if_pos hC]
    have hT := iff_true_intro hC
    simp only [hT, true_and]
    have hex : ∃ k, ¬ Q (2 ^ (k + 1)) := by
      refine ⟨∑ s, lv (ω s), ?_⟩
      rintro ⟨s, -, hle⟩
      have h1 : lv (ω s) ≤ ∑ s, lv (ω s) :=
        Finset.single_le_sum (f := fun s => lv (ω s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
      have h2 : ∑ s, lv (ω s) < 2 ^ (∑ s, lv (ω s)) := Nat.lt_two_pow_self
      have h3 : 2 ^ (∑ s, lv (ω s)) ≤ 2 ^ (∑ s, lv (ω s) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hmono : ∀ a b, a ≤ b → Q b → Q a := by
      rintro a b hab ⟨s, hs, h⟩; exact ⟨s, hs, hab.trans h⟩
    set k0 := Nat.find hex with hk0
    have hk0n : ¬ Q (2 ^ (k0 + 1)) := Nat.find_spec hex
    have hk0q : Q (2 ^ k0) := by
      rcases Nat.eq_zero_or_pos k0 with h | h
      · rw [h]; exact ⟨0, hl0, by rw [h0]; simp⟩
      · obtain ⟨k', hk'⟩ : ∃ k', k0 = k' + 1 := ⟨k0 - 1, by omega⟩
        have := Nat.find_min hex (show k' < k0 by omega)
        rw [hk']; exact not_not.mp this
    rw [tsum_eq_single k0]
    · rw [if_pos ⟨hk0n, hk0q⟩]
    · intro k hk
      rw [if_neg]
      rintro ⟨hn, hq⟩
      rcases lt_or_gt_of_ne hk with h | h
      · exact hn (hmono _ _ (Nat.pow_le_pow_right (by norm_num) (by omega)) hk0q)
      · exact hk0n (hmono _ _ (Nat.pow_le_pow_right (by norm_num) (by omega)) hq)
  · rw [if_neg hC]
    simp [hC]

lemma g72ma_qstep {ι : Type*} (B A₀ A₁ A₂ : ι → ι → ℝ) (x y : ℕ × ι)
    (h : 0 < qbdP B A₀ A₁ A₂ x y) : y.1 ≤ x.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd h (lt_irrefl 0)

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ i j : ι, matG (qbdP B A₀ A₁ A₂) i j =
      ∑' k : ℕ, hitDownInBand (qbdP B A₀ A₁ A₂) k i j := by
  classical
  intro i j
  unfold matG hitDownInBand firstEntrance firstEntranceAfter
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun t => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  by_cases hb : ω 0 = (1, i) ∧ ω (Fin.last (t + 1)) = (0, j)
  swap
  · rw [if_neg (fun h => hb ⟨h.1, h.2.1⟩)]
    symm; apply ENNReal.tsum_eq_zero.mpr; intro k
    rw [if_neg (fun h => hb ⟨h.1, h.2.1⟩)]
  by_cases hW : pathWeightE (qbdP B A₀ A₁ A₂) ω = 0
  · simp [hW]
  have hstep : ∀ m : Fin (t + 1), (ω m.succ).1 ≤ (ω m.castSucc).1 + 1 := by
    intro m
    have h1 := (Finset.prod_ne_zero_iff.mp hW) m (Finset.mem_univ m)
    rw [Ne, ENNReal.ofReal_eq_zero, not_le] at h1
    exact g72ma_qstep B A₀ A₁ A₂ _ _ h1
  have h0 : (ω 0).1 = 1 := by rw [hb.1]
  have key := g72ma_band_pt Prod.fst ω hstep h0 (pathWeightE (qbdP B A₀ A₁ A₂) ω)
  have e1 : ∀ k, (ω 0 = (1, i) ∧ ω (Fin.last (t + 1)) = (0, j) ∧
      (0, j) ∈ (level 0 ∪ level (2 ^ (k + 1)) : Set (ℕ × ι)) ∧
      (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ (level 0 ∪ level (2 ^ (k + 1)))) ∧
      ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ ω s ∈ (level (2 ^ k) : Set (ℕ × ι))) ↔
      ((∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
        ¬ ((ω m).1 = 0 ∨ (ω m).1 = 2 ^ (k + 1))) ∧
        ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ (ω s).1 = 2 ^ k) := by
    intro k
    simp only [level, Set.mem_union, Set.mem_setOf_eq, true_or, hb, true_and]
  have e2 : (ω 0 = (1, i) ∧ ω (Fin.last (t + 1)) = (0, j) ∧
      (0, j) ∈ (level 0 : Set (ℕ × ι)) ∧
      (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ (level 0 : Set (ℕ × ι)))) ↔
      (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ¬ (ω m).1 = 0) := by
    simp only [level, Set.mem_setOf_eq, hb, true_and]
  simp_rw [e1, e2]
  exact key.symm
