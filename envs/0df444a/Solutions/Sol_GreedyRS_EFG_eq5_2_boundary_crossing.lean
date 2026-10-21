-- Prove2me | solution 1 for GreedyRS.EFG.eq5_2_boundary_crossing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:17:52.524047+00:00
-- url     : https://prove2.me/submissions/e1c627c7-feeb-4c91-b7da-ca38cc48fff1

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open GreedyRS.Greedy

open Classical in
theorem inf_nat_GEF (P : ℕ → Prop) (a : ℕ) (h : (⨅ (n : ℕ) (_ : P n), (n : ℕ∞)) = (a : ℕ∞)) :
    P a ∧ ∀ n, P n → a ≤ n := by
  by_cases hne : ∃ n, P n
  · have : (⨅ (n : ℕ) (_ : P n), (n : ℕ∞)) = (Nat.find hne : ℕ∞) := by
      apply le_antisymm
      · exact iInf₂_le (Nat.find hne) (Nat.find_spec hne)
      · exact le_iInf₂ (fun n hn => by exact_mod_cast Nat.find_min' hne hn)
    rw [this] at h
    have h' : Nat.find hne = a := by exact_mod_cast h
    subst h'
    exact ⟨Nat.find_spec hne, fun n hn => Nat.find_min' hne hn⟩
  · push Not at hne
    simp [hne] at h

theorem leader_spec_GEF (k : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (s : ℕ → ℕ) :
    leader k x s < k ∧
      (∀ j < k, runMean x j (s j) ≤ runMean x (leader k x s) (s (leader k x s))) := by
  unfold leader; rw [dif_pos hk]
  exact Nat.find_spec (exists_leader k hk x s)

theorem leader_eq_zero_GEF (k : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (s : ℕ → ℕ)
    (h : ∀ j < k, runMean x j (s j) ≤ runMean x 0 (s 0)) : leader k x s = 0 := by
  unfold leader; rw [dif_pos hk]
  exact Nat.le_zero.1 (Nat.find_min' (exists_leader k hk x s) ⟨hk, h⟩)

theorem efg_succ_GEF (k n0 : ℕ) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    efgSizes k n0 x (t + 1) = Function.update (efgSizes k n0 x t) (leader k x (efgSizes k n0 x t))
      (efgSizes k n0 x t (leader k x (efgSizes k n0 x t)) + 1) := rfl

theorem efg_sum_GEF (k n0 : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    ∑ j ∈ Finset.range k, efgSizes k n0 x t j = n0 * k + t := by
  induction t with
  | zero => simp [efgSizes, mul_comm]
  | succ t ih =>
    rw [efg_succ_GEF]
    have hl := (leader_spec_GEF k hk x (efgSizes k n0 x t)).1
    set s := efgSizes k n0 x t
    set l := leader k x s
    have : ∑ j ∈ Finset.range k, Function.update s l (s l + 1) j =
        ∑ j ∈ Finset.range k, (s j + if j = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = l
      · subst h; simp
      · simp [Function.update_of_ne h, h]
    rw [this, Finset.sum_add_distrib, ih]
    simp [Finset.mem_range, hl]
    ring

theorem pathwise_GEF (x : ℕ → ℕ → ℝ) (k n0 B : ℕ) (hk : 0 < k) (hn0 : 1 ≤ n0)
    (A0 : ℕ) (a : ℕ → ℕ) (b : ℝ)
    (hA0 : n0 ≤ A0) (hmin : ∀ n, n0 ≤ n → runMean x 0 A0 ≤ runMean x 0 n) (hb : b = runMean x 0 A0)
    (ha1 : ∀ i, 1 ≤ i → i < k → runMean x i (a i) < b)
    (ha2 : ∀ i, 1 ≤ i → i < k → ∀ n, n0 ≤ n → runMean x i n < b → a i ≤ n)
    (hna : ∀ i, 1 ≤ i → i < k → n0 ≤ a i)
    (hB : A0 + ∑ i ∈ Finset.Ico 1 k, a i ≤ B) :
    efgSelect k n0 B x = 0 := by
  have hgood : ∀ s : ℕ → ℕ, (∀ j, n0 ≤ s j) → (∀ i, 1 ≤ i → i < k → runMean x i (s i) ≤ b) →
      leader k x s = 0 := by
    intro s hs hg
    apply leader_eq_zero_GEF k hk
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · calc runMean x j (s j) ≤ b := hg j hj0 hj
        _ = runMean x 0 A0 := hb
        _ ≤ runMean x 0 (s 0) := hmin _ (hs 0)
  have inv : ∀ t, (∀ j, n0 ≤ efgSizes k n0 x t j) ∧
      (∀ i, 1 ≤ i → i < k → efgSizes k n0 x t i ≤ a i) ∧
      (efgSizes k n0 x t 0 ≤ A0 ∨
        (∀ i, 1 ≤ i → i < k → runMean x i (efgSizes k n0 x t i) ≤ b)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun j => by simp [efgSizes], fun i hi hik => by simpa [efgSizes] using hna i hi hik, ?_⟩
      left; simpa [efgSizes] using hA0
    | succ t ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      rw [efg_succ_GEF]
      set s := efgSizes k n0 x t with hs
      obtain ⟨hl, hlmax⟩ := leader_spec_GEF k hk x s
      set l := leader k x s with hl_def
      refine ⟨?_, ?_, ?_⟩
      · intro j
        by_cases h : j = l
        · rw [h, Function.update_self]; have := ih1 l; omega
        · rw [Function.update_of_ne h]; exact ih1 j
      · intro i hi hik
        by_cases h : i = l
        · rw [h, Function.update_self]
          have h1 : runMean x 0 (s 0) ≤ runMean x l (s l) := hlmax 0 hk
          have h2 : b ≤ runMean x l (s l) := by
            calc b = runMean x 0 A0 := hb
              _ ≤ runMean x 0 (s 0) := hmin _ (ih1 0)
              _ ≤ _ := h1
          have h3 : s l ≠ a l := by
            intro he; rw [he] at h2; exact absurd (ha1 l (by omega) hl) (not_lt.2 h2)
          have := ih2 l (by omega) hl
          omega
        · rw [Function.update_of_ne h]; exact ih2 i hi hik
      · rcases ih3 with h3 | h3
        · by_cases h : l = 0
          · by_cases hlt : s 0 + 1 ≤ A0
            · left; rw [h, Function.update_self]; exact hlt
            · right
              intro i hi hik
              have hne : i ≠ l := by omega
              rw [Function.update_of_ne hne]
              have hs0 : s 0 = A0 := by
                have : s 0 ≤ A0 := h3
                omega
              have := hlmax i hik
              rw [h, hs0] at this
              calc runMean x i (s i) ≤ runMean x 0 A0 := this
                _ = b := hb.symm
          · left
            have : (0 : ℕ) ≠ l := fun e => h e.symm
            rw [Function.update_of_ne this]; exact h3
        · right
          have hl0 : l = 0 := hgood s ih1 h3
          intro i hi hik
          have hne : i ≠ l := by omega
          rw [Function.update_of_ne hne]
          exact h3 i hi hik
  -- conclusion
  unfold efgSelect
  set T := B - n0 * k with hT
  obtain ⟨i1, i2, i3⟩ := inv T
  by_contra hne
  have hlg : ¬ (∀ i, 1 ≤ i → i < k → runMean x i (efgSizes k n0 x T i) ≤ b) := by
    intro hg; exact hne (hgood _ i1 hg)
  have h0 : efgSizes k n0 x T 0 ≤ A0 := by
    rcases i3 with h | h
    · exact h
    · exact absurd h hlg
  obtain ⟨hl, hlmax⟩ := leader_spec_GEF k hk x (efgSizes k n0 x T)
  set s := efgSizes k n0 x T with hs
  set l := leader k x s with hl_def
  have hl1 : 1 ≤ l := by
    by_contra h0'
    exact hne (by omega)
  have h1 : runMean x 0 (s 0) ≤ runMean x l (s l) := hlmax 0 hk
  have h2 : b ≤ runMean x l (s l) := by
    calc b = runMean x 0 A0 := hb
      _ ≤ runMean x 0 (s 0) := hmin _ (i1 0)
      _ ≤ _ := h1
  have h3 : s l ≠ a l := by
    intro he; rw [he] at h2; exact absurd (ha1 l hl1 hl) (not_lt.2 h2)
  have h4 : s l < a l := lt_of_le_of_ne (i2 l hl1 hl) h3
  have hsum : ∑ j ∈ Finset.range k, s j = n0 * k + T := efg_sum_GEF k n0 hk x T
  have hsplit : ∑ j ∈ Finset.range k, s j = s 0 + ∑ j ∈ Finset.Ico 1 k, s j := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  have hlt : ∑ j ∈ Finset.Ico 1 k, s j < ∑ j ∈ Finset.Ico 1 k, a j := by
    apply Finset.sum_lt_sum
    · intro j hj
      rw [Finset.mem_Ico] at hj
      exact i2 j hj.1 hj.2
    · exact ⟨l, Finset.mem_Ico.2 ⟨hl1, hl⟩, h4⟩
  omega

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) (k n0 B : ℕ) (hn0 : 1 ≤ n0) :
    P {ω | (∑ i ∈ Finset.Ico 1 k,
          GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.boundary (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0) n0) +
        GreedyRS.Greedy.argminFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 ≤ (B : ℕ∞)}
      ≤ GreedyRS.Greedy.pcs P X k n0 B := by
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  show efgSelect k n0 B (fun i j => X i j ω) = 0
  set x : ℕ → ℕ → ℝ := fun i j => X i j ω with hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [efgSelect, leader]
  set b := boundary (runMean x 0) n0 with hbdef
  have hNle : ∀ i ∈ Finset.Ico 1 k, crossBelow (runMean x i) b n0 ≤ (B : ℕ∞) := by
    intro i hi
    exact le_trans (le_trans (Finset.single_le_sum
      (f := fun i => crossBelow (runMean x i) b n0) (fun _ _ => bot_le) hi) le_self_add) hω
  have hAle : argminFrom (runMean x 0) n0 ≤ (B : ℕ∞) := le_trans le_add_self hω
  set a : ℕ → ℕ := fun i => (crossBelow (runMean x i) b n0).toNat with ha
  set A0 : ℕ := (argminFrom (runMean x 0) n0).toNat with hA0
  have hN : ∀ i ∈ Finset.Ico 1 k, crossBelow (runMean x i) b n0 = ((a i : ℕ) : ℕ∞) := by
    intro i hi
    exact (ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top B) (hNle i hi))).symm
  have hA : argminFrom (runMean x 0) n0 = ((A0 : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top B) hAle)).symm
  have hB : A0 + ∑ i ∈ Finset.Ico 1 k, a i ≤ B := by
    have h1 : (((A0 + ∑ i ∈ Finset.Ico 1 k, a i : ℕ)) : ℕ∞) =
        (∑ i ∈ Finset.Ico 1 k, crossBelow (runMean x i) b n0) + argminFrom (runMean x 0) n0 := by
      rw [Nat.cast_add, Nat.cast_sum, add_comm, hA]
      congr 1
      exact (Finset.sum_congr rfl (fun i hi => (hN i hi).symm))
    have h2 : (((A0 + ∑ i ∈ Finset.Ico 1 k, a i : ℕ)) : ℕ∞) ≤ (B : ℕ∞) := by rw [h1]; exact hω
    exact_mod_cast h2
  obtain ⟨hA1, hA2⟩ := inf_nat_GEF (fun m => n0 ≤ m ∧ ∀ n, n0 ≤ n → runMean x 0 m ≤ runMean x 0 n) A0 hA
  have hmin : ∀ n, n0 ≤ n → runMean x 0 A0 ≤ runMean x 0 n := fun n hn => hA1.2 n hn
  have hb : b = runMean x 0 A0 := by
    rw [hbdef]
    unfold boundary
    apply le_antisymm
    · have hbdd : BddBelow (Set.range fun n => runMean x 0 (n0 + n)) :=
        ⟨runMean x 0 A0, by rintro _ ⟨n, rfl⟩; exact hmin _ (by omega)⟩
      have := ciInf_le hbdd (A0 - n0)
      have e : n0 + (A0 - n0) = A0 := by have := hA1.1; omega
      simp only [e] at this
      exact this
    · exact le_ciInf fun n => hmin _ (by omega)
  have hP : ∀ i ∈ Finset.Ico 1 k, (n0 ≤ a i ∧ runMean x i (a i) < b) ∧
      ∀ n, (n0 ≤ n ∧ runMean x i n < b) → a i ≤ n := by
    intro i hi
    exact inf_nat_GEF (fun n => n0 ≤ n ∧ runMean x i n < b) (a i) (hN i hi)
  apply pathwise_GEF x k n0 B hk hn0 A0 a b hA1.1 hmin hb
  · intro i hi hik; exact (hP i (Finset.mem_Ico.2 ⟨hi, hik⟩)).1.2
  · intro i hi hik n hn hlt; exact (hP i (Finset.mem_Ico.2 ⟨hi, hik⟩)).2 n ⟨hn, hlt⟩
  · intro i hi hik; exact (hP i (Finset.mem_Ico.2 ⟨hi, hik⟩)).1.1
  · exact hB
