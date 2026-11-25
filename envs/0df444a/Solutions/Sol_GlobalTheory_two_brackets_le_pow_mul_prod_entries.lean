-- Prove2me | solution 1 for GlobalTheory.two_brackets_le_pow_mul_prod_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:11.472271+00:00
-- url     : https://prove2.me/submissions/cc6eee86-81d8-4ed2-8f3f-addc6950f052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InterlacedShiftedDistanceBracketBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace GlobalTheory
open Finset in
private lemma lam_add_two_mul_le_of_consecutive (k : ℕ) (c : ℝ) (lam : ℕ → ℝ)
    (h : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) :
    ∀ j s : ℕ, 1 ≤ s → s + j ≤ k - 1 → lam (s + j) + 2 * c * j ≤ lam s := by
  intro j
  induction j with
  | zero => intro s _ _; simp
  | succ j ih =>
    intro s hs hsj
    have h1 := ih (s + 1) (by omega) (by omega)
    have h2 := h s hs (by omega)
    rw [show s + (j + 1) = s + 1 + j by ring]
    push_cast
    linarith
open Finset in
private lemma two_mul_sub_one_mul_le_two_mul_add_one_mul (m c D a p : ℝ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hD : 7 / 2 + 2 * c * m ≤ D) (ha : a ≤ (D + c) ^ 2) (hp : D ^ 2 ≤ p) :
    (2 * m - 1) * a ≤ (2 * m + 1) * p := by
  have hD0 : 0 ≤ D := by nlinarith
  have h1 : 2 * m * (D + c) ≤ (2 * m + 1) * D := by nlinarith
  have h2 : (2 * m * (D + c)) ^ 2 ≤ ((2 * m + 1) * D) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) h1 2
  have h2m : 0 ≤ 2 * m - 1 := by linarith
  have h3 : 4 * m ^ 2 * ((2 * m - 1) * (D + c) ^ 2) ≤ 4 * m ^ 2 * ((2 * m + 1) * D ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h2m,
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * m + 1) (sq_nonneg D)]
  have h4 : (2 * m - 1) * (D + c) ^ 2 ≤ (2 * m + 1) * D ^ 2 :=
    le_of_mul_le_mul_left h3 (by positivity)
  calc (2 * m - 1) * a ≤ (2 * m - 1) * (D + c) ^ 2 := mul_le_mul_of_nonneg_left ha h2m
    _ ≤ (2 * m + 1) * D ^ 2 := h4
    _ ≤ (2 * m + 1) * p := mul_le_mul_of_nonneg_left hp (by linarith)
open Finset in
private lemma prod_le_mul_odd_mul_prod_of_bracket_chain (c : ℝ) (hc : 1 ≤ c) (a d p : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, 0 ≤ a j ∧ a j ≤ (d j + 1 + c) ^ 2 ∧ 5 / 2 + 2 * c * (j : ℝ) ≤ d j ∧
      (d j + 1) ^ 2 ≤ p j) :
    ∏ j ∈ range n, a j ≤ (1 + 2 * c / 7) ^ 2 * (2 * (n : ℝ) + 1) * ∏ j ∈ range n, p j := by
  have hK : 1 ≤ (1 + 2 * c / 7) ^ 2 := by nlinarith
  have hK0 : 0 ≤ (1 + 2 * c / 7) ^ 2 := by positivity
  have hp0 : ∀ m ≤ n, 0 ≤ ∏ j ∈ range m, p j := fun m hm =>
    prod_nonneg fun j hj => le_trans (sq_nonneg _) (h j (by simp at hj; omega)).2.2.2
  have key : ∀ m, m + 1 ≤ n → ∏ j ∈ range (m + 1), a j ≤
      (1 + 2 * c / 7) ^ 2 * (2 * (m : ℝ) + 1) * ∏ j ∈ range (m + 1), p j := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨_, ha, hd, hp⟩ := h 0 (by omega)
      simp only [prod_range_one, Nat.cast_zero, mul_zero, zero_add, mul_one]
      simp only [Nat.cast_zero, mul_zero, add_zero] at hd
      have h1 : d 0 + 1 + c ≤ (1 + 2 * c / 7) * (d 0 + 1) := by nlinarith
      have h2 : (d 0 + 1 + c) ^ 2 ≤ ((1 + 2 * c / 7) * (d 0 + 1)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h1 2
      calc a 0 ≤ (d 0 + 1 + c) ^ 2 := ha
        _ ≤ ((1 + 2 * c / 7) * (d 0 + 1)) ^ 2 := h2
        _ = (1 + 2 * c / 7) ^ 2 * (d 0 + 1) ^ 2 := by ring
        _ ≤ (1 + 2 * c / 7) ^ 2 * p 0 := mul_le_mul_of_nonneg_left hp hK0
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      obtain ⟨ha0, ha, hd, hp⟩ := h (m + 1) (by omega)
      push_cast at hd
      have hstep := two_mul_sub_one_mul_le_two_mul_add_one_mul ((m : ℝ) + 1) c (d (m + 1) + 1) (a (m + 1)) (p (m + 1))
        (by have := m.cast_nonneg (α := ℝ); linarith) hc (by linarith) ha hp
      have hP := hp0 (m + 1) (by omega)
      rw [prod_range_succ a (m + 1), prod_range_succ p (m + 1)]
      calc (∏ j ∈ range (m + 1), a j) * a (m + 1)
          ≤ ((1 + 2 * c / 7) ^ 2 * (2 * (m : ℝ) + 1) * ∏ j ∈ range (m + 1), p j) * a (m + 1) :=
            mul_le_mul_of_nonneg_right ih' ha0
        _ = (1 + 2 * c / 7) ^ 2 * (∏ j ∈ range (m + 1), p j) *
            ((2 * ((m : ℝ) + 1) - 1) * a (m + 1)) := by ring
        _ ≤ (1 + 2 * c / 7) ^ 2 * (∏ j ∈ range (m + 1), p j) *
            ((2 * ((m : ℝ) + 1) + 1) * p (m + 1)) :=
            mul_le_mul_of_nonneg_left hstep (mul_nonneg hK0 hP)
        _ = _ := by push_cast; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hK
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := key m le_rfl
    have hP := hp0 (m + 1) le_rfl
    calc _ ≤ _ := h1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hP
        apply mul_le_mul_of_nonneg_left _ hK0
        push_cast; linarith
open Finset in
private lemma prod_le_cube_mul_prod_of_bracket_chain (b c : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ b) (hc : 1 ≤ c)
    (hcb : c + 2 ≤ b) (a d p : ℕ → ℝ)
    (h : ∀ j < n, 0 ≤ a j ∧ a j ≤ (d j + 1 + c) ^ 2 ∧ 5 / 2 + 2 * c * (j : ℝ) ≤ d j ∧
      (d j + 1) ^ 2 ≤ p j) :
    ∏ j ∈ range n, a j ≤ b ^ 3 * ∏ j ∈ range n, p j := by
  have hP : 0 ≤ ∏ j ∈ range n, p j :=
    prod_nonneg fun j hj => le_trans (sq_nonneg _) (h j (by simpa using hj)).2.2.2
  have h1 : 1 + 2 * c / 7 ≤ b / 2 := by linarith
  have h2 : (1 + 2 * c / 7) ^ 2 ≤ (b / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have hn0 : (0:ℝ) ≤ n := n.cast_nonneg
  have hK : (1 + 2 * c / 7) ^ 2 * (2 * (n : ℝ) + 1) ≤ b ^ 3 := by
    nlinarith [mul_le_mul h2 (by linarith : 2 * (n:ℝ) + 1 ≤ 2 * b + 1) (by positivity)
      (by positivity), mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ 2 * b - 1)]
  calc _ ≤ _ := prod_le_mul_odd_mul_prod_of_bracket_chain c hc a d p n h
    _ ≤ b ^ 3 * ∏ j ∈ range n, p j := mul_le_mul_of_nonneg_right hK hP
open Finset in
private lemma sq_le_abs_mul_of_le_abs (D X X' : ℝ) (hD : 0 ≤ D) (h : D ≤ |X|) (h' : D ≤ |X'|) :
    D ^ 2 ≤ |X * X'| := by
  rw [abs_mul, sq]
  exact mul_le_mul h h' hD (abs_nonneg _)
open Finset in
private lemma bracket_product_le_of_neg_between_lemma (k r l : ℕ) (b c Y : ℝ) (lam u u' : ℕ → ℝ)
    (h1l : 1 ≤ l) (hlk : l ≤ k) (hc : 1 ≤ c) (hcb : c + 2 ≤ b) (hkb : (k : ℝ) ≤ b)
    (hul : |u l| ≤ b) (hu'l : |u' l| ≤ b)
    (hlam : ∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b)
    (hsp : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s)
    (hint : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k →
      (s ≠ l → lam s + 1 / 2 ≤ u s) ∧ (s + 1 ≠ l → u (s + 1) + 1 / 2 ≤ lam s))
    (hint' : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k →
      (s ≠ l → lam s + 1 / 2 ≤ u' s) ∧ (s + 1 ≠ l → u' (s + 1) + 1 / 2 ≤ lam s))
    (hdec : ∀ i : ℕ, 1 ≤ i → i ≤ k - 1 → u (i + 1) ≤ u i - 1 ∧ u' (i + 1) ≤ u' i - 1 ∧
      u (i + 1) ≤ u' i - 1 ∧ u' (i + 1) ≤ u i - 1)
    (hY : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) *
      (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)) ≤
      b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
  obtain ⟨hY1, hY2⟩ := hY
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hYb1 : -b + 2 ≤ -Y := by have := (abs_le.mp hul).1; linarith
  have hYb2 : -Y ≤ b - 2 := by have := (abs_le.mp hu'l).2; linarith
  have hspread := lam_add_two_mul_le_of_consecutive k c lam hsp
  have hA0 : ∀ s, 0 ≤ (|Y + lam s| + c) * (|Y + 1 + lam s| + c) := fun s =>
    mul_nonneg (by linarith [abs_nonneg (Y + lam s)]) (by linarith [abs_nonneg (Y + 1 + lam s)])
  rw [← prod_mul_distrib]
  have hLR : Disjoint (Ico 1 (l - 1)) (Ico (l + 1) k) := by
    rw [disjoint_left]; intro s h1 h2; simp only [mem_Ico] at h1 h2; omega
  have hsub : Ico 1 (l - 1) ∪ Ico (l + 1) k ⊆ Icc 1 (k + 2 * r + 1) := by
    intro s hs; simp only [mem_union, mem_Ico, mem_Icc] at hs ⊢; omega
  rw [← prod_sdiff hsub, prod_union hLR]
  have hA : ∀ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ b ^ 4 := by
    intro s hs
    have hl := abs_le.mp (hlam s hs)
    have e1 : |Y + lam s| ≤ 2 * b - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e2 : |Y + 1 + lam s| ≤ 2 * b - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e3 : (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ (3 * b) * (3 * b) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [abs_nonneg (Y + 1 + lam s)])
        (by linarith)
    have hb9 : 9 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb9 (sq_nonneg b)]
  have hT : ∏ s ∈ Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k),
      (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ b ^ (4 * (2 * r + 4)) := by
    have hcard : (Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k)).card ≤ 2 * r + 4 := by
      have h1 := card_sdiff_add_card_eq_card hsub
      rw [card_union_of_disjoint hLR, Nat.card_Icc, Nat.card_Ico, Nat.card_Ico] at h1
      omega
    calc _ ≤ ∏ s ∈ Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k), b ^ 4 :=
          prod_le_prod (fun s _ => hA0 s) (fun s hs => hA s (mem_sdiff.mp hs).1)
      _ = (b ^ 4) ^ (Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k)).card := prod_const _
      _ ≤ (b ^ 4) ^ (2 * r + 4) := pow_le_pow_right₀ (one_le_pow₀ hb1) hcard
      _ = b ^ (4 * (2 * r + 4)) := (pow_mul b 4 _).symm
  have hL : ∏ s ∈ Ico 1 (l - 1), (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤
      b ^ 3 * ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
    have r1 : ∏ j ∈ range (l - 1 - 1), (|Y + lam (1 + (l - 1 - 1 - 1 - j))| + c) *
        (|Y + 1 + lam (1 + (l - 1 - 1 - 1 - j))| + c) =
        ∏ j ∈ range (l - 1 - 1), (|Y + lam (1 + j)| + c) * (|Y + 1 + lam (1 + j)| + c) :=
      prod_range_reflect (fun j => (|Y + lam (1 + j)| + c) * (|Y + 1 + lam (1 + j)| + c)) _
    have r2 : ∏ j ∈ range (l - 1 - 1), |(Y + 1 / 2 + u (1 + (l - 1 - 1 - 1 - j))) *
        (Y + 1 / 2 + u' (1 + (l - 1 - 1 - 1 - j)))| =
        ∏ j ∈ range (l - 1 - 1), |(Y + 1 / 2 + u (1 + j)) * (Y + 1 / 2 + u' (1 + j))| :=
      prod_range_reflect (fun j => |(Y + 1 / 2 + u (1 + j)) * (Y + 1 / 2 + u' (1 + j))|) _
    rw [← r1, ← r2]
    have hn : ((l - 1 - 1 : ℕ) : ℝ) ≤ b := by
      have : ((l - 1 - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : l - 1 - 1 ≤ k)
      linarith
    apply prod_le_cube_mul_prod_of_bracket_chain b c (l - 1 - 1) hn hc hcb _
      (fun j => Y + lam (1 + (l - 1 - 1 - 1 - j)))
    intro j hj
    beta_reduce
    set s := 1 + (l - 1 - 1 - 1 - j) with hs
    have hs1 : 1 ≤ s := by omega
    have hsj : s + j = l - 2 := by omega
    have e0 := hspread j s hs1 (by omega)
    rw [hsj] at e0
    have e1 := (hint (l - 2) (by omega) (by omega)).2 (by omega)
    rw [show l - 2 + 1 = l - 1 by omega] at e1
    have e2 := (hdec (l - 1) (by omega) (by omega)).2.2.2
    rw [show l - 1 + 1 = l by omega] at e2
    have f1 := (hint s hs1 (by omega)).1 (by omega)
    have f2 := (hint' s hs1 (by omega)).1 (by omega)
    have hc0 : (0:ℝ) ≤ 2 * c * j := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    refine ⟨hA0 s, ?_, by linarith, ?_⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; nlinarith
    · exact sq_le_abs_mul_of_le_abs _ _ _ (by linarith) (le_abs.mpr (Or.inl (by linarith)))
        (le_abs.mpr (Or.inl (by linarith)))
  have hR : ∏ s ∈ Ico (l + 1) k, (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤
      b ^ 3 * ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range, show k + 1 - (l + 2) = k - (l + 1) by omega]
    have hn : ((k - (l + 1) : ℕ) : ℝ) ≤ b := by
      have : ((k - (l + 1) : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : k - (l + 1) ≤ k)
      linarith
    apply prod_le_cube_mul_prod_of_bracket_chain b c (k - (l + 1)) hn hc hcb _
      (fun j => -Y - lam (l + 1 + j) - 1)
    intro j hj
    beta_reduce
    have e0 := hspread j (l + 1) (by omega) (by omega)
    have e1 := (hint (l + 1) (by omega) (by omega)).1 (by omega)
    have e2 := (hdec l h1l (by omega)).1
    have f1 := (hint (l + 1 + j) (by omega) (by omega)).2 (by omega)
    have f2 := (hint' (l + 1 + j) (by omega) (by omega)).2 (by omega)
    rw [show l + 1 + j + 1 = l + 2 + j by ring] at f1 f2
    have hc0 : (0:ℝ) ≤ 2 * c * j := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    refine ⟨hA0 _, ?_, by linarith, ?_⟩
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; nlinarith
    · exact sq_le_abs_mul_of_le_abs _ _ _ (by linarith) (le_abs.mpr (Or.inr (by linarith)))
        (le_abs.mpr (Or.inr (by linarith)))
  have hLn : 0 ≤ ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hRn : 0 ≤ ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hPQ : (∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
      ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| ≤
      ∏ i ∈ Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    have hLR' : Disjoint (Ico 1 (l - 1)) (Ico (l + 2) (k + 1)) := by
      rw [disjoint_left]; intro s h1 h2; simp only [mem_Ico] at h1 h2; omega
    have hsub' : Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1) ⊆ Icc 1 k := by
      intro s hs; simp only [mem_union, mem_Ico, mem_Icc] at hs ⊢; omega
    rw [← prod_sdiff hsub', prod_union hLR']
    have hrest : (1:ℝ) ≤ ∏ i ∈ Icc 1 k \ (Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1)),
        |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
      calc (1:ℝ) = ∏ i ∈ Icc 1 k \ (Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1)), (1:ℝ) :=
            prod_const_one.symm
        _ ≤ _ := by
          apply prod_le_prod (fun _ _ => zero_le_one)
          intro i hi
          simp only [mem_sdiff, mem_union, mem_Ico, mem_Icc] at hi
          rw [abs_mul]
          have key : 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
            rcases (by omega : (i = l - 1 ∧ 2 ≤ l) ∨ i = l ∨ (i = l + 1 ∧ l + 1 ≤ k))
              with ⟨hi1, hl2⟩ | hi1 | ⟨hi1, hl2⟩
            · have e := hdec (l - 1) (by omega) (by omega)
              rw [show l - 1 + 1 = l by omega] at e
              rw [hi1]
              exact ⟨le_abs.mpr (Or.inl (by linarith [e.2.2.2])),
                le_abs.mpr (Or.inl (by linarith [e.2.1]))⟩
            · rw [hi1]
              exact ⟨le_abs.mpr (Or.inr (by linarith)), le_abs.mpr (Or.inl (by linarith))⟩
            · have e := hdec l h1l (by omega)
              rw [hi1]
              exact ⟨le_abs.mpr (Or.inr (by linarith [e.1])),
                le_abs.mpr (Or.inr (by linarith [e.2.2.2]))⟩
          exact one_le_mul_of_one_le_of_one_le key.1 key.2
    calc _ = 1 * ((∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
          ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hrest (mul_nonneg hLn hRn)
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  calc _ ≤ b ^ (4 * (2 * r + 4)) *
        ((b ^ 3 * ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
        (b ^ 3 * ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|)) :=
        mul_le_mul hT (mul_le_mul hL hR (prod_nonneg fun s _ => hA0 s) (mul_nonneg hb3 hLn))
          (mul_nonneg (prod_nonneg fun s _ => hA0 s) (prod_nonneg fun s _ => hA0 s))
          (pow_nonneg hb0 _)
    _ = b ^ (4 * (2 * r + 4) + 3 + 3) *
        ((∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
        ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) := by
        rw [pow_add, pow_add]; ring
    _ ≤ b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
        mul_le_mul (pow_le_pow_right₀ hb1 (by omega)) hPQ (mul_nonneg hLn hRn) (pow_nonneg hb0 _)
end GlobalTheory
end

set_option autoImplicit false
open Finset
open GlobalTheory
open Finset
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (k r l : ℕ) (b c Y : ℝ) (lam u u' : ℕ → ℝ), 1 ≤ l → l ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |u l| ≤ b → |u' l| ≤ b → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u s) ∧ (s + 1 ≠ l → u (s + 1) + 1 / 2 ≤ lam s)) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u' s) ∧ (s + 1 ≠ l → u' (s + 1) + 1 / 2 ≤ lam s)) → (∀ i : ℕ, 1 ≤ i → i ≤ k - 1 → u (i + 1) ≤ u i - 1 ∧ u' (i + 1) ≤ u' i - 1 ∧ u (i + 1) ≤ u' i - 1 ∧ u' (i + 1) ≤ u i - 1) → ((u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) ∨ (u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2)) → (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) * (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)) ≤ b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
  intro k r l b c Y lam u u' h1l hlk hc hcb hkb hul hu'l hlam hsp hint hint' hdec hY
  rcases hY with hY | hY
  · exact bracket_product_le_of_neg_between_lemma k r l b c Y lam u u' h1l hlk hc hcb hkb hul hu'l hlam hsp hint
      hint' hdec hY
  · have h := bracket_product_le_of_neg_between_lemma k r l b c Y lam u' u h1l hlk hc hcb hkb hu'l hul hlam hsp
      hint' hint (fun i hi hik => by
        obtain ⟨a1, a2, a3, a4⟩ := hdec i hi hik
        exact ⟨a2, a1, a4, a3⟩) hY
    calc _ ≤ _ := h
      _ = _ := by
        congr 1
        exact prod_congr rfl fun i _ => by rw [mul_comm]
end _root_.GlobalTheory
end GlobalTheory
