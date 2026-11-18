-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_cyc_bijective_mod0
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T01:14:11.17107+00:00
-- url     : https://prove2.me/submissions/dc8c4d05-2290-4974-b98d-5a29b5c9788e

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

open KnodelPrimeCordial

theorem labelF_block_image (q r : ℕ) (hr : r < 12) :
    labelF (12 * q + r) = 12 * q + labelF r := by
  interval_cases r <;> simp [labelF]

theorem labelF_block_values (d : ℕ) (hd : d < 12) :
    ∃ r : ℕ, r < 12 ∧ labelF r = d + 1 := by
  have h : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨
           d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 := by omega
  rcases h with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
  · exact ⟨3, by norm_num, by rw [h0]; simp [labelF]⟩
  · exact ⟨0, by norm_num, by rw [h1]; simp [labelF]⟩
  · exact ⟨4, by norm_num, by rw [h2]; simp [labelF]⟩
  · exact ⟨1, by norm_num, by rw [h3]; simp [labelF]⟩
  · exact ⟨2, by norm_num, by rw [h4]; simp [labelF]⟩
  · exact ⟨5, by norm_num, by rw [h5]; simp [labelF]⟩
  · exact ⟨8, by norm_num, by rw [h6]; simp [labelF]⟩
  · exact ⟨6, by norm_num, by rw [h7]; simp [labelF]⟩
  · exact ⟨9, by norm_num, by rw [h8]; simp [labelF]⟩
  · exact ⟨11, by norm_num, by rw [h9]; simp [labelF]⟩
  · exact ⟨7, by norm_num, by rw [h10]; simp [labelF]⟩
  · exact ⟨10, by norm_num, by rw [h11]; simp [labelF]⟩

theorem labelF_block_finset (q : ℕ) :
    (Finset.univ.image (fun r : Fin 12 => labelF (12 * q + r.val)))
      = Finset.Icc (12 * q + 1) (12 * q + 12) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨r, hr⟩
    rw [labelF_block_image q r.val r.isLt] at hr
    have h1 : 1 ≤ labelF r.val := by
      have := r.isLt
      interval_cases r.val <;> simp [labelF]
    have h2 : labelF r.val ≤ 12 := by
      have := r.isLt
      interval_cases r.val <;> simp [labelF]
    omega
  · intro hy
    have hd : y - 12 * q - 1 < 12 := by omega
    obtain ⟨r, hr12, hrv⟩ := labelF_block_values (y - 12 * q - 1) hd
    exact ⟨⟨r, hr12⟩, by rw [labelF_block_image q r hr12, hrv]; omega⟩

theorem labelF_range_block (k : ℕ) :
    (Finset.Icc (12 * k) (12 * k + 11)).image labelF
      = Finset.Icc (12 * k + 1) (12 * k + 12) := by
  have hset : Finset.Icc (12 * k) (12 * k + 11) =
      (Finset.univ : Finset (Fin 12)).image (fun r : Fin 12 => 12 * k + r.val) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨⟨x - 12 * k, by omega⟩, ?_⟩
      show 12 * k + (x - 12 * k) = x
      omega
    · rintro ⟨r, rfl⟩
      omega
  rw [hset, Finset.image_image]
  exact labelF_block_finset k

theorem labelF_image_range (N : ℕ) :
    (Finset.range (12 * N)).image labelF = Finset.Icc 1 (12 * N) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.range (12 * (k + 1)) =
        Finset.range (12 * k) ∪ Finset.Icc (12 * k) (12 * k + 11) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
      constructor
      · intro hx
        by_cases h : x < 12 * k
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by omega⟩
      · rintro (h | ⟨h1, h2⟩)
        · omega
        · omega
    have hlow : (Finset.range (12 * k)).image labelF = Finset.Icc 1 (12 * k) := ih
    have hhigh : (Finset.Icc (12 * k) (12 * k + 11)).image labelF
        = Finset.Icc (12 * k + 1) (12 * k + 12) := labelF_range_block k
    rw [hsplit, Finset.image_union, hlow, hhigh]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega

theorem labelF_injOn_fin (N : ℕ) {a b : Fin (12 * N)}
    (h : labelF a.val = labelF b.val) : a = b := by
  have himg := labelF_image_range N
  have hcard : ((Finset.range (12 * N)).image labelF).card
      = (Finset.range (12 * N)).card := by
    rw [himg, Finset.card_range, Nat.card_Icc]
    omega
  have hinj : Set.InjOn labelF (↑(Finset.range (12 * N)) : Set ℕ) :=
    Finset.injOn_of_card_image_eq hcard
  have := hinj (Finset.mem_range.mpr a.isLt) (Finset.mem_range.mpr b.isLt) h
  exact Fin.ext this

theorem solution (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    Set.BijOn (fun i : Fin n => labelF i.val) Set.univ (Set.Icc 1 n) := by
  obtain ⟨k, rfl⟩ := h12
  cases k with
  | zero => omega
  | succ m =>
    refine ⟨?_, ?_, ?_⟩
    · intro i _
      have hmem : labelF i.val ∈ (Finset.range (12 * (m + 1))).image labelF :=
        Finset.mem_image_of_mem _ (Finset.mem_range.mpr i.isLt)
      rw [labelF_image_range] at hmem
      exact Finset.mem_Icc.mp hmem
    · intro i _ j _ hij
      exact labelF_injOn_fin (m + 1) hij
    · intro y hy
      have hy' : y ∈ Finset.Icc 1 (12 * (m + 1)) := Finset.mem_Icc.mpr ⟨hy.1, hy.2⟩
      have hmem : y ∈ (Finset.range (12 * (m + 1))).image labelF := by
        rw [labelF_image_range]; exact hy'
      obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hmem
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, Set.mem_univ _, hiy⟩
