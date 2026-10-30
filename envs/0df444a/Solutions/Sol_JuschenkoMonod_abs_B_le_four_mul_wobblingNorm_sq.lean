-- Prove2me | solution 1 for JuschenkoMonod.abs_B_le_four_mul_wobblingNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:35:34.66048+00:00
-- url     : https://prove2.me/submissions/6e7d2b3b-e598-4b64-a202-18015229f0c4

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

lemma sum_Icc_eq (f : ℤ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc (-(m:ℤ)) m, f i =
      f 0 + ∑ j ∈ Finset.range m, (f ((j:ℤ) + 1) + f (-((j:ℤ) + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : Finset.Icc (-((m+1:ℕ):ℤ)) ((m+1:ℕ):ℤ) =
        insert ((m:ℤ)+1) (insert (-((m:ℤ)+1)) (Finset.Icc (-(m:ℤ)) m)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [this, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · ring
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; omega

lemma int_bound (g : Equiv.Perm ℤ) (k : ℕ) (hk : ∀ j, |g j - j| ≤ k) (m : ℕ) :
    0 ≤ ∑ i ∈ Finset.Icc (-(m:ℤ)) m, (|g i| - |i|) ∧
      ∑ i ∈ Finset.Icc (-(m:ℤ)) m, (|g i| - |i|) ≤ 4 * (k:ℤ)^2 := by
  set I := Finset.Icc (-(m:ℤ)) m with hI
  set S := I.image g with hS
  have hcard : S.card = I.card := Finset.card_image_of_injective _ g.injective
  have hsum : ∑ i ∈ I, (|g i| - |i|) = ∑ s ∈ S, |s| - ∑ i ∈ I, |i| := by
    rw [Finset.sum_sub_distrib, hS, Finset.sum_image (fun a _ b _ h => g.injective h)]
  have hr : (S \ I).card = (I \ S).card := Finset.card_sdiff_comm hcard
  have h1 : ∑ s ∈ S, |s| = ∑ s ∈ S ∩ I, |s| + ∑ s ∈ S \ I, |s| :=
    (Finset.sum_inter_add_sum_sdiff _ _ _).symm
  have h2 : ∑ i ∈ I, |i| = ∑ i ∈ I ∩ S, |i| + ∑ i ∈ I \ S, |i| :=
    (Finset.sum_inter_add_sum_sdiff _ _ _).symm
  rw [Finset.inter_comm] at h1
  have hA : ∀ s ∈ S \ I, (m:ℤ) + 1 ≤ |s| ∧ |s| ≤ m + k := by
    intro s hs
    rw [Finset.mem_sdiff, hS, Finset.mem_image] at hs
    obtain ⟨⟨i, hi, rfl⟩, hni⟩ := hs
    rw [hI, Finset.mem_Icc] at hi hni
    have := abs_le.mp (hk i)
    rcases abs_cases (g i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> constructor <;> omega
  have hB : ∀ i ∈ I \ S, (m:ℤ) + 1 - k ≤ |i| ∧ |i| ≤ m := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨hiI, hiS⟩ := hi
    have hjI : g.symm i ∉ I := by
      intro hj
      apply hiS
      rw [hS, Finset.mem_image]
      exact ⟨g.symm i, hj, by simp⟩
    have := abs_le.mp (hk (g.symm i))
    simp only [Equiv.apply_symm_apply] at this
    rw [hI, Finset.mem_Icc] at hiI hjI
    rcases abs_cases i with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> constructor <;> omega
  have hcardB : ((I \ S).card : ℤ) ≤ 2 * k := by
    have hsub : I \ S ⊆ Finset.Icc (-(m:ℤ)) ((k:ℤ) - m - 1) ∪ Finset.Icc ((m:ℤ) + 1 - k) m := by
      intro i hi
      have := hB i hi
      have hiI := (Finset.mem_sdiff.mp hi).1
      rw [hI, Finset.mem_Icc] at hiI
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      rcases abs_cases i with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at this <;> omega
    have h3 := Finset.card_le_card hsub
    have h4 := Finset.card_union_le (Finset.Icc (-(m:ℤ)) ((k:ℤ) - m - 1)) (Finset.Icc ((m:ℤ) + 1 - k) m)
    simp only [Int.card_Icc] at h4
    have : ((I \ S).card : ℤ) ≤ (((k:ℤ) - m - 1 + 1 - -(m:ℤ)).toNat + ((m:ℤ) + 1 - (m + 1 - k)).toNat : ℕ) := by
      exact_mod_cast h3.trans h4
    push_cast at this
    omega
  have hU : ∑ s ∈ S \ I, |s| ≤ (S \ I).card • ((m:ℤ) + k) :=
    Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hA s hs).2)
  have hL : (S \ I).card • ((m:ℤ) + 1) ≤ ∑ s ∈ S \ I, |s| :=
    Finset.card_nsmul_le_sum _ _ _ (fun s hs => (hA s hs).1)
  have hU' : ∑ i ∈ I \ S, |i| ≤ (I \ S).card • (m:ℤ) :=
    Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hB s hs).2)
  have hL' : (I \ S).card • ((m:ℤ) + 1 - k) ≤ ∑ i ∈ I \ S, |i| :=
    Finset.card_nsmul_le_sum _ _ _ (fun s hs => (hB s hs).1)
  simp only [nsmul_eq_mul] at hU hL hU' hL'
  rw [← hr] at hcardB hU' hL'
  have hrnn : (0:ℤ) ≤ ((S \ I).card : ℤ) := by positivity
  rw [hsum, h1, h2]
  constructor
  · nlinarith
  · nlinarith

theorem B_aux (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ)
    (u : ℝ) (hu : 0 ≤ u) : |B g u| ≤ 4 * wobblingNorm g ^ 2 := by
  obtain ⟨C, hC⟩ := hg
  have hbdd : BddAbove (Set.range fun j : ℤ => (|g j - j| : ℝ)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := hC j
    rw [Int.dist_eq] at this
    simpa using this
  have hw : ∀ j, (|g j - j| : ℝ) ≤ wobblingNorm g := fun j => le_ciSup hbdd j
  have hw0 : 0 ≤ wobblingNorm g := (abs_nonneg _).trans (hw 0)
  set k := ⌊wobblingNorm g⌋₊ with hk
  have hk' : ∀ j, |g j - j| ≤ (k:ℤ) := by
    intro j
    have h1 := hw j
    have h2 : ((|g j - j| : ℤ) : ℝ) ≤ wobblingNorm g := by push_cast; exact h1
    have h3 : |g j - j| ≤ ⌊wobblingNorm g⌋ := Int.le_floor.mpr h2
    have : (⌊wobblingNorm g⌋ : ℤ) = k := by rw [hk, ← Int.natCast_floor_eq_floor hw0]
    omega
  have hkw : (k:ℝ) ≤ wobblingNorm g := Nat.floor_le hw0
  set m := ⌊u⌋₊ with hm
  have hBeq : B g u = ((∑ i ∈ Finset.Icc (-(m:ℤ)) m, (|g i| - |i|) : ℤ) : ℝ) := by
    push_cast
    rw [sum_Icc_eq (fun i => |(g i : ℝ)| - |(i:ℝ)|) m]
    unfold B
    rw [Finset.sum_range_succ' _ m]
    simp only [b]
    simp
    push_cast
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : |(j:ℝ) + 1| = (j:ℝ) + 1 := abs_of_nonneg (by positivity)
    have e2 : |-1 + -(j:ℝ)| = (j:ℝ) + 1 := by
      rw [show (-1 + -(j:ℝ)) = -((j:ℝ) + 1) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [e1, e2]
  obtain ⟨h0, h1⟩ := int_bound g k hk' m
  rw [hBeq]
  have h1' : ((∑ i ∈ Finset.Icc (-(m:ℤ)) m, (|g i| - |i|) : ℤ) : ℝ) ≤ 4 * (k:ℝ)^2 := by exact_mod_cast h1
  have h0' : (0:ℝ) ≤ ((∑ i ∈ Finset.Icc (-(m:ℤ)) m, (|g i| - |i|) : ℤ) : ℝ) := by exact_mod_cast h0
  rw [abs_of_nonneg h0']
  have : (k:ℝ)^2 ≤ wobblingNorm g ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hkw
  linarith

end JuschenkoMonod

theorem solution : ∀ (g : Equiv.Perm ℤ) (_ : g ∈ IntervalExchange.wobbling ℤ)
    (u : ℝ) (_ : 0 ≤ u), |JuschenkoMonod.B g u| ≤ 4 * JuschenkoMonod.wobblingNorm g ^ 2 :=
  fun g hg u hu => JuschenkoMonod.B_aux g hg u hu
