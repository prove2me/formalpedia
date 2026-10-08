-- Prove2me | solution 1 for KelsoCrawford.Returns.dr_iff_gs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:49:53.02065+00:00
-- url     : https://prove2.me/submissions/d82d353f-883c-48e8-9feb-ccfefa506c0d

import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology
open KelsoCrawford.Returns KelsoCrawford.Process
open scoped BigOperators

private lemma marginal (m : ℕ) (v : ℕ → ℝ) (hv : DR m v)
    (a b : ℕ) (hab : a ≤ b) (hb : b + 1 ≤ m) :
    v (b+1) - v b ≤ v (a+1) - v a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hh := hv (b+1) (by omega) hb
    simp only [Nat.add_sub_cancel] at hh
    exact hh.trans (ih (by omega))

private theorem symmetric_gs {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
    (hDR : DR (Fintype.card W) ybar) :
    GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by
  classical
  intro s hs s' hs' hss A hA
  let y := fun C : Finset W => ybar C.card
  let K := A.filter (fun i => s' i = s i)
  obtain ⟨B₀, _, hB₀⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun B => profit y B s') (by simp)
  have hB₀' : IsDemanded y s' B₀ := fun C => hB₀ C (by simp)
  let D := (Finset.univ : Finset (Finset W)).filter (IsDemanded y s')
  have hD : D.Nonempty := ⟨B₀, by simp [D, hB₀']⟩
  obtain ⟨B, hBD, hmax⟩ := D.exists_max_image (fun B => (K ∩ B).card) hD
  have hB : IsDemanded y s' B := (Finset.mem_filter.mp hBD).2
  refine ⟨B, hB, ?_⟩
  intro i hi
  by_contra hiB
  have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
  have his : s' i = s i := (Finset.mem_filter.mp hi).2
  have improve (B' : Finset W) (hprofit : profit y B s' ≤ profit y B' s')
      (hsub : K ∩ B ⊆ K ∩ B') (hi' : i ∈ B') : False := by
    have hd' : IsDemanded y s' B' := fun C => (hB C).trans hprofit
    have hm := hmax B' (by simp [D, hd'])
    have hstrict : K ∩ B ⊂ K ∩ B' := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro he
      have : i ∈ K ∩ B' := Finset.mem_inter.mpr ⟨hi, hi'⟩
      rw [← he] at this
      exact hiB (Finset.mem_inter.mp this).2
    exact (not_lt_of_ge hm) (Finset.card_lt_card hstrict)
  by_cases hc : B.card < A.card
  · have ha0 : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
    have hh := marginal (Fintype.card W) ybar hDR B.card (A.card-1)
      (by omega) (by have := Finset.card_le_univ A; omega)
    have hcA : (A.erase i).card = A.card-1 := Finset.card_erase_of_mem hiA
    have hcB : (insert i B).card = B.card+1 := Finset.card_insert_of_notMem hiB
    have hsA := hA (A.erase i)
    have sumA : ∑ j ∈ A.erase i, s j = (∑ j ∈ A, s j) - s i := by
      have := Finset.sum_erase_add A s hiA; linarith
    have hpr : profit y B s' ≤ profit y (insert i B) s' := by
      unfold profit y at *
      dsimp only at hsA
      rw [hcA, sumA] at hsA
      rw [hcB, Finset.sum_insert hiB, his]
      have he : A.card-1+1 = A.card := by omega
      rw [he] at hh
      linarith
    apply improve (insert i B) hpr
    · intro j hj; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1,
        Finset.mem_insert_of_mem (Finset.mem_inter.mp hj).2⟩
    · simp
  · have hjex : ∃ j ∈ B, j ∉ A := by
      by_contra hnone
      have hsub : B ⊆ A := by
        intro j hj
        by_contra hjA
        exact hnone ⟨j, hj, hjA⟩
      have he : B = A := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hiB (he.symm ▸ hiA)
    obtain ⟨j, hjB, hjA⟩ := hjex
    have hij : i ≠ j := by intro he; exact hjA (he ▸ hiA)
    have hiswap : j ∉ A.erase i := fun hj => hjA (Finset.mem_of_mem_erase hj)
    have hjswap : i ∉ B.erase j := fun hi => hiB (Finset.mem_of_mem_erase hi)
    have hsA := hA (insert j (A.erase i))
    have hcA : (insert j (A.erase i)).card = A.card := by
      rw [Finset.card_insert_of_notMem hiswap, Finset.card_erase_of_mem hiA]
      have := Finset.card_pos.mpr ⟨i, hiA⟩; omega
    have hcB : (insert i (B.erase j)).card = B.card := by
      rw [Finset.card_insert_of_notMem hjswap, Finset.card_erase_of_mem hjB]
      have := Finset.card_pos.mpr ⟨j, hjB⟩; omega
    have sumA : ∑ k ∈ A.erase i, s k = (∑ k ∈ A, s k) - s i := by
      have := Finset.sum_erase_add A s hiA; linarith
    have sumB : ∑ k ∈ B.erase j, s' k = (∑ k ∈ B, s' k) - s' j := by
      have := Finset.sum_erase_add B s' hjB; linarith
    have hpr : profit y B s' ≤ profit y (insert i (B.erase j)) s' := by
      unfold profit y at *
      dsimp only at hsA
      rw [hcA, Finset.sum_insert hiswap, sumA] at hsA
      rw [hcB, Finset.sum_insert hjswap, sumB, his]
      have hh := hss j
      linarith
    apply improve (insert i (B.erase j)) hpr
    · intro k hk
      have hkK := (Finset.mem_inter.mp hk).1
      have hkB := (Finset.mem_inter.mp hk).2
      have hkj : k ≠ j := by
        intro he; have := (Finset.mem_filter.mp hkK).1; exact hjA (he ▸ this)
      exact Finset.mem_inter.mpr ⟨hkK, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hkj, hkB⟩)⟩
    · simp

private lemma force_sets {W : Type} [Fintype W] [DecidableEq W]
    (y : Finset W → ℝ) (H : ℝ) (hH : ∀ C D, y C - y D < H)
    (S U : Finset W) (r : W → ℝ)
    (hrS : ∀ i ∈ S, r i = -H) (hrU : ∀ i, i ∉ U → r i = H)
    (C : Finset W) (hC : IsDemanded y r C) : S ⊆ C ∧ C ⊆ U := by
  constructor
  · intro i hi
    by_contra hiC
    have hh := hC (insert i C)
    unfold profit at hh
    rw [Finset.sum_insert hiC, hrS i hi] at hh
    have hb := hH C (insert i C)
    linarith
  · intro i hi
    by_contra hiU
    have hh := hC (C.erase i)
    have hsum := Finset.sum_erase_add C r hi
    rw [hrU i hiU] at hsum
    unfold profit at hh
    have hb := hH C (C.erase i)
    linarith

private lemma four_sets {W : Type} [DecidableEq W] (S C : Finset W) (a b : W)
    (hS : S ⊆ C) (hU : C ⊆ insert a (insert b S)) :
    C = S ∨ C = insert a S ∨ C = insert b S ∨ C = insert a (insert b S) := by
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
  · right; right; right; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · right; left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · right; right; left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop

private lemma gs_submodular {W : Type} [Fintype W] [DecidableEq W]
    (y : Finset W → ℝ) (hgs : GrossSubstitutesOn y Set.univ)
    (S : Finset W) (a b : W) (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    y (insert a (insert b S)) + y S ≤ y (insert a S) + y (insert b S) := by
  classical
  obtain ⟨Z, _, hZ⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun C => |y C|) (by simp)
  let H := 2 * |y Z| + 1
  have hH (C D : Finset W) : y C - y D < H := by
    have hC := hZ C (by simp)
    have hD := hZ D (by simp)
    dsimp [H]; linarith [le_abs_self (y C), neg_abs_le (y D)]
  let U := insert a (insert b S)
  let va := y (insert a S) - y S
  let vb := y (insert b S) - y S
  let δ := y U + y S - y (insert a S) - y (insert b S)
  by_contra hn
  have hd : 0 < δ := by dsimp [δ,U]; linarith
  let s : W → ℝ := fun i => if i ∈ S then -H else
    if i = a then va + δ/3 else if i = b then vb + δ/3 else H
  let s' : W → ℝ := fun i => if i = a then va + 2*δ else s i
  have hba : b ≠ a := hab.symm
  have haU : a ∉ insert b S := by simp [ha, hab]
  have hss : s ≤ s' := by
    intro i
    by_cases hi : i = a
    · subst i; simp [s',s,ha]; linarith
    · simp [s',hi]
  have hsS : ∀ i ∈ S, s i = -H := by intro i hi; simp [s, hi]
  have hsU : ∀ i, i ∉ U → s i = H := by
    intro i hi
    have hi' : i ≠ a ∧ i ≠ b ∧ i ∉ S := by simpa [U] using hi
    simp [s, hi'.1, hi'.2.1, hi'.2.2]
  have hs'S : ∀ i ∈ S, s' i = -H := by
    intro i hi
    have hiA : i ≠ a := by intro h; exact ha (h ▸ hi)
    simp [s',hiA,hsS i hi]
  have hs'U : ∀ i, i ∉ U → s' i = H := by
    intro i hi
    have hiA : i ≠ a := by intro h; subst i; exact hi (by simp [U])
    simp [s',hiA,hsU i hi]
  have sa : s a = va + δ/3 := by simp [s,ha]
  have sb : s b = vb + δ/3 := by simp [s,hb,hba]
  have s'a : s' a = va + 2*δ := by simp [s']
  have s'b : s' b = vb + δ/3 := by simp [s',hba,sb]
  have old_scores (C : Finset W) (hSC : S ⊆ C) (hCU : C ⊆ U) :
      profit y C s ≤ profit y U s := by
    rcases four_sets S C a b hSC hCU with rfl | rfl | rfl | rfl <;>
      simp [profit, U, Finset.sum_insert, haU, ha, hb, sa, sb] <;>
      dsimp [va,vb,δ,U] at * <;> linarith
  obtain ⟨B,_,hB⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun C => profit y C s) (by simp)
  have hB' : IsDemanded y s B := fun C => hB C (by simp)
  obtain ⟨hSB,hBU⟩ := force_sets y H hH S U s hsS hsU B hB'
  have hDemand : IsDemanded y s U := fun C => (hB' C).trans (old_scores B hSB hBU)
  obtain ⟨C,hC,hkeep⟩ := hgs s (by trivial) s' (by trivial) hss U hDemand
  have hbC : b ∈ C := hkeep (by simp [U,s',hba])
  obtain ⟨hSC,hCU⟩ := force_sets y H hH S U s' hs'S hs'U C hC
  have hz := hC S
  rcases four_sets S C a b hSC hCU with rfl | rfl | rfl | rfl
  · exact hb hbC
  · have : b ∈ S := by simpa [hba] using hbC
    exact hb this
  · simp [profit, Finset.sum_insert, hb, s'b] at hz
    dsimp [vb] at hz; linarith
  · simp [profit, Finset.sum_insert, haU, hb, s'a, s'b] at hz
    dsimp [va,vb,δ,U] at *; linarith

theorem solution {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ) :
    DR (Fintype.card W) ybar ↔ GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by
  classical
  constructor
  · exact symmetric_gs ybar
  · intro hgs w hw hw2
    obtain ⟨U,_,hU⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset W)) (n := w+1) (by simpa using hw2)
    have hUn : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a,ha⟩ := hUn
    have hUa : (U.erase a).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha,hU]; omega)
    obtain ⟨b,hb⟩ := hUa
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hbU : b ∈ U := Finset.mem_of_mem_erase hb
    let S := (U.erase a).erase b
    have haS : a ∉ S := by simp [S]
    have hbS : b ∉ S := by simp [S]
    have hSc : S.card = w-1 := by
      dsimp [S]; rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem ha,hU]; omega
    have hSa : (insert a S).card = w := by rw [Finset.card_insert_of_notMem haS,hSc]; omega
    have hSb : (insert b S).card = w := by rw [Finset.card_insert_of_notMem hbS,hSc]; omega
    have hSab : (insert a (insert b S)).card = w+1 := by
      rw [Finset.card_insert_of_notMem (by simp [haS,hba.symm]),hSb]
    have hh := gs_submodular (fun C : Finset W => ybar C.card) hgs S a b haS hbS hba.symm
    rw [hSab,hSa,hSb,hSc] at hh
    linarith

#print axioms solution
