-- Prove2me | solution 1 for GlobalTheory.BadShare.TwoRoots.card_le_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:37.738684+00:00
-- url     : https://prove2.me/submissions/d9c6d33e-b7b9-4964-90fd-79d9b75fdb49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_pow_card_pow_natDegree
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_pow_eq_pow_padicVal
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_exists_small_degree
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_sum_pow_le
import Theorems.Thm_GlobalTheory_BadShare_mem_sqSet
import Theorems.Thm_GlobalTheory_BadShare_root_ne_zero
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff_of_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots
namespace GlobalTheory.BadShare.TwoRoots
theorem _root_.solution (g : ℕ) [Fact g.Prime] (d l : ℕ) (hd : 2 ≤ d) (hl : l.Prime) :
    ((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card ≤
      l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  set S := (sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y with hS
  set L := l ^ padicValNat l (g ^ d - 1) with hL
  have hL0 : 0 < L := pow_pos hl.pos _
  let Q : ℕ → (AlgebraicClosure (ZMod g))[X] := fun e => X ^ (L * g ^ e) - X ^ L
  have hQ : ∀ e, 1 ≤ e → (Q e).natDegree = L * g ^ e := by
    intro e he
    have : 1 < g ^ e := Nat.one_lt_pow (by omega) hg
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow, natDegree_X_pow]; nlinarith
  let B : Finset (AlgebraicClosure (ZMod g)) := (Finset.Icc 1 (d / 2)).biUnion fun e => (Q e).roots.toFinset
  have hB : B.card ≤ 2 * (L * g ^ (d / 2)) := by
    calc B.card ≤ ∑ e ∈ Finset.Icc 1 (d / 2), (Q e).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Finset.Icc 1 (d / 2), L * g ^ e := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [← hQ e (Finset.mem_Icc.1 he).1]
        exact (Multiset.toFinset_card_le _).trans (card_roots' _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have := Nat.mul_le_mul_left L (sum_pow_le hg (d / 2))
        linarith
  have hmemB : ∀ x y : AlgebraicClosure (ZMod g), minpoly (ZMod g) x = minpoly (ZMod g) y →
      (minpoly (ZMod g) x).natDegree = d → x ≠ y → x ^ L = y ^ L → x ∈ B := by
    intro x y h1 h2 h3 h4
    obtain ⟨e, he1, he2, he3⟩ := exists_small_degree h1 h3 h4
    rw [h2] at he2
    refine Finset.mem_biUnion.2 ⟨e, Finset.mem_Icc.2 ⟨he1, he2⟩, ?_⟩
    have hQ0 : Q e ≠ 0 := by
      intro h0
      have := hQ e he1
      rw [h0, natDegree_zero] at this
      have : 0 < L * g ^ e := by positivity
      omega
    rw [Multiset.mem_toFinset, mem_roots hQ0]
    simp [Q, pow_mul, he3]
  have hcount : 2 * S.card ≤ (B.filter fun x => minpoly (ZMod g) x ∈ S).card := by
    refine Finset.mul_card_image_le_card_of_maps_to (f := fun x => minpoly (ZMod g) x)
      (fun a ha => (Finset.mem_filter.1 ha).2) 2 ?_
    intro P hP
    obtain ⟨hP1, hirr, x, hx, y, hy, hxy, hs⟩ := Finset.mem_filter.1 hP
    obtain ⟨hmon, hdeg, -, h0⟩ := mem_sqSet.1 hP1
    have ex := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hx).2 hmon).symm
    have ey := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hmon).symm
    have hx0 := root_ne_zero h0 hx
    have hy0 := root_ne_zero h0 hy
    have hgd : 1 < g ^ d := Nat.one_lt_pow (by omega) hg
    have hroot : ∀ t : AlgebraicClosure (ZMod g), t ≠ 0 → minpoly (ZMod g) t = P → t ^ (g ^ d - 1) = 1 := by
      intro t ht et
      have := pow_card_pow_natDegree t
      rw [et, hdeg] at this
      apply mul_right_cancel₀ ht
      rw [← pow_succ, Nat.sub_add_cancel hgd.le, this, one_mul]
    obtain ⟨a, ha⟩ := (samePart_iff_of_ne_zero hl hx0 hy0).1 hs
    have hLxy : x ^ L = y ^ L := pow_eq_pow_padicVal (by omega) hl (hroot x hx0 ex) (hroot y hy0 ey) ha
    have hxB := hmemB x y (ex.trans ey.symm) (by rw [ex, hdeg]) hxy hLxy
    have hyB := hmemB y x (ey.trans ex.symm) (by rw [ey, hdeg]) hxy.symm hLxy.symm
    rw [← Finset.card_pair hxy]
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_filter]
    rcases ht with rfl | rfl
    · exact ⟨⟨hxB, by rw [ex]; exact hP⟩, ex⟩
    · exact ⟨⟨hyB, by rw [ey]; exact hP⟩, ey⟩
  have := hcount.trans ((Finset.card_filter_le _ _).trans hB)
  omega
end GlobalTheory.BadShare.TwoRoots
