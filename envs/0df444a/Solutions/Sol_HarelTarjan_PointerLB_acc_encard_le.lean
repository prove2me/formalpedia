-- Prove2me | solution 1 for HarelTarjan.PointerLB.acc_encard_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:09:18.618528+00:00
-- url     : https://prove2.me/submissions/7054417b-d50a-4ab9-b6ec-c69886634ced

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine



namespace HarelTarjan.PointerLB

open Finset

section accsec
variable {N : Type*} (ptr : N → Fin 2 → Option N)

def succS (X : Set N) : Set N := {b | ∃ m ∈ X, ∃ i : Fin 2, ptr m i = some b}

lemma acc_succ (j : ℕ) (a : N) : acc ptr (j + 1) a = acc ptr j a ∪ succS ptr (acc ptr j a) := rfl

lemma acc_mono_succ (j : ℕ) (a : N) : acc ptr j a ⊆ acc ptr (j + 1) a := by
  rw [acc_succ]; exact Set.subset_union_left

lemma acc_mono {j j' : ℕ} (h : j ≤ j') (a : N) : acc ptr j a ⊆ acc ptr j' a := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (acc_mono_succ ptr _ a)

lemma succS_mono {X Y : Set N} (h : X ⊆ Y) : succS ptr X ⊆ succS ptr Y := by
  rintro b ⟨m, hm, i, hi⟩; exact ⟨m, h hm, i, hi⟩

lemma acc_succ_sub (j : ℕ) (a : N) : acc ptr (j + 1) a ⊆ {a} ∪ succS ptr (acc ptr j a) := by
  induction j with
  | zero => rw [acc_succ]; rfl
  | succ j ih =>
    rw [acc_succ]
    apply Set.union_subset
    · exact ih.trans (Set.union_subset_union le_rfl (succS_mono ptr (acc_mono_succ ptr j a)))
    · exact Set.subset_union_right

lemma succS_encard (X : Set N) : (succS ptr X).encard ≤ 2 * X.encard := by
  have hsplit : succS ptr X = (⋃ i : Fin 2, {b | ∃ m ∈ X, ptr m i = some b}) := by
    ext b; simp only [succS, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨m, hm, i, hi⟩; exact ⟨i, m, hm, hi⟩
    · rintro ⟨i, m, hm, hi⟩; exact ⟨m, hm, i, hi⟩
  have hi : ∀ i : Fin 2, ({b | ∃ m ∈ X, ptr m i = some b} : Set N).encard ≤ X.encard := by
    intro i
    rw [← (Option.some_injective N).encard_image]
    refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le (fun m => ptr m i) X)
    rintro _ ⟨b, ⟨m, hm, hb⟩, rfl⟩; exact ⟨m, hm, hb⟩
  rw [hsplit]
  have : (⋃ i : Fin 2, {b | ∃ m ∈ X, ptr m i = some b} : Set N) =
      {b | ∃ m ∈ X, ptr m 0 = some b} ∪ {b | ∃ m ∈ X, ptr m 1 = some b} := by
    ext b; simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, h⟩; fin_cases i
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  rw [this]
  refine (Set.encard_union_le _ _).trans ?_
  rw [two_mul]; exact add_le_add (hi 0) (hi 1)

end accsec

theorem acc_encard_core {N : Type*} (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    (acc ptr j a).encard + 1 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => simp [acc]; norm_num
  | succ j ih =>
    have h1 := Set.encard_le_encard (acc_succ_sub ptr j a)
    have h2 := Set.encard_union_le ({a} : Set N) (succS ptr (acc ptr j a))
    have h3 := succS_encard ptr (acc ptr j a)
    rw [Set.encard_singleton] at h2
    calc (acc ptr (j + 1) a).encard + 1 ≤ (1 + 2 * (acc ptr j a).encard) + 1 := by
          gcongr; exact h1.trans (h2.trans (add_le_add le_rfl h3))
      _ = 2 * ((acc ptr j a).encard + 1) := by ring
      _ ≤ 2 * 2 ^ (j + 1) := by gcongr
      _ = 2 ^ (j + 1 + 1) := by ring

end HarelTarjan.PointerLB

open HarelTarjan.PointerLB

theorem solution {N : Type*} (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    (acc ptr j a).encard + 1 ≤ 2 ^ (j + 1) := by
  exact acc_encard_core ptr a j
