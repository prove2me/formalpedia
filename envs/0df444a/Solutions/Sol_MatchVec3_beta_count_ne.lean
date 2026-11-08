-- Prove2me | solution 1 for MatchVec3.beta_count_ne
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:29:22.926202+00:00
-- url     : https://prove2.me/submissions/99bf3bd5-4f33-47ae-ac17-73f5629184d9

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn

open MatchVec3 in
theorem solution {m p q a b n K : ℕ} {α β : ZMod m}
    (hstr : ResidueStructure m p q a b α β)
    (U V : Fin K → Fin n → ZMod m) (hfam : IsMVFamily U V) (hoff : OffDiagIn U V α β)
    (A B : Finset (Fin K)) (hdisj : Disjoint A B) (hcard : A.card = B.card)
    (hsum : ∑ j ∈ A, U j = ∑ j ∈ B, U j) (i : Fin K) (hi : i ∈ A) :
    (B.filter fun j => U j ⬝ᵥ V i = β).card ≠ (A.filter fun j => U j ⬝ᵥ V i = β).card := by
  intro heq
  have hβ0 : β ≠ 0 := fun h => hstr.β_not_dvd (by rw [h, ZMod.val_zero]; exact dvd_zero _)
  have hα0 : α ≠ 0 := fun h => hstr.α_not_dvd (by rw [h, ZMod.val_zero]; exact dvd_zero _)
  have hfi : U i ⬝ᵥ V i = 0 := hfam.1 i
  have hiB : i ∉ B := Finset.disjoint_left.mp hdisj hi
  have key : ∀ S : Finset (Fin K), (∀ j ∈ S, j ≠ i) →
      ∑ j ∈ S, U j ⬝ᵥ V i =
        ((S.filter (fun j => U j ⬝ᵥ V i = β)).card : ZMod m) * β +
          ((S.filter (fun j => ¬ U j ⬝ᵥ V i = β)).card : ZMod m) * α := by
    intro S hS
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => U j ⬝ᵥ V i = β)]
    have h1 : ∑ j ∈ S.filter (fun j => U j ⬝ᵥ V i = β), U j ⬝ᵥ V i =
        ∑ j ∈ S.filter (fun j => U j ⬝ᵥ V i = β), β :=
      Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2
    have h2 : ∑ j ∈ S.filter (fun j => ¬ U j ⬝ᵥ V i = β), U j ⬝ᵥ V i =
        ∑ j ∈ S.filter (fun j => ¬ U j ⬝ᵥ V i = β), α := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hjS, hjne⟩ := Finset.mem_filter.mp hj
      rcases hoff j i (hS j hjS) with h | h
      · exact h
      · exact absurd h hjne
    rw [h1, h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hA : ∑ j ∈ A, U j ⬝ᵥ V i = ∑ j ∈ A.erase i, U j ⬝ᵥ V i := by
    rw [← Finset.add_sum_erase A _ hi, hfi, zero_add]
  have hV : ∑ j ∈ A, U j ⬝ᵥ V i = ∑ j ∈ B, U j ⬝ᵥ V i := by
    rw [← sum_dotProduct, ← sum_dotProduct, hsum]
  have eA := key (A.erase i) (fun j hj => Finset.ne_of_mem_erase hj)
  have eB := key B (fun j hj h => hiB (h ▸ hj))
  have hcA : ((A.erase i).filter (fun j => U j ⬝ᵥ V i = β)).card =
      (A.filter (fun j => U j ⬝ᵥ V i = β)).card := by
    rw [Finset.filter_erase]
    apply congrArg
    apply Finset.erase_eq_of_notMem
    intro hmem
    exact hβ0 (by rw [← (Finset.mem_filter.mp hmem).2, hfi])
  have hsA := Finset.card_filter_add_card_filter_not (s := A.erase i)
    (fun j => U j ⬝ᵥ V i = β)
  have hsB := Finset.card_filter_add_card_filter_not (s := B) (fun j => U j ⬝ᵥ V i = β)
  have hcardA := Finset.card_erase_of_mem hi
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hr : (B.filter (fun j => ¬ U j ⬝ᵥ V i = β)).card =
      ((A.erase i).filter (fun j => ¬ U j ⬝ᵥ V i = β)).card + 1 := by
    omega
  have e4 : (((A.erase i).filter (fun j => U j ⬝ᵥ V i = β)).card : ZMod m) =
      ((B.filter (fun j => U j ⬝ᵥ V i = β)).card : ZMod m) := by
    rw [hcA, heq]
  have e5 : ((B.filter (fun j => ¬ U j ⬝ᵥ V i = β)).card : ZMod m) =
      (((A.erase i).filter (fun j => ¬ U j ⬝ᵥ V i = β)).card : ZMod m) + 1 := by
    rw [hr]; push_cast; ring
  have e3 : ∑ j ∈ A.erase i, U j ⬝ᵥ V i = ∑ j ∈ B, U j ⬝ᵥ V i := by rw [← hA, hV]
  apply hα0
  linear_combination eA - eB - e3 + β * e4 - α * e5
