-- Prove2me | solution 1 for HajnalSzemeredi.exists_equipartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:00.79408+00:00
-- url     : https://prove2.me/submissions/f3668889-e00d-402a-b4dc-70e120b8e264

module
public import Definitions.Def_HajnalSzemeredi_Cases
public import Definitions.Def_HajnalSzemeredi_Main
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution (P : Finset ℕ) (s : ℕ) :
    ∀ S : Finset V, S.card = s * P.card → ∃ c : V → ℕ, Into S c P ∧
      ∀ i ∈ P, (cls S c i).card = s := by
  induction P using Finset.induction_on with
  | empty =>
    intro S hS
    refine ⟨fun _ => 0, fun v hv => ?_, fun i hi => absurd hi (notMem_empty i)⟩
    simp at hS; subst hS; simp at hv
  | insert a P ha ih =>
    intro S hS
    rw [card_insert_of_notMem ha, Nat.mul_succ] at hS
    obtain ⟨Tₐ, hTS, hTcard⟩ := exists_subset_card_eq (s := S) (n := s) (by omega)
    obtain ⟨c, hc, hcard⟩ := ih (S \ Tₐ) (by rw [card_sdiff_of_subset hTS]; omega)
    refine ⟨fun v => if v ∈ Tₐ then a else c v, fun v hv => ?_, fun i hi => ?_⟩
    · by_cases hvT : v ∈ Tₐ
      · simp [hvT]
      · simp only [hvT, ite_false]
        exact mem_insert_of_mem (hc v (mem_sdiff.mpr ⟨hv, hvT⟩))
    · rcases mem_insert.mp hi with rfl | hi
      · rw [← hTcard]
        congr 1
        ext v
        simp only [mem_cls]
        constructor
        · rintro ⟨hv, hva⟩
          by_contra hvT
          simp only [hvT, ite_false] at hva
          exact ha (hva ▸ hc v (mem_sdiff.mpr ⟨hv, hvT⟩))
        · intro hvT
          exact ⟨hTS hvT, by simp [hvT]⟩
      · rw [← hcard i hi]
        congr 1
        ext v
        simp only [mem_cls, mem_sdiff]
        constructor
        · rintro ⟨hv, hvi⟩
          have hvT : v ∉ Tₐ := by
            intro hvT
            simp only [hvT, ite_true] at hvi
            exact ha (hvi ▸ hi)
          simp only [hvT, ite_false] at hvi
          exact ⟨⟨hv, hvT⟩, hvi⟩
        · rintro ⟨⟨hv, hvT⟩, hvi⟩
          exact ⟨hv, by simp [hvT, hvi]⟩
end HajnalSzemeredi
