-- Prove2me | solution 1 for KneserColouring.altCount_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:53.423721+00:00
-- url     : https://prove2.me/submissions/cc68660f-4445-4282-9490-7463c4fdda8a

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_isAlt_singleton
public import Theorems.Thm_KneserColouring_IsRoom_perm_lt


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) : altCount lab 1 = 1 := by
  rw [altCount, card_eq_one]
  refine ⟨(fun c => if c.val = 0 then 1 else 0, 1), ?_⟩
  ext ⟨t, ρ⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  have hL : ∀ r : Room n, labSet lab 1 r = {rlab lab r 0} := fun r => by simp [labSet]
  constructor
  · rintro ⟨hU, -, -⟩
    have ht : t = fun c => if c.val = 0 then 1 else 0 := by
      funext c
      split_ifs with hc
      · exact hU.2 c (by omega)
      · by_contra h
        exact hc (by have := (hU.1.1 c).1 h; omega)
    have hρ : ρ = 1 := by
      ext c
      by_cases hc : c.val = 0
      · have := hU.1.perm_lt (c := c) (by omega)
        simp only [Equiv.Perm.coe_one, id_eq]
        simp only at this
        omega
      · simp only [Equiv.Perm.coe_one, id_eq]
        exact congrArg Fin.val (hU.1.2 c (by omega))
    rw [ht, hρ]
  · intro heq
    rw [heq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro c
      simp only
      split_ifs with hc <;> simp [hc]
    · intro c _
      rfl
    · intro c hc
      simp only
      rw [if_pos (by omega)]
    · rw [hL]
      exact isAlt_singleton _
    · rw [hL, card_singleton]
end KneserColouring
