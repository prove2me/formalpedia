-- Prove2me | solution 1 for NashWilliams.exists_tight_of_not_req
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:22:14.361879+00:00
-- url     : https://prove2.me/submissions/d34daaa0-7cf7-45e7-9465-5475c22fa899

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
public import Theorems.Thm_NashWilliams_cutF_erase_eq
public import Theorems.Thm_NashWilliams_cutF_le_erase_add_one


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {i : ι} (hi : ¬ Req K T ends (F.erase i)) :
    ∃ S, Tight K T ends F S ∧ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)) := by
  simp only [Req, not_forall, not_le] at hi
  obtain ⟨S, hST, hne, hneT, hlt⟩ := hi
  have h1 := cutF_le_erase_add_one ends F S i
  have h2 := hreq S hST hne hneT
  refine ⟨S, ⟨hST, hne, hneT, by omega⟩, ?_⟩
  intro hc
  rw [cutF_erase_eq ends F S i (not_not.2 hc)] at hlt
  omega
end NashWilliams
