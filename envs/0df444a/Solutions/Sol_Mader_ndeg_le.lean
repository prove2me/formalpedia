-- Prove2me | solution 1 for Mader.ndeg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:36.809799+00:00
-- url     : https://prove2.me/submissions/3187566d-7b45-4ed1-8394-eeeef469464f

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
namespace Mader
theorem _root_.solution {S : Finset V} {v : V} (hv : v ∈ S) : ndeg G S v ≤ S.card - 1 := by
  classical
  unfold ndeg
  rw [← Finset.card_erase_of_mem hv]
  apply card_le_card
  intro w
  simp only [mem_filter, mem_erase]
  intro ⟨hw, hadj⟩
  exact ⟨(G.ne_of_adj hadj).symm, hw⟩
end Mader
