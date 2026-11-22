-- Prove2me | solution 1 for GridHam.hamPath_implies_diff_parity_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:15:28.271959+00:00
-- url     : https://prove2.me/submissions/512f5fbd-8072-4ef1-87c8-9af606b26176

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
public import Theorems.Thm_GridHam_chain_parity_head_last

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution
    (width height : ℕ) (s t : Coord) (heven : (width * height) % 2 = 0)
    (h : HasHamPath width height s t) : parity s ≠ parity t := by
  obtain ⟨p, hlen, hhead, hlast, _, _, _, hchain⟩ := h
  have hpne : p ≠ [] := by
    intro hcontra; rw [hcontra] at hhead; simp at hhead
  cases p with
  | nil => exact absurd rfl hpne
  | cons a rest =>
    have haseq : (a :: rest).head? = some a := rfl
    rw [haseq] at hhead
    injection hhead with heqas
    subst heqas
    have hne : (a :: rest) ≠ [] := by simp
    have hgl := getLast?_eq_getLast_of_ne_nil (a :: rest) hne t hlast
    have key := chain_parity_head_last rest a hchain hne
    rw [hgl] at key
    have hs2 : parity a < 2 := by unfold parity; omega
    have ht2 : parity t < 2 := by unfold parity; omega
    have hlen2 : rest.length + 1 = width * height := by
      have hcl : (a :: rest).length = rest.length + 1 := rfl
      omega
    omega
end GridHam
