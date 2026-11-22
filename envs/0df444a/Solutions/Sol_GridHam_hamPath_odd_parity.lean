-- Prove2me | solution 1 for GridHam.hamPath_odd_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:23:38.647422+00:00
-- url     : https://prove2.me/submissions/d9ba75bb-6982-41d8-9888-7e8670ea1ce8

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
public import Theorems.Thm_GridHam_chain_parity_head_last
public import Theorems.Thm_GridHam_mem_allCoords_iff
public import Theorems.Thm_GridHam_cnt1_chain
public import Theorems.Thm_GridHam_cnt1_grid

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hodd : width % 2 = 1 ∧ height % 2 = 1) (h : HasHamPath width height s t) :
    parity s = 0 ∧ parity t = 0 := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, _, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    have hcount := cnt1_chain l a hch
    have hsub : List.Subperm (a :: l) (allCoords width height) :=
      List.Nodup.subperm hnd (fun v hv => (mem_allCoords_iff width height v).mpr (hin v hv))
    have hle : cnt1 (a :: l) ≤ cnt1 (allCoords width height) := by
      unfold cnt1
      exact List.Subperm.countP_le _ hsub
    have hgrid := cnt1_grid height hodd.2 width
    have hlen' : l.length + 1 = width * height := hlen
    have ha2 : parity a < 2 := by unfold parity; omega
    have hpa : parity a = 0 := by omega
    have hne : (a :: l) ≠ [] := by simp
    have hgl := getLast?_eq_getLast_of_ne_nil (a :: l) hne t hlast
    have key := chain_parity_head_last l a hch hne
    rw [hgl] at key
    refine ⟨by rw [← has]; exact hpa, by omega⟩
end GridHam
