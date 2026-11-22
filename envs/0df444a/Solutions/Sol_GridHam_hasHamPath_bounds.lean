-- Prove2me | solution 1 for GridHam.hasHamPath_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:13.147416+00:00
-- url     : https://prove2.me/submissions/2f2c1fc6-218b-44b6-a660-8be4da278f14

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_P2M_GridHam_mem_of_getLast__beac85f634f6

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : InBounds width height s ∧ InBounds width height t := by
  obtain ⟨p, _, hhead, hlast, _, hin, _, _⟩ := h
  refine ⟨hin s ?_, hin t (mem_of_getLast? p t hlast)⟩
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    rw [← has]
    simp
end GridHam
