-- Prove2me | solution 1 for GridHam.hasHamPath_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:58:43.387991+00:00
-- url     : https://prove2.me/submissions/ed2ab88c-144c-4fda-bedc-d5153dd7e933

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_reverse

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : HasHamPath width height t s := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  unfold HasHamPath
  refine ⟨p.reverse, ?_⟩
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse]
    exact hlen
  · simpa using hlast
  · simpa using hhead
  · exact List.nodup_reverse.mpr hnd
  · intro v hv
    exact hin v (List.mem_reverse.mp hv)
  · intro v hv
    exact List.mem_reverse.mpr (hcov v hv)
  · exact chainAdjacent_reverse p hch
end GridHam
