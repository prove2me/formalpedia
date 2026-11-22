-- Prove2me | solution 1 for GridHam.validPath_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:59:25.295839+00:00
-- url     : https://prove2.me/submissions/ff775f63-5f79-4b22-b29b-339e8e996702

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_reverse

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) : ValidPath width height t s p.reverse := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
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
