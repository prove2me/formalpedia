-- Prove2me | solution 1 for GridHam.hasHamPath_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:25:05.663945+00:00
-- url     : https://prove2.me/submissions/9b65b32f-b31a-4a27-8348-9e14c1248f70

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_nodup_map_coord
public import Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66
public import Theorems.Thm_GridHam_chainAdjacent_map
public import Theorems.Thm_GridHam_adjacent_swapXY

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath height width (swapXY s) (swapXY t) := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    unfold HasHamPath
    refine ⟨(a :: l).map swapXY, ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen, Nat.mul_comm]
    · show (swapXY a :: l.map swapXY).head? = some (swapXY s)
      rw [has]
      rfl
    · exact getLast?_map_coord swapXY (a :: l) t hlast
    · apply nodup_map_coord swapXY _ (a :: l) hnd
      intro v w hvw
      unfold swapXY at hvw
      have h1 := congrArg Prod.fst hvw
      have h2 := congrArg Prod.snd hvw
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold swapXY
      dsimp only
      exact ⟨hu'.2, hu'.1⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords height width v).mp hv
      have hu := hcov (swapXY v) ((mem_allCoords width height _).mpr
        ⟨by unfold swapXY; dsimp only; exact hy, by unfold swapXY; dsimp only; exact hx⟩)
      exact List.mem_map.mpr ⟨swapXY v, hu, rfl⟩
    · exact chainAdjacent_map swapXY (fun v w hvw => adjacent_swapXY hvw) (a :: l) hch
end GridHam
