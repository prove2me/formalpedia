-- Prove2me | solution 1 for GridHam.hasHamPath_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:57:21.924549+00:00
-- url     : https://prove2.me/submissions/00cb0dcf-f40f-481b-968a-efc6af1cfb7b

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66
public import Theorems.Thm_GridHam_nodup_map_coord_on
public import Theorems.Thm_GridHam_chainAdjacent_map_on

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath width height (reflectX width s) (reflectX width t) := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    unfold HasHamPath
    refine ⟨(a :: l).map (reflectX width), ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen]
    · show (reflectX width a :: l.map (reflectX width)).head? = some (reflectX width s)
      rw [has]
      rfl
    · exact getLast?_map_coord (reflectX width) (a :: l) t hlast
    · apply nodup_map_coord_on (reflectX width) (a :: l) _ hnd
      intro v hv u hu hvu
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold reflectX at hvu
      have h1 := congrArg Prod.fst hvu
      have h2 := congrArg Prod.snd hvu
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold reflectX
      dsimp only
      exact ⟨by omega, hu'.2⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords width height v).mp hv
      have hu := hcov (reflectX width v) ((mem_allCoords width height _).mpr
        ⟨by unfold reflectX; dsimp only; omega, by unfold reflectX; dsimp only; exact hy⟩)
      refine List.mem_map.mpr ⟨reflectX width v, hu, ?_⟩
      unfold reflectX
      ext
      · show width - 1 - (width - 1 - v.1) = v.1
        omega
      · rfl
    · apply chainAdjacent_map_on (reflectX width) (a :: l) _ hch
      intro v hv u hu hadj
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold Adjacent at hadj ⊢
      unfold reflectX
      dsimp only
      omega
end GridHam
