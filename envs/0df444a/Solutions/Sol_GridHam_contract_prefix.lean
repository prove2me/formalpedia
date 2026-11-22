-- Prove2me | solution 1 for GridHam.contract_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:34:12.531254+00:00
-- url     : https://prove2.me/submissions/c2e7fe5a-59f2-4f52-8a8c-1316f3b08d42

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_P2M_GridHam_nodup_append_right__a582c6ad4e63
public import Theorems.Thm_GridHam_nodup_append_disjoint
public import Theorems.Thm_GridHam_chainAdjacent_map_on
public import Theorems.Thm_GridHam_chainAdjacent_suffix
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_nodup_map_coord_on
public import Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a
public import Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (u v a : Coord) (M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hv : ValidPath w 3 u v (M ++ a :: R)) :
    ValidPath (w - 2) 3 (shiftL2 a) (shiftL2 v) ((a :: R).map shiftL2) := by
  obtain ⟨hlen, _, hlast, hnd, hin, hcov, hch⟩ := hv
  have hdisj := nodup_append_disjoint M (a :: R) hnd
  have hnd2 := nodup_append_right' M (a :: R) hnd
  have hge : ∀ c ∈ a :: R, 2 ≤ c.1 := by
    intro c hc
    by_contra hlt
    have hcb := hin c (List.mem_append.mpr (Or.inr hc))
    unfold InBounds at hcb
    exact hdisj c (hM c (by omega) hcb.2) hc
  have haw : 2 ≤ a.1 := hge a (by simp)
  have hab := hin a (List.mem_append.mpr (Or.inr (by simp)))
  unfold InBounds at hab
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (M ++ a :: R).length = M.length + (R.length + 1) := by simp
    rw [List.length_map, List.length_cons]
    omega
  · rfl
  · rw [getLast?_append_cons] at hlast
    exact getLast?_map_coord shiftL2 (a :: R) v hlast
  · apply nodup_map_coord_on shiftL2 (a :: R) _ hnd2
    intro c hc d hd hcd
    have hc2 := hge c hc
    have hd2 := hge d hd
    unfold shiftL2 at hcd
    have h1 := congrArg Prod.fst hcd
    have h2 := congrArg Prod.snd hcd
    dsimp only at h1 h2
    ext
    · omega
    · omega
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hdb := hin d (List.mem_append.mpr (Or.inr hd))
    have hd2 := hge d hd
    unfold InBounds at hdb ⊢
    unfold shiftL2
    dsimp only
    exact ⟨by omega, hdb.2⟩
  · intro c hc
    obtain ⟨hcx, hcy⟩ := (mem_allCoords (w - 2) 3 c).mp hc
    have hd := hcov (c.1 + 2, c.2) ((mem_allCoords w 3 _).mpr ⟨by dsimp only; omega, hcy⟩)
    rcases List.mem_append.mp hd with hdM | hdR
    · have := hMx _ hdM
      dsimp only at this
      omega
    · refine List.mem_map.mpr ⟨_, hdR, ?_⟩
      unfold shiftL2
      ext
      · show c.1 + 2 - 2 = c.1
        omega
      · rfl
  · apply chainAdjacent_map_on shiftL2 (a :: R) _ (chainAdjacent_suffix M _ hch)
    intro x hx y hy hadj
    have hx2 := hge x hx
    have hy2 := hge y hy
    unfold Adjacent at hadj ⊢
    unfold shiftL2
    dsimp only
    omega
end GridHam
