-- Prove2me | solution 1 for GridHam.f2_height2_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:41:16.984946+00:00
-- url     : https://prove2.me/submissions/2a53e895-b6cf-4709-af3c-783ff2a5f772

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_GridHam_chain_proj_intermediate
public import Theorems.Thm_GridHam_chainAdjacent_prefix
public import Theorems.Thm_GridHam_nodup_not_mem_last
public import Theorems.Thm_GridHam_path_split_ends
public import Theorems.Thm_GridHam_chainAdjacent_tail
public import Theorems.Thm_GridHam_mem_allCoords


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (s t : Coord) (hsb : s.1 < w ∧ s.2 < 2)
    (htb : t.1 < w ∧ t.2 < 2) (hcol : s.1 = t.1) (hx0 : 0 < s.1) (hx1 : s.1 + 1 < w) :
    ¬ HasHamPath w 2 s t := by
  rintro ⟨p, hv⟩
  obtain ⟨m, hpm⟩ := path_split_ends hv (by omega)
  obtain ⟨_, _, _, hnd, hin, hcov, hch⟩ := hv
  rw [hpm] at hnd hin hcov hch
  obtain ⟨hsn, hndr⟩ := List.nodup_cons.mp hnd
  have hchm : chainAdjacent m = true := chainAdjacent_prefix m [t] (chainAdjacent_tail s _ hch)
  have htm : t ∉ m := nodup_not_mem_last m t hndr
  have hsm : s ∉ m := fun hm => hsn (List.mem_append.mpr (Or.inl hm))
  have hst : s.2 ≠ t.2 := by
    intro e
    apply hsn
    have hst' : s = t := by
      ext
      · exact hcol
      · exact e
    rw [hst']
    simp
  have inm : ∀ v : Coord, v.1 < w → v.2 < 2 → v ≠ s → v ≠ t → v ∈ m := by
    intro v hvx hvy hvs hvt
    have hv := hcov v ((mem_allCoords w 2 v).mpr ⟨hvx, hvy⟩)
    rcases List.mem_cons.mp hv with e | e
    · exact absurd e hvs
    · rcases List.mem_append.mp e with e2 | e2
      · exact e2
      · exact absurd (List.mem_singleton.mp e2) hvt
  have ha0 : ((0, 0) : Coord) ∈ m :=
    inm (0, 0) (by show 0 < w; omega) (by show 0 < 2; omega)
      (fun e => by rw [← e] at hx0; exact absurd hx0 (by show ¬ 0 < 0; omega))
      (fun e => by rw [← e] at hcol; exact absurd hx0 (by show ¬ 0 < s.1; rw [hcol]; omega))
  have hb0 : ((w - 1, 0) : Coord) ∈ m :=
    inm (w - 1, 0) (by show w - 1 < w; omega) (by show 0 < 2; omega)
      (fun e => by rw [← e] at hx1; exact absurd hx1 (by show ¬ w - 1 + 1 < w; omega))
      (fun e => by
        rw [← e] at hcol
        exact absurd hx1 (by show ¬ s.1 + 1 < w; rw [hcol]; show ¬ w - 1 + 1 < w; omega))
  obtain ⟨c, hc, hcx⟩ := chain_proj_intermediate Prod.fst
    (fun u v huv => by unfold Adjacent at huv; omega) m hchm (0, 0) ha0 (w - 1, 0) hb0 s.1
    (by show 0 ≤ s.1; omega) (by show s.1 ≤ w - 1; omega)
  have hcb := hin c (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hc))))
  unfold InBounds at hcb
  have hcx' : c.1 = s.1 := hcx
  rcases (by omega : c.2 = s.2 ∨ c.2 = t.2) with h1 | h1
  · have hcs : c = s := by
      ext
      · exact hcx'
      · exact h1
    rw [hcs] at hc
    exact hsm hc
  · have hct : c = t := by
      ext
      · rw [hcx', hcol]
      · exact h1
    rw [hct] at hc
    exact htm hc
end GridHam
