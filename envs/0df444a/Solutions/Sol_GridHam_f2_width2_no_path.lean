-- Prove2me | solution 1 for GridHam.f2_width2_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:43.458938+00:00
-- url     : https://prove2.me/submissions/283b9326-85eb-4f7d-a7e5-b7078e76b856

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
theorem _root_.solution (h : ℕ) (s t : Coord) (hsb : s.1 < 2 ∧ s.2 < h)
    (htb : t.1 < 2 ∧ t.2 < h) (hrow : s.2 = t.2) (hy0 : 0 < s.2) (hy1 : s.2 + 1 < h) :
    ¬ HasHamPath 2 h s t := by
  rintro ⟨p, hv⟩
  obtain ⟨m, hpm⟩ := path_split_ends hv (by omega)
  obtain ⟨_, _, _, hnd, hin, hcov, hch⟩ := hv
  rw [hpm] at hnd hin hcov hch
  obtain ⟨hsn, hndr⟩ := List.nodup_cons.mp hnd
  have hchm : chainAdjacent m = true := chainAdjacent_prefix m [t] (chainAdjacent_tail s _ hch)
  have htm : t ∉ m := nodup_not_mem_last m t hndr
  have hsm : s ∉ m := fun hm => hsn (List.mem_append.mpr (Or.inl hm))
  have hst : s.1 ≠ t.1 := by
    intro e
    apply hsn
    have hst' : s = t := by
      ext
      · exact e
      · exact hrow
    rw [hst']
    simp
  have inm : ∀ v : Coord, v.1 < 2 → v.2 < h → v ≠ s → v ≠ t → v ∈ m := by
    intro v hvx hvy hvs hvt
    have hv := hcov v ((mem_allCoords 2 h v).mpr ⟨hvx, hvy⟩)
    rcases List.mem_cons.mp hv with e | e
    · exact absurd e hvs
    · rcases List.mem_append.mp e with e2 | e2
      · exact e2
      · exact absurd (List.mem_singleton.mp e2) hvt
  have ha0 : ((0, 0) : Coord) ∈ m :=
    inm (0, 0) (by show 0 < 2; omega) (by show 0 < h; omega)
      (fun e => by rw [← e] at hy0; exact absurd hy0 (by show ¬ 0 < 0; omega))
      (fun e => by rw [← e] at hrow; exact absurd hy0 (by show ¬ 0 < s.2; rw [hrow]; omega))
  have hb0 : ((0, h - 1) : Coord) ∈ m :=
    inm (0, h - 1) (by show 0 < 2; omega) (by show h - 1 < h; omega)
      (fun e => by rw [← e] at hy1; exact absurd hy1 (by show ¬ h - 1 + 1 < h; omega))
      (fun e => by
        rw [← e] at hrow
        exact absurd hy1 (by show ¬ s.2 + 1 < h; rw [hrow]; show ¬ h - 1 + 1 < h; omega))
  obtain ⟨c, hc, hcy⟩ := chain_proj_intermediate Prod.snd
    (fun u v huv => by unfold Adjacent at huv; omega) m hchm (0, 0) ha0 (0, h - 1) hb0 s.2
    (by show 0 ≤ s.2; omega) (by show s.2 ≤ h - 1; omega)
  have hcb := hin c (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hc))))
  unfold InBounds at hcb
  have hcy' : c.2 = s.2 := hcy
  rcases (by omega : c.1 = s.1 ∨ c.1 = t.1) with h1 | h1
  · have hcs : c = s := by
      ext
      · exact h1
      · exact hcy'
    rw [hcs] at hc
    exact hsm hc
  · have hct : c = t := by
      ext
      · exact h1
      · rw [hcy', hrow]
    rw [hct] at hc
    exact htm hc
end GridHam
