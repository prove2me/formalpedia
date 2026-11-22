-- Prove2me | solution 1 for GridHam.b0_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:12:02.297724+00:00
-- url     : https://prove2.me/submissions/92d89229-ee63-4cc3-bdce-1cac6040a704

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_unique_right
public import Theorems.Thm_GridHam_forced_after_head
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_P2M_GridHam_mem_of_getLast__beac85f634f6


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (v : Coord) (hv : 1 ≤ v.1) : ¬ HasHamPath w 3 (0, 1) v := by
  rintro ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩
  have hvin := hin v (mem_of_getLast? p v hlast)
  unfold InBounds at hvin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnothead : ∀ c : Coord, c ≠ (0, 1) → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    exact hc (Option.some.inj e).symm
  have hnotlast : ∀ c : Coord, c.1 = 0 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have h00 : PNext p (0, 1) (0, 0) := by
    apply forced_after_head (z := (1, 0)) hnd hch hhead
      (hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega))
      (hnothead (0, 0) (by simp)) (hnotlast (0, 0) rfl)
    intro y _ hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hy
    dsimp only at hy
    simp only [Prod.mk.injEq]
    omega
  have h02 : PNext p (0, 1) (0, 2) := by
    apply forced_after_head (z := (1, 2)) hnd hch hhead
      (hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega))
      (hnothead (0, 2) (by simp)) (hnotlast (0, 2) rfl)
    intro y hyp hy
    have hyb := hin y hyp
    unfold InBounds at hyb
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hy
    dsimp only at hy hyb
    simp only [Prod.mk.injEq]
    omega
  have := pnext_unique_right hnd h00 h02
  simp at this
end GridHam
