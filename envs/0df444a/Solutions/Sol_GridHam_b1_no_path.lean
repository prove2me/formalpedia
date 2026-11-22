-- Prove2me | solution 1 for GridHam.b1_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:04.364042+00:00
-- url     : https://prove2.me/submissions/24c18abf-b43d-4ccb-b1c9-365587cf03f7

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_b0_no_path
public import Theorems.Thm_GridHam_contract_prefix
public import Theorems.Thm_GridHam_c2_prefix

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 0) v := by
  rintro ⟨p, hvp⟩
  obtain ⟨R, hR⟩ := c2_prefix w v p (by omega) hvp
  rw [hR] at hvp
  have hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx : ∀ c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have hq := contract_prefix w (1, 0) v (2, 1) [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] R
    hM hMx rfl hvp
  exact b0_no_path (w - 2) (shiftL2 v) (by unfold shiftL2; dsimp only; omega) ⟨_, hq⟩
end GridHam
