-- Prove2me | solution 1 for GridHam.g3_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:23.827036+00:00
-- url     : https://prove2.me/submissions/15ccf8eb-d83e-46e1-998b-f29a7ae0cf88

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_GridHam_hasHamPath_reverse
public import Theorems.Thm_GridHam_obs_no_path


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (m sx sy tx ty : ℕ) (hs : sx < m ∧ sy < 3) (ht : tx < m ∧ ty < 3)
    (hg : G3 m sx tx sy ((sx + sy) % 2) ((tx + ty) % 2)) :
    ¬ HasHamPath m 3 (sx, sy) (tx, ty) := by
  intro hp
  unfold G3 at hg
  by_cases hlt : tx < sx
  · exact obs_no_path tx m (tx, ty) (sx, sy) (Nat.le_refl _)
      (by show (tx + ty) % 2 = 1; omega) (by show ty < 3; omega) (by show tx < sx; omega)
      (by show ty = 1 ∨ tx + 1 < sx; omega) (hasHamPath_reverse hp)
  · exact obs_no_path sx m (sx, sy) (tx, ty) (Nat.le_refl _)
      (by show (sx + sy) % 2 = 1; omega) (by show sy < 3; omega) (by show sx < tx; omega)
      (by show sy = 1 ∨ sx + 1 < tx; omega) hp
end GridHam
