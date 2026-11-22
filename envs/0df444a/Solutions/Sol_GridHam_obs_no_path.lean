-- Prove2me | solution 1 for GridHam.obs_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:51:36.770537+00:00
-- url     : https://prove2.me/submissions/514246c4-aba3-4dab-983e-66c6ed1b9ed3

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_b0_no_path
public import Theorems.Thm_GridHam_b1_no_path
public import Theorems.Thm_P2M_GridHam_b1_no_path__4d6679970d5b
public import Theorems.Thm_GridHam_c1_contract

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (k : ℕ) : ∀ (w : ℕ) (u v : Coord), u.1 ≤ k → (u.1 + u.2) % 2 = 1 →
    u.2 < 3 → u.1 < v.1 → (u.2 = 1 ∨ u.1 + 1 < v.1) → ¬ HasHamPath w 3 u v := by
  induction k with
  | zero =>
    intro w u v hk hc hu3 hlt hcond h
    obtain ⟨u1, u2⟩ := u
    dsimp only at hk hc hu3 hlt hcond
    have e1 : u1 = 0 := by omega
    have e2 : u2 = 1 := by omega
    subst e1
    subst e2
    exact b0_no_path w v (by omega) h
  | succ k ih =>
    intro w u v hk hc hu3 hlt hcond h
    by_cases hk' : u.1 ≤ k
    · exact ih w u v hk' hc hu3 hlt hcond h
    · obtain ⟨u1, u2⟩ := u
      dsimp only at hk hc hu3 hlt hcond hk'
      by_cases h1 : u1 = 1
      · subst h1
        have hv3 : 3 ≤ v.1 := by omega
        rcases (by omega : u2 = 0 ∨ u2 = 2) with e | e
        · subst e
          exact b1_no_path w v hv3 h
        · subst e
          exact b1_no_path' w v hv3 h
      · have hu2 : 2 ≤ u1 := by omega
        have hc1 := c1_contract w (u1, u2) v hu2 (by omega) h
        exact ih (w - 2) (shiftL2 (u1, u2)) (shiftL2 v)
          (by unfold shiftL2; dsimp only; omega) (by unfold shiftL2; dsimp only; omega)
          (by unfold shiftL2; dsimp only; omega) (by unfold shiftL2; dsimp only; omega)
          (by unfold shiftL2; dsimp only; omega) hc1
end GridHam
