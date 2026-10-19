-- Prove2me | solution 1 for KramersWannier.kw_not_invertible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:53:54.580677+00:00
-- url     : https://prove2.me/submissions/c2be6383-4393-4c00-bbc7-db17211a5c62

import Definitions.Def_KramersWannier_defs

open Matrix KramersWannier

theorem solution (L : ℕ) [NeZero L] :
    ¬ IsUnit (kwD L) ∧ ∃ v : Config L → ℂ, v ≠ 0 ∧ kwD L *ᵥ v = 0 := by
  have h01 : (0 : Config L) ≠ 1 := by
    intro h
    have := congrFun h (0 : Fin L)
    exact zero_ne_one this
  let v : Config L → ℂ := Pi.single 0 1 - Pi.single 1 1
  have hv : v ≠ 0 := by
    intro h
    have he := congrFun h (0 : Config L)
    simp [v, h01] at he
  have hker : kwD L *ᵥ v = 0 := by
    ext t
    simp only [v, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.sub_apply,
      Matrix.col_apply, Pi.zero_apply]
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    simp [kwD, h]
  refine ⟨?_, v, hv, hker⟩
  intro hu
  apply hv
  exact Matrix.mulVec_injective_of_isUnit hu (hker.trans (Matrix.mulVec_zero _).symm)
