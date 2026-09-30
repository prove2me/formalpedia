-- Prove2me | solution 1 for Grunbaum2003.characteristicCone_of_bounded_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:53:57.17398+00:00
-- url     : https://prove2.me/submissions/83f2a387-19dd-48f8-bab6-f875b5b8ff40

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
open Grunbaum2003
open scoped Pointwise

theorem solution {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hb : Bornology.IsBounded K) :
    characteristicCone K = {0} := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨R,hR,hbound⟩ := hb.exists_pos_norm_le
  ext v
  constructor
  · intro hv
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hne
    let t : ℝ := (R+‖x‖+1)/‖v‖
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hmem := hv x hx t ht
    have hnorm : ‖t • v‖ ≤ R+‖x‖ := by
      calc
        ‖t • v‖ = ‖(x+t•v)-x‖ := by congr 1; abel
        _ ≤ ‖x+t•v‖+‖x‖ := norm_sub_le _ _
        _ ≤ R+‖x‖ := add_le_add_left (hbound _ hmem) _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at hnorm
    have he : t*‖v‖=R+‖x‖+1 := div_mul_cancel₀ _ (ne_of_gt hn)
    linarith
  · rintro rfl x hx t ht
    simpa using hx
