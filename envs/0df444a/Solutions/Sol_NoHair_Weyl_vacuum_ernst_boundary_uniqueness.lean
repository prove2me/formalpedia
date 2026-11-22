-- Prove2me | solution 1 for NoHair.Weyl.vacuum_ernst_boundary_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:02:34.416836+00:00
-- url     : https://prove2.me/submissions/a4332eae-117f-4d97-ac64-45f4dfd7ba2b

import Theorems.Thm_NoHair_Weyl_ernst_deviation_subharmonic
import Theorems.Thm_NoHair_Weyl_maximum_principle_off_axis
import Mathlib.Tactic.Positivity

open NoHair.Weyl

theorem solution (u v : ErnstPotentials)
    (hu : u.IsSolution) (hv : v.IsSolution) (hb : HasComparisonBounds u v) :
    u = v := by
  obtain ⟨hreg, hsub⟩ := ernst_deviation_subharmonic u v hu hv
  have hle := maximum_principle_off_axis (deviation u v) hreg hsub hb.1 hb.2
  have equal_components (p : OrbitPoint) :
      u.normSq p = v.normSq p ∧ u.twist p = v.twist p := by
    have hpos := mul_pos (hu.2.2 p).1 (hv.2.2 p).1
    have hnum := (div_le_iff₀ hpos).mp (hle p)
    rw [zero_mul] at hnum
    have hz := le_antisymm hnum (add_nonneg (sq_nonneg _) (sq_nonneg _))
    obtain ⟨hX, hY⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hz
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hX), sub_eq_zero.mp (sq_eq_zero_iff.mp hY)⟩
  have hX := funext fun p => (equal_components p).1
  have hY := funext fun p => (equal_components p).2
  cases u
  cases v
  congr 1
