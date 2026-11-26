-- Prove2me | solution 1 for Kyprianou.Ch04.pathRunningInfimumLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:15:57.944846+00:00
-- url     : https://prove2.me/submissions/a8efe780-6796-4499-b2cd-3b82d7fa6ca5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_runningInfimumAntitoneFromFiniteBounds
open Set Filter
open scoped NNReal Topology
set_option autoImplicit false

/-- Increasing horizons exhaust the all-time infimum of a lower-bounded path. -/
theorem solution (x : NNReal → ℝ) (hbd : BddBelow (range x)) :
    Tendsto (fun t : NNReal => sInf (x '' Iic t)) atTop (nhds (sInf (range x))) := by
  let f : NNReal → ℝ := fun t => sInf (x '' Iic t)
  have hbt (t : NNReal) : BddBelow (x '' Iic t) :=
    hbd.mono (image_subset_range _ _)
  have ha := Kyprianou.Ch04.runningInfimumAntitoneFromFiniteBounds x hbt
  have hlo (t : NNReal) : sInf (range x) ≤ f t := by
    apply le_csInf (show (x '' Iic t).Nonempty from ⟨x 0,0,by simp,rfl⟩)
    rintro y ⟨u,hu,rfl⟩
    exact csInf_le hbd ⟨u,rfl⟩
  have hb : BddBelow (range f) := ⟨sInf (range x), by rintro y ⟨t,rfl⟩; exact hlo t⟩
  have he : (⨅ t, f t) = sInf (range x) := by
    apply le_antisymm
    · apply le_csInf (range_nonempty x)
      rintro y ⟨t,rfl⟩
      exact (ciInf_le hb t).trans (csInf_le (hbt t) ⟨t,by simp,rfl⟩)
    · exact le_ciInf hlo
  rw [← he]
  exact tendsto_atTop_ciInf ha hb
