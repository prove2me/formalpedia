-- Prove2me | solution 1 for Kyprianou.Ch05.smithBlackwellIndicatorVolume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:58:15.864683+00:00
-- url     : https://prove2.me/submissions/bd4b88b9-bed1-4816-beee-353db9782ee8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Integrating the indicator of [0,y) on the positive half-line gives its length y. -/
theorem solution
    (y : Real) (hy : 0 < y) :
    (∫ v in Set.Ioi 0, (Set.Ico 0 y).indicator (fun _ : Real => (1 : Real)) v) = y := by
  rw [integral_indicator_const 1 measurableSet_Ico, Measure.real_def,
    Measure.restrict_apply measurableSet_Ico]
  have hs : Set.Ico (0 : Real) y ∩ Set.Ioi 0 = Set.Ioo 0 y := by
    ext v
    simp only [mem_inter_iff, mem_Ico, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨⟨_, hvy⟩, hv⟩
      exact ⟨hv, hvy⟩
    · rintro ⟨hv, hvy⟩
      exact ⟨⟨hv.le, hvy⟩, hv⟩
  rw [hs, Real.volume_Ioo]
  simp [ENNReal.toReal_ofReal hy.le]
