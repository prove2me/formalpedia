-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GapNonzeroV14
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:04.985667+00:00
-- url     : https://prove2.me/submissions/11d834a4-7c2e-471c-a689-aa93e2cc161c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41CompactNonzeroV12
import Theorems.Thm_Kyprianou_Ch04_exercise41LocalNonzeroV12
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (a b : NNReal) (ha : 0 < a)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hgap : ∀ u ∈ Icc a b, x u ≠ 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Icc a b, e ≤ |x u| := by
  apply exercise41CompactNonzeroV12 x a b
  intro s hs
  have hp : 0 < s := ha.trans_le hs.1
  obtain ⟨l,hl⟩ := hL s hp
  have hne : l ≠ 0 := by
    intro h
    letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hp⟩
    exact hgap s hs (hNoJump s hp ((leftLim_eq_of_tendsto hl).trans h))
  exact exercise41LocalNonzeroV12 x s l (hgap s hs) hne (hR s) hl
