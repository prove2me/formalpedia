-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_null_right_local_intervals
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:09:28.664438+00:00
-- url     : https://prove2.me/submissions/d05e238a-e77f-4388-9afd-515675a9517e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_null_left_endpoints_fixed_right
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (mu : Measure Real) [NullSingletonClass mu] :
    mu {x : Real | ∃ y : Real, x < y ∧ mu (Ioc x y) = 0} = 0 := by 
  let A : Rat → Set Real := fun q =>
    {x | x < (q : Real) ∧ mu (Ioc x (q : Real)) = 0}
  have hA (q : Rat) : mu (A q) = 0 :=
    Kyprianou.Ch04.kw47_null_left_endpoints_fixed_right mu q
  apply measure_mono_null (t := ⋃ q : Rat, A q)
  · rintro x ⟨y, hxy, hzero⟩
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
    refine mem_iUnion.mpr ⟨q, ?_⟩
    change x < (q : Real) ∧ mu (Ioc x (q : Real)) = 0
    refine ⟨hxq, measure_mono_null ?_ hzero⟩
    intro z hz
    exact ⟨hz.1, hz.2.trans hqy.le⟩
  · exact le_antisymm ((measure_iUnion_le A).trans (by simp [hA])) bot_le
