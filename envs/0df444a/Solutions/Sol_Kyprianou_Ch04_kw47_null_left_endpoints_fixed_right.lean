-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_null_left_endpoints_fixed_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:19:56.836524+00:00
-- url     : https://prove2.me/submissions/46ee9bf4-74bf-4217-bf00-2ccd0728f29f

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (mu : Measure Real) [NullSingletonClass mu] (q : Real) :
    mu {x : Real | x < q ∧ mu (Ioc x q) = 0} = 0 := by 
  let A : Set Real := {x | x < q ∧ mu (Ioc x q) = 0}
  let B : A → Set Real := fun x => Ioo x.1 q
  obtain ⟨T, hT, hEq⟩ := TopologicalSpace.isOpen_iUnion_countable B
    (fun _ => isOpen_Ioo)
  let C : Set Real := ⋃ x ∈ T, B x
  have hC : mu C = 0 := (measure_biUnion_null_iff hT).2
    (fun x _ => measure_mono_null Ioo_subset_Ioc_self x.2.2)
  have hSub : (A \ C).Subsingleton := by
    intro x hx y hy
    have aux (a b : Real) (ha : a ∈ A \ C) (hb : b ∈ A \ C)
        (hab : a < b) : False := by
      apply hb.2
      change b ∈ ⋃ x ∈ T, B x
      rw [hEq]
      exact mem_iUnion.mpr ⟨⟨a, ha.1⟩, hab, hb.1.1⟩
    exact le_antisymm (le_of_not_gt (aux y x hy hx)) (le_of_not_gt (aux x y hx hy))
  apply measure_mono_null (t := C ∪ (A \ C)) _ (measure_union_null hC
    (hSub.countable.measure_zero mu))
  intro x hx
  by_cases h : x ∈ C
  · exact Or.inl h
  · exact Or.inr ⟨hx, h⟩
