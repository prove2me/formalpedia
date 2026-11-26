-- Prove2me | solution 1 for Kyprianou.Ch04.closedStopKernelRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:26:47.294464+00:00
-- url     : https://prove2.me/submissions/de1f2a49-41d3-49be-803e-d264185b2bc2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_stoppingTimeMinMeasurable
import Theorems.Thm_Kyprianou_Ch04_closedStopMaskLeftLimit
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- The closed stopping mask preserves joint, adapted and past-horizon measurability
as well as common-null left continuity of a signed marked kernel. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w)))
    (hPast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    let H := fun s x w => if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0
    Measurable (fun z : (ℝ × ℝ) × Omega => H z.1.1 z.1.2 z.2) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => H (t : ℝ) z.2 z.1)) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => H s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (H (t : ℝ) x w))) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then H z.2.1 z.2.2 z.1 else 0)) := by
  classical
  let H := fun s x w => if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0
  have htm : Measurable tau := by
    apply measurable_of_Iic
    intro a
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe r => exact F.le r _ (htau r)
  refine ⟨?_,?_,?_,?_⟩
  · exact Measurable.ite
      (measurableSet_le (continuous_real_toNNReal.measurable.comp measurable_fst.fst).withTop_coe
        (htm.comp measurable_snd)) hm measurable_const
  · intro t
    have hmin := stoppingTimeMinMeasurable F tau htau t
    have hset : MeasurableSet[(F t).prod inferInstance]
        {z : Omega × ℝ | (t : WithTop NNReal) ≤ min (tau z.1) (t : WithTop NNReal)} :=
      measurableSet_le measurable_const (hmin.comp measurable_fst)
    have hh : Measurable[(F t).prod inferInstance] (fun z : Omega × ℝ =>
        if (t : WithTop NNReal) ≤ min (tau z.1) (t : WithTop NNReal)
        then k (t : ℝ) z.2 z.1 else 0) :=
      Measurable.ite hset (ha t) measurable_const
    change Measurable[(F t).prod inferInstance] (fun z : Omega × ℝ => H (t : ℝ) z.2 z.1)
    convert hh using 1
    ext z
    simp only [H, Real.toNNReal_coe, le_min_iff, le_refl, and_true]
  · filter_upwards [hc] with w hw
    intro x t ht
    simpa only [H,Real.toNNReal_coe] using closedStopMaskLeftLimit (fun s => k s x w)
      (tau w) t ht (hw x t ht)
  · intro t
    have hmin := stoppingTimeMinMeasurable F tau htau t
    have hset : MeasurableSet[(F t).prod inferInstance] {z : Omega × (ℝ × ℝ) |
        (z.2.1.toNNReal : WithTop NNReal) ≤ min (tau z.1) (t : WithTop NNReal)} :=
      measurableSet_le (continuous_real_toNNReal.measurable.comp measurable_snd.fst).withTop_coe
        (hmin.comp measurable_fst)
    have hh : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
        if (z.2.1.toNNReal : WithTop NNReal) ≤ min (tau z.1) (t : WithTop NNReal)
        then (if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)
        else 0) := Measurable.ite hset (hPast t) measurable_const
    change Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) => if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ)
        then H z.2.1 z.2.2 z.1 else 0)
    convert hh using 1
    ext z
    by_cases hz : z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ)
    · have hzt : (z.2.1.toNNReal : WithTop NNReal) ≤ (t : WithTop NNReal) :=
        WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hz.2)
      simp only [H,if_pos hz,le_min_iff,hzt,and_true]
    · by_cases h : (z.2.1.toNNReal : WithTop NNReal) ≤ min (tau z.1) (t : WithTop NNReal)
      · simp only [if_neg hz,if_pos h]
      · simp only [if_neg hz,if_neg h]
