-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorIncrementCoreV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:24:14.621266+00:00
-- url     : https://prove2.me/submissions/97edd429-9ad6-4f37-84bb-eba345455ef7

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t →
      f t - f s ≤ d * ((t : Real) - (s : Real))) :
    let R : NNReal → Real := fun t => max w (sSup (f '' Iic t))
    R 0 = w ∧
    (∀ t, f t ≤ R t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real)))) := by
  intro R
  have hB (t : NNReal) : BddAbove (f '' Iic t) := by
    refine ⟨d * (t : Real), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h := hf 0 u zero_le
    have hu' : (u : Real) ≤ (t : Real) := hu
    simp only [hf0, NNReal.coe_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hu' hd.le)
  have hN (t : NNReal) : (f '' Iic t).Nonempty := ⟨f t, t, mem_Iic.mpr le_rfl, rfl⟩
  have hDom (t : NNReal) : f t ≤ R t :=
    (le_csSup (hB t) ⟨t, mem_Iic.mpr le_rfl, rfl⟩).trans (le_max_right _ _)
  have hMono : Monotone R := by
    intro s t hst
    apply max_le_max_left
    apply csSup_le (hN s)
    rintro _ ⟨u, hu, rfl⟩
    exact le_csSup (hB t) ⟨u, mem_Iic.mpr (le_trans (mem_Iic.mp hu) hst), rfl⟩
  have hz : R 0 = w := by
    have hS : f '' Iic (0 : NNReal) = {0} := by
      ext z
      simp [hf0, eq_comm]
    simp [R, hS, hw]
  refine ⟨hz, hDom, ?_⟩
  intro s t hst
  let a := max 0 (f s - R s + d * ((t : Real) - (s : Real)))
  have ha : 0 ≤ a := le_max_left _ _
  refine ⟨sub_nonneg.mpr (hMono hst), ?_⟩
  change R t - R s ≤ a
  have hRs : w ≤ R s := le_max_left _ _
  have ht : R t ≤ R s + a := by
    apply max_le (by linarith only [hRs,ha])
    apply csSup_le (hN t)
    rintro _ ⟨u, hu, rfl⟩
    by_cases hus : u ≤ s
    · exact ((le_csSup (hB s) ⟨u, mem_Iic.mpr hus, rfl⟩).trans
        (le_max_right w _)).trans (by linarith only [ha])
    · have h := hf s u (le_of_not_ge hus)
      have hu' : (u : Real) ≤ (t : Real) := hu
      have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hu' (s : Real)) hd.le
      have hb : f s - R s + d * ((t : Real) - (s : Real)) ≤ a := le_max_right _ _
      linarith only [h,hmul,hb]
  linarith only [ht]
