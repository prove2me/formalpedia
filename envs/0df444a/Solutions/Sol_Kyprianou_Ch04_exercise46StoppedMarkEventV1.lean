-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46StoppedMarkEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:39:18.536858+00:00
-- url     : https://prove2.me/submissions/9a2389c0-1620-4c70-bd16-53c56ab16d16

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46BoundedStoppedMarkV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (C : Set Real) (hC : MeasurableSet C) (T : NNReal) :
    let J : Omega → Real := fun w =>
      -(L.X ((A w).untopD 0) w - Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0))
    MeasurableSet[G.rightCont T] (J ⁻¹' C ∩ {w | A w ≤ (T : WithTop NNReal)}) := by
  dsimp only
  let a : Omega → NNReal := fun w => (min (A w) (T : WithTop NNReal)).untopD 0
  have hfin (w : Omega) : min (A w) (T : WithTop NNReal) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top T))
  have haeq (w : Omega) : (a w : WithTop NNReal) = min (A w) (T : WithTop NNReal) := by
    exact WithTop.coe_untop₀_of_ne_top (by simpa using hfin w)
  have ha : IsStoppingTime G.rightCont (fun w => (a w : WithTop NNReal)) := by
    rw [funext haeq]
    exact hA.min_const T
  have hT (w : Omega) : a w ≤ T := WithTop.coe_le_coe.mp
    ((haeq w).le.trans (min_le_right _ _))
  have hm := Kyprianou.Ch04.exercise46BoundedStoppedMarkV1 P G L a ha T hT
  let Jc : Omega → Real := fun w =>
    -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))
  have he : (fun w => -(L.X ((A w).untopD 0) w -
      Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0))) ⁻¹' C ∩
      {w | A w ≤ (T : WithTop NNReal)} =
      Jc ⁻¹' C ∩ {w | A w ≤ (T : WithTop NNReal)} := by
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, and_congr_left_iff]
    intro hw
    have heq : a w = (A w).untopD 0 := by
      change (min (A w) (T : WithTop NNReal)).untopD 0 = (A w).untopD 0
      rw [min_eq_left hw]
    change -(L.X ((A w).untopD 0) w -
      Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0)) ∈ C ↔
      -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w)) ∈ C
    rw [heq]
  rw [he]
  exact (hm hC).inter (hA T)
