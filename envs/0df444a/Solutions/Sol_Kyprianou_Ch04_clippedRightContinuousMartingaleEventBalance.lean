-- Prove2me | solution 1 for Kyprianou.Ch04.clippedRightContinuousMartingaleEventBalance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:03:16.37079+00:00
-- url     : https://prove2.me/submissions/d13a4791-a4d9-430c-b026-cc44d251e3d5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_eventBeforeClippedStopMeasurable
import Theorems.Thm_Kyprianou_Ch04_boundedRightContinuousStopSetIntegral
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A bounded-horizon stopped right-continuous martingale has zero event increments. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J : NNReal → Omega → ℝ) (hM : Martingale J F.rightCont P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Set.Ici t) t)
    (tau : Omega → WithTop NNReal) (ht : IsStoppingTime F.rightCont tau) :
    let C := fun (t : NNReal) w => J ((min (tau w) (t : WithTop NNReal)).untopD t) w
    (∀ t, Integrable (C t) P) ∧
      ∀ s t, s ≤ t → ∀ A : Set Omega, MeasurableSet[F.rightCont s] A →
        (∫ w in A, C s w ∂P) = ∫ w in A, C t w ∂P := by
  let c := fun (t : NNReal) w => (min (tau w) (t : WithTop NNReal)).untopD t
  have hco (t : NNReal) (w : Omega) : (c t w : WithTop NNReal) = min (tau w) (t : WithTop NNReal) :=
    clippedClockCoe (tau w) t
  have hc (t : NNReal) : IsStoppingTime F.rightCont (fun w => (c t w : WithTop NNReal)) := by
    simpa only [hco] using ht.min_const t
  have hle (t : NNReal) (w : Omega) : c t w ≤ t :=
    WithTop.coe_le_coe.mp ((hco t w).trans_le (min_le_right _ _))
  refine ⟨?_,?_⟩
  · intro t
    obtain ⟨n,hn⟩ := exists_nat_ge t
    exact (boundedRightContinuousStopSetIntegral P F J hM hr n (c t) (hc t)
      (fun w => (hle t w).trans hn)).1
  · intro s t hst A hA
    obtain ⟨n,hn⟩ := exists_nat_ge t
    have hS := boundedRightContinuousStopSetIntegral P F J hM hr n (c s) (hc s)
      (fun w => (hle s w).trans (hst.trans hn))
    have hT := boundedRightContinuousStopSetIntegral P F J hM hr n (c t) (hc t)
      (fun w => (hle t w).trans hn)
    let B := A ∩ {w | tau w ≤ (s : WithTop NNReal)}ᶜ
    have hBm : MeasurableSet[F.rightCont s] B := hA.inter (ht s).compl
    have hBS : MeasurableSet[(hc s).measurableSpace] B := by
      rw [(hc s).measurableSet]
      have hh := eventBeforeClippedStopMeasurable F.rightCont tau ht s A hA
      rw [(ht.min_const s).measurableSet] at hh
      simpa only [hco] using hh
    have hCT : (fun w => (c s w : WithTop NNReal)) ≤ fun w => (c t w : WithTop NNReal) := by
      intro w
      change (c s w : WithTop NNReal) ≤ (c t w : WithTop NNReal)
      rw [hco,hco]
      exact min_le_min_left _ (WithTop.coe_le_coe.mpr hst)
    have hBT := (hc s).measurableSpace_mono (hc t) hCT B hBS
    have hEqB := (hS.2 B hBS).trans (hT.2 B hBT).symm
    have hEqEarly : Set.EqOn (fun w => J (c s w) w) (fun w => J (c t w) w)
        (A ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
      intro w hw
      have hh : c s w = c t w := WithTop.coe_injective (by
        rw [hco,hco,min_eq_left hw.2,min_eq_left
          (hw.2.trans (WithTop.coe_le_coe.mpr hst))])
      change J (c s w) w = J (c t w) w
      rw [hh]
    let D := {w | tau w ≤ (s : WithTop NNReal)}
    have hD : MeasurableSet D := F.rightCont.le s D (ht s)
    have hAm : MeasurableSet A := F.rightCont.le s A hA
    have hE := setIntegral_congr_fun (μ := P) (hAm.inter hD) hEqEarly
    change (∫ w in A, J (c s w) w ∂P) = ∫ w in A, J (c t w) w ∂P
    have hdis : Disjoint (A ∩ D) B := by
      exact Set.disjoint_left.mpr (fun w hw hb => hb.2 hw.2)
    have hAB : (A ∩ D) ∪ B = A := by ext w; simp [B,D]
    rw [← hAB,setIntegral_union hdis (F.rightCont.le s B hBm)
      hS.1.integrableOn hS.1.integrableOn,
      setIntegral_union hdis (F.rightCont.le s B hBm) hT.1.integrableOn hT.1.integrableOn,
      hE,hEqB]
