-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCrossingCountableMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:05:21.534184+00:00
-- url     : https://prove2.me/submissions/56a0d10c-efaa-49f5-9fcf-5613927128d9

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_renewalEpochMonotoneAEV1
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellIffIndexV1
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (hx : 0 < x)
    (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) :
    P {w : Omega | 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B} = ∑' n : Nat, P ((fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) n) := by
  let C : ℕ → Set Omega := fun n => {w | renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧ x-renewalEpoch Z n w ∈ B}
  let G : Set Omega := {w | Monotone (fun n => renewalEpoch Z n w)}
  have hGae : ∀ᵐ w ∂P, w ∈ G := renewalEpochMonotoneAEV1 P Z F hRenewal
  have hm (n : ℕ) : Measurable (renewalEpoch Z n) := by
    unfold renewalEpoch
    exact Finset.measurable_sum _ fun i _ => hRenewal.1 i
  have hG : MeasurableSet G := by
    have he : G = ⋂ n : ℕ, {w | renewalEpoch Z n w ≤ renewalEpoch Z (n+1) w} := by
      ext w
      simp only [G,mem_setOf_eq,mem_iInter]
      exact ⟨fun h n => h (Nat.le_succ n),monotone_nat_of_le_succ⟩
    rw [he]
    exact MeasurableSet.iInter fun n => measurableSet_le (hm n) (hm (n+1))
  have hC (n : ℕ) : MeasurableSet (C n) :=
    (hm n measurableSet_Icc).inter
      (((hRenewal.1 n).sub (measurable_const.sub (hm n)) hA).inter
        ((measurable_const.sub (hm n)) hB))
  have hD : Pairwise (Function.onFun Disjoint (fun n => C n ∩ G)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro w hi hj
    have h1 := (renewalCrossingCellIffIndexV1 Z w hi.2 x hx A B hA2 i).1 hi.1
    have h2 := (renewalCrossingCellIffIndexV1 Z w hj.2 x hx A B hA2 j).1 hj.1
    exact hij (by omega)
  calc
    _ = P (⋃ n : ℕ, C n ∩ G) := by
      apply measure_congr
      filter_upwards [hGae] with w hw
      change (0 < renewalOvershoot Z x w ∧ renewalOvershoot Z x w ∈ A ∧
        renewalUndershoot Z x w ∈ B) = (w ∈ ⋃ n : ℕ, C n ∩ G)
      apply propext
      constructor
      · intro hh
        have hn : nextRenewalIndex Z x w ≠ 0 := by
          intro he
          have hp := hh.1
          simp [renewalOvershoot,he,renewalEpoch] at hp
          linarith
        obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact mem_iUnion.mpr ⟨n,(renewalCrossingCellIffIndexV1 Z w hw x hx A B hA2 n).2
          ⟨hn,hh⟩,hw⟩
      · intro hh
        obtain ⟨n,hn⟩ := mem_iUnion.mp hh
        exact ((renewalCrossingCellIffIndexV1 Z w hw x hx A B hA2 n).1 hn.1).2
    _ = ∑' n : ℕ, P (C n ∩ G) := measure_iUnion hD (fun n => (hC n).inter hG)
    _ = _ := by
      congr 1
      funext n
      apply measure_congr
      filter_upwards [hGae] with w hw
      change (w ∈ C n ∩ G) = (w ∈ C n)
      simp only [mem_inter_iff,hw,and_true]
