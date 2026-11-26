-- Prove2me | solution 1 for Kyprianou.Ch05.smithIIDRealisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:07:34.022541+00:00
-- url     : https://prove2.me/submissions/d99c0160-de50-4f01-b09d-1c0df6dd93a9

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

/-- Every probability law on the nonnegative half-line of positive mean has an i.i.d. realisation with pointwise nonnegative coordinates and the given marginal laws. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hs : F (Set.Iio (0 : Real)) = 0)
    (hp : 0 < ∫ x : Real, x ∂F) :
    ∃ (P : Measure (Nat → Real)) (X : Nat → (Nat → Real) → Real),
      IsProbabilityMeasure P ∧ IsRenewalProcess P X ∧
      (∀ n, Measure.map (X n) P = F) := by
  let P : Measure (Nat → Real) := Measure.infinitePi (fun _ : Nat => F)
  let X : Nat → (Nat → Real) → Real := fun i w => max 0 (w i)
  have hP : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI := hP
  have hm (i : Nat) : Measurable (X i) := measurable_const.max (measurable_pi_apply i)
  have hmap (i : Nat) : Measure.map (fun w : Nat → Real => w i) P = F := by
    exact (measurePreserving_eval_infinitePi (fun _ : Nat => F) i).map_eq
  have hnonneg : ∀ᵐ x ∂F, 0 ≤ x := by
    rw [ae_iff]
    have he : {x : Real | ¬ 0 ≤ x} = Set.Iio 0 := by
      ext x
      simp [not_le]
    rw [he]
    exact hs
  have hc : Measure.map (fun x : Real => max 0 x) F = F := by
    calc
      _ = Measure.map id F := by
        apply Measure.map_congr
        filter_upwards [hnonneg] with x hx
        simp [max_eq_right hx]
      _ = F := Measure.map_id
  have hl (i : Nat) : Measure.map (X i) P = F := by
    calc
      _ = Measure.map (fun x : Real => max 0 x)
          (Measure.map (fun w : Nat → Real => w i) P) := by
        exact (Measure.map_map (g := fun x : Real => max 0 x)
          (f := fun w : Nat → Real => w i)
          (measurable_const.max measurable_id) (measurable_pi_apply i)).symm
      _ = F := by rw [hmap i, hc]
  refine ⟨P, X, hP, ⟨hm, ?_, ?_, ?_, ?_⟩, hl⟩
  · change iIndepFun (fun i (w : Nat → Real) => max 0 (w i))
      (Measure.infinitePi (fun _ : Nat => F))
    apply iIndepFun_infinitePi
    intro i
    exact measurable_const.max measurable_id
  · intro i
    exact ⟨(hm i).aemeasurable, (hm 0).aemeasurable, (hl i).trans (hl 0).symm⟩
  · intro i w
    exact le_max_left _ _
  · have he : P {w | X 0 w = 0} = F {0} := by
      rw [← hl 0, Measure.map_apply (hm 0) (measurableSet_singleton 0)]
      rfl
    rw [he]
    have hle : F {0} ≤ 1 := by
      calc
        F {0} ≤ F Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    refine lt_of_le_of_ne hle ?_
    intro hz
    have hae : ∀ᵐ x ∂F, x = 0 :=
      (mem_ae_iff_prob_eq_one (measurableSet_singleton 0)).mpr hz
    have hzero : (∫ x : Real, x ∂F) = 0 := by
      rw [integral_congr_ae hae]
      simp
    exact (ne_of_gt hp) hzero
