-- Prove2me | solution 1 for Kyprianou.Ch05.gridAverageSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:50:39.638846+00:00
-- url     : https://prove2.me/submissions/7c7967d2-8127-4275-ba44-7510d6315600

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_nonnegativeHalfOpenGridPartition
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Absolute integrability supplies a summable majorant for the cell averages. -/
theorem solution (h : Real → Real) (hi : Integrable h)
    (d : Real) (hd : 0 < d) :
    let c := fun k : Nat =>
      (∫ z in Set.Ico ((k : Real)*d) (((k : Real)+1)*d), h z ∂volume)/d
    Summable (fun k => |c k|) ∧
      (∑' k : Nat, c k)*d = (∫ y in Set.Ici 0, h y ∂volume) := by
  let S := fun k : Nat => Ico ((k : Real)*d) (((k : Real)+1)*d)
  obtain ⟨hU,hD⟩ := nonnegativeHalfOpenGridPartition d hd
  have hM : ∀ k : Nat, MeasurableSet (S k) := fun k => measurableSet_Ico
  have hsum := hasSum_integral_iUnion hM
    hD (hi.norm.integrableOn (s := ⋃ k, S k))
  have hs : Summable (fun k : Nat => ∫ z in S k, ‖h z‖ ∂volume) := hsum.summable
  have ha : Summable (fun k : Nat => |∫ z in S k, h z ∂volume|) := by
    apply hs.of_nonneg_of_le (fun k => abs_nonneg _)
    intro k
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := h) (μ := volume.restrict (S k)))
  change Summable (fun k : Nat => |(∫ z in S k, h z ∂volume)/d|) ∧ _
  constructor
  · simpa only [abs_div, abs_of_pos hd] using ha.div_const d
  · have hI := integral_iUnion hM hD (hi.integrableOn (s := ⋃ k, S k))
    rw [show (⋃ k, S k) = Ici 0 from hU] at hI
    change (∑' k : Nat, (∫ z in S k, h z ∂volume)/d)*d = _
    rw [tsum_div_const, div_mul_cancel₀ _ hd.ne']
    exact hI.symm
