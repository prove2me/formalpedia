-- Prove2me | solution 1 for Kyprianou.Ch05.boundedFunctionDRIFromOscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:59:03.815456+00:00
-- url     : https://prove2.me/submissions/5a0b5383-e545-4579-9feb-69a281da6ab2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Integrable bounded function with uniformly summable grid oscillations is DRI. -/
theorem solution
    (h : Real → Real) (hi : Integrable h)
    (hn : ∀ t, 0 ≤ h t) (hb : ∀ t, h t ≤ 1)
    (ho : ∀ d : Real, 0 < d →
      Summable (fun k : Int => riCellOscillation h d k) ∧
      (∑' k : Int, riCellOscillation h d k) ≤ 2) :
    DirectlyRiemannIntegrable h := by
  refine ⟨hi, ?_, ?_⟩
  · intro a b hab
    exact ⟨⟨1, by rintro _ ⟨t,ht,rfl⟩; exact hb t⟩,
      ⟨0, by rintro _ ⟨t,ht,rfl⟩; exact hn t⟩⟩
  · intro eps heps
    refine ⟨eps/3, by positivity, ?_⟩
    intro d hd hde
    obtain ⟨hs,hbnd⟩ := ho d hd
    refine ⟨hs.mul_left d, ?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hbnd hd.le).trans_lt (by linarith)
