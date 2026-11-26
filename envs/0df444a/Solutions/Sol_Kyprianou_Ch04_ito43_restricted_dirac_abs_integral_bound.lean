-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_restricted_dirac_abs_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:33:28.697009+00:00
-- url     : https://prove2.me/submissions/47463523-643f-4b7c-b512-c5291e363ebe

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Absolute finite-sum bounds give integrability and an integral bound on a countable restricted atomic measure. -/
theorem solution {I : Type} [Countable I] (φ : I → ℝ × ℝ)
    (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hfin : ∀ S : Finset I, (∑ s ∈ S, |B.indicator F (φ s)|) ≤ C) :
    IntegrableOn F B (Measure.sum fun s : I => Measure.dirac (φ s)) ∧
      |∫ z in B, F z ∂(Measure.sum fun s : I => Measure.dirac (φ s))| ≤ C := by
  classical
  let G : I → ℝ := fun s => B.indicator F (φ s)
  have hG : Summable (fun s => |G s|) := summable_of_sum_le (fun _ => abs_nonneg _) hfin
  constructor
  · let c : I → ENNReal := fun s => if φ s ∈ B then 1 else 0
    rw [IntegrableOn,Measure.restrict_sum _ hB]
    have he : (Measure.sum fun s : I => (Measure.dirac (φ s)).restrict B) =
        Measure.sum (fun s : I => c s • Measure.dirac (φ s)) := by
      congr 1
      funext s
      rw [restrict_dirac]
      by_cases h : φ s ∈ B <;> simp [c,h]
    rw [he]
    apply integrable_sum_dirac (fun s => by by_cases h : φ s ∈ B <;> simp [c,h])
    apply hG.congr
    intro s
    by_cases h : φ s ∈ B <;> simp [G,Set.indicator_apply,c,h,Real.norm_eq_abs]
  · rw [bvRestrictedDiracIntegralV1 φ B hB F]
    have hGn : Summable (fun s : I => ‖G s‖) := by simpa only [Real.norm_eq_abs] using hG
    have H := norm_tsum_le_tsum_norm hGn
    rw [Real.norm_eq_abs] at H
    simp only [Real.norm_eq_abs] at H
    exact H.trans (hG.tsum_le_of_sum_le hfin)
