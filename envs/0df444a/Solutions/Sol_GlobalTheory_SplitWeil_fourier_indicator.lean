-- Prove2me | solution 1 for GlobalTheory.SplitWeil.fourier_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:04.212391+00:00
-- url     : https://prove2.me/submissions/c8e31d5c-3497-436a-bcc9-f8f9d902f8bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ c) (s : kˣ) (x : k) :
    ∫ y, (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y * x) : ℂ) ∂ν =
      (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ)) x := by
  by_cases hx : x ∈ cball s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y * x) : ℂ) =
        (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ cball (c * s⁻¹)
      · have h1 : y * x ∈ cball c := by
          have h2 : valuation k (y * x) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' hy hx
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_cball _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero ν h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ cball (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (add_mem_cball hy ht)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy (by simpa using add_mem_cball h1 (neg_mem_cball ht))
end GlobalTheory.SplitWeil
