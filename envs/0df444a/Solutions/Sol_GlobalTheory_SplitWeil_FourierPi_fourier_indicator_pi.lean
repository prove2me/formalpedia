-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:05.731442+00:00
-- url     : https://prove2.me/submissions/0867e480-1810-41dc-a5c2-d22a629bebd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) (s : kˣ)
    (x : n → k) :
    ∫ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) ∂μ =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x := by
  haveI := secondCountable k
  by_cases hx : x ∈ box n s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) =
        (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ box n (c * s⁻¹)
      · have h1 : y ⬝ᵥ x ∈ cball c := by
          show valuation k (∑ i, y i * x i) ≤ valuation k (c : k)
          refine Valuation.map_sum_le (valuation k) fun i _ => ?_
          have h2 : valuation k (y i * x i) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' (hy i trivial) (hx i trivial)
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero_pi μ h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ box n (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
        (show y + t ∈ box n (c * s⁻¹) from fun i _ => add_mem_cball (hy i trivial) (ht i trivial))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy fun i _ => by simpa using add_mem_cball (h1 i trivial) (neg_mem_cball (ht i trivial))
end GlobalTheory.SplitWeil.FourierPi
