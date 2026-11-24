-- Prove2me | solution 1 for GlobalTheory.JR.FourUnit.integral_indicator_char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:40.423826+00:00
-- url     : https://prove2.me/submissions/3d8c4485-51e1-4348-8e52-8ec12dc5cb22

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.FourUnit
namespace GlobalTheory.JR.FourUnit
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (S : Set G) (φ : G → ℂ)
    (hφ : ∀ a b, φ (a + b) = φ a * φ b) (t : G) (hS : ∀ z, t + z ∈ S ↔ z ∈ S) (ht : φ t ≠ 1) :
    ∫ z, S.indicator φ z ∂μ = 0 := by
  have key : ∀ z, S.indicator φ (t + z) = φ t * S.indicator φ z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem ((hS z).2 hz), Set.indicator_of_mem hz, hφ]
    · rw [Set.indicator_of_notMem (fun h => hz ((hS z).1 h)), Set.indicator_of_notMem hz, mul_zero]
  have h := integral_add_left_eq_self (μ := μ) (S.indicator φ) t
  simp_rw [key, integral_const_mul] at h
  have h2 : (φ t - 1) * ∫ z, S.indicator φ z ∂μ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) ht
  · exact h3
end GlobalTheory.JR.FourUnit
