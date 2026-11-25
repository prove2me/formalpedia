-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:35:53.037448+00:00
-- url     : https://prove2.me/submissions/7aee84cd-706e-49a0-8e7f-354f86aab00e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_meas
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_measure
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_disj
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_union

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution (G : Type) [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H}) (h1 : ν (H : Set G) = 1)
    (hc : Countable (G ⧸ H)) (f : G → ℂ) (fbar : G ⧸ H → ℂ)
    (hf : ∀ g : G, f g = fbar (g : G ⧸ H)) :
    (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧
      ((Summable fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c) := by
  have hmeas : Measurable f := by
    intro s _
    have hs : f ⁻¹' s = ⋃ c ∈ fbar ⁻¹' s, fib H c := by
      ext x
      simp [fib, hf]
    rw [hs]
    exact MeasurableSet.biUnion (to_countable _) fun c _ => fib_meas H hm c
  have hlin : ∫⁻ g, ‖f g‖ₑ ∂ν = ∑' c, ‖fbar c‖ₑ := by
    rw [← setLIntegral_univ, ← fib_union H, lintegral_iUnion (fib_meas H hm) (fib_disj H)]
    refine tsum_congr fun c => ?_
    rw [setLIntegral_congr_fun (fib_meas H hm c) (g := fun _ => ‖fbar c‖ₑ), setLIntegral_const,
      fib_measure ν H h1 c, mul_one]
    intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]
  have hiff : (Integrable f ν ↔ Summable fun c => ‖fbar c‖) := by
    rw [Integrable, hasFiniteIntegral_iff_enorm, hlin]
    simp only [hmeas.aestronglyMeasurable, true_and]
    rw [lt_top_iff_ne_top]
    simp only [← ofReal_norm]
    constructor
    · intro h
      have h' : (∑' c, ((‖fbar c‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
        simpa [ofReal_norm, enorm_eq_nnnorm] using h
      have := ENNReal.tsum_coe_ne_top_iff_summable.mp h'
      exact NNReal.summable_coe.mpr this |>.congr fun c => by simp
    · intro h
      have h' : Summable fun c => ‖fbar c‖₊ := NNReal.summable_coe.mp (by simpa using h)
      simpa [ofReal_norm, enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr h'
  refine ⟨hiff, fun hs => ?_⟩
  have hint : Integrable f ν := hiff.mpr hs
  rw [← setIntegral_univ, ← fib_union H, integral_iUnion (fib_meas H hm) (fib_disj H) hint.integrableOn]
  refine tsum_congr fun c => ?_
  rw [setIntegral_congr_fun (fib_meas H hm c) (g := fun _ => fbar c), setIntegral_const]
  · simp [Measure.real, fib_measure ν H h1 c]
  · intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]
end GlobalTheory.CompanionTheory.CosetSum
