-- Prove2me | solution 1 for GlobalTheory.sum_intervalIntegral_le_of_spaced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:15.220793+00:00
-- url     : https://prove2.me/submissions/fa69356c-ed55-400f-bf78-e26051a8cc02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by
  have hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v) := fun u v =>
    (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]
  rw [Finset.sum_congr rfl fun x _ =>
    intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]
  rw [← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ))
    (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]
  · apply setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)
    apply HasSubset.Subset.eventuallyLE
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩
  · intro x hx z hz hxz
    have := h3 x hx z hz hxz
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    have : |p x - p z| < δ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith
end GlobalTheory
