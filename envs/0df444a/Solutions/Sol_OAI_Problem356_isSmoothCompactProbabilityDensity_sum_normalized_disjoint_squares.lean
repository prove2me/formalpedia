-- Prove2me | solution 1 for OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:24:59.211299+00:00
-- url     : https://prove2.me/submissions/ec40888c-90f3-48d3-b8ba-d1c9ddec94a6

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators
theorem pb_sqrt_sum {ι X : Type*} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases hx : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hgi⟩ := hx
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hne
      exact Set.disjoint_left.mp (hd j hj i hi hji) (Function.mem_support.mpr hne) (Function.mem_support.mpr hgi)
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring),
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring)]
    rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
  · push Not at hx
    rw [Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring),
      Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring)]
    simp

theorem pb_hcs_sum {ι X : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℝ)
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  have hK : IsCompact (⋃ i ∈ s, tsupport (f i)) := s.isCompact_biUnion (fun i hi => h i hi)
  have hKc : IsClosed (⋃ i ∈ s, tsupport (f i)) :=
    s.finite_toSet.isClosed_biUnion (fun i _ => isClosed_tsupport _)
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (closure_minimal ?_ hKc)
  intro x hx
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact Set.mem_biUnion hi (subset_tsupport _ hne)

theorem pb_main {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  refine ⟨fun x => Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)), ?_, ?_, ?_, ?_, hmass⟩
  · exact ContDiff.sum (fun i hi => contDiff_const.mul ((hsm i hi).pow 2))
  · refine pb_hcs_sum s _ (fun i hi => (hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring
  · have e : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) = fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x :=
      funext (pb_sqrt_sum s a g ha hg hd)
    rw [e]
    exact ContDiff.sum (fun i hi => contDiff_const.mul (hsm i hi))
  · have e : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) = fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x :=
      funext (pb_sqrt_sum s a g ha hg hd)
    rw [e]
    refine pb_hcs_sum s _ (fun i hi => (hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring

theorem solution
    {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  apply pb_main s a g ha hg hsm hcs hd
  have hint : ∀ i ∈ s, Integrable (fun x : E3 => a i * g i x ^ 2) volume := by
    intro i hi
    have hc : Continuous (fun x : E3 => a i * g i x ^ 2) := by
      have := (hsm i hi).continuous
      fun_prop
    refine hc.integrable_of_hasCompactSupport ((hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring
  rw [integral_finsetSum s hint]
  rw [← haint]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [integral_const_mul, hgint i hi, mul_one]

