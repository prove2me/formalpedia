-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_finite_grid_rare_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:49:58.881181+00:00
-- url     : https://prove2.me/submissions/2ff7e23d-efe3-4e8a-91d9-099746e90352

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.Positivity
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → ℕ → Set Ω) (cnt : ℕ → ℕ) (b : ℕ → ℝ)
    (hlim : Tendsto (fun n => (cnt n : ℝ) * b n) atTop (𝓝 0))
    (hE : ∀ n k, P (E n k) ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ ω ∂P, ∀ M : ℕ, ¬ (∀ᶠ n in atTop, ∃ k < M * cnt n, ω ∈ E n k) := by
  let A (M n : ℕ) : Set Ω := ⋃ k ∈ Finset.range (M * cnt n), E n k
  have hA (M n : ℕ) : P (A M n) ≤ ENNReal.ofReal ((M : ℝ) * ((cnt n : ℝ) * b n)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc
      (∑ k ∈ Finset.range (M * cnt n), P (E n k)) ≤
          ∑ _k ∈ Finset.range (M * cnt n), ENNReal.ofReal (b n) :=
        Finset.sum_le_sum (fun k _ => hE n k)
      _ = ENNReal.ofReal ((M : ℝ) * ((cnt n : ℝ) * b n)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Nat.cast_mul, mul_assoc]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (M : ℝ) * (cnt n : ℝ)), mul_assoc]
  refine ae_all_iff.2 fun M => ?_
  have hbound : Tendsto (fun n => ENNReal.ofReal ((M : ℝ) * ((cnt n : ℝ) * b n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto ((M : ℝ) * 0)).comp (hlim.const_mul (M : ℝ))
  have hnull (N : ℕ) : P {ω | ∀ n ≥ N, ω ∈ A M n} = 0 := by
    apply nonpos_iff_eq_zero.mp
    apply ge_of_tendsto hbound
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (measure_mono (by intro ω hω; exact hω n hn)).trans (hA M n)
  have hae : ∀ᵐ ω ∂P, ∀ N : ℕ, ¬ (∀ n ≥ N, ω ∈ A M n) := by
    refine ae_all_iff.2 fun N => ae_iff.2 ?_
    simpa only [not_not] using hnull N
  filter_upwards [hae] with ω hω h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  apply hω N
  intro n hn
  obtain ⟨k, hk, he⟩ := hN n hn
  exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨Finset.mem_range.2 hk, he⟩⟩
