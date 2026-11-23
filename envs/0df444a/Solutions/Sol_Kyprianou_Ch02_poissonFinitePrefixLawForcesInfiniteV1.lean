-- Prove2me | solution 1 for Kyprianou.Ch02.poissonFinitePrefixLawForcesInfiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:17:57.993064+00:00
-- url     : https://prove2.me/submissions/ffdc1d76-5866-4bd3-8e05-9d98c38d71a7

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_poissonMeasureIicTendstoZeroV1
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ENNReal)
    (C : ℕ → Ω → ℕ) (rate : ℕ → NNReal)
    (hC : ∀ n, Measurable (C n))
    (hlaw : ∀ n, P.map (C n) = ProbabilityTheory.poissonMeasure (rate n))
    (hdom : ∀ n ω, (C n ω : ENNReal) ≤ f ω)
    (hrate : Tendsto rate atTop atTop) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by
  classical
  have hzero (N : ℕ) :
      P {ω | f ω < (N : ENNReal)} = 0 := by
    have hsub (n : ℕ) :
        {ω | f ω < (N : ENNReal)} ⊆
          (C n) ⁻¹' (Set.Iic N) := by
      intro ω hω
      have hc : (C n ω : ENNReal) ≤ (N : ENNReal) :=
        le_trans (hdom n ω) hω.le
      exact_mod_cast hc
    have hmeasure (n : ℕ) :
        P {ω | f ω < (N : ENNReal)} ≤
          ProbabilityTheory.poissonMeasure (rate n) (Set.Iic N) := by
      calc
        P {ω | f ω < (N : ENNReal)} ≤
            P ((C n) ⁻¹' (Set.Iic N)) := measure_mono (hsub n)
        _ = (P.map (C n)) (Set.Iic N) := by
          rw [Measure.map_apply (hC n) measurableSet_Iic]
        _ = ProbabilityTheory.poissonMeasure (rate n) (Set.Iic N) := by
          rw [hlaw n]
    have ht : Tendsto
        (fun n : ℕ => ProbabilityTheory.poissonMeasure (rate n) (Set.Iic N))
        atTop (𝓝 (0 : ENNReal)) :=
      (Kyprianou.Ch02.poissonMeasureIicTendstoZeroV1 N).comp hrate
    exact le_antisymm (ge_of_tendsto' ht hmeasure) bot_le
  have hnon (N : ℕ) : ∀ᵐ ω ∂P, ¬ f ω < (N : ENNReal) := by
    apply ae_iff.mpr
    simpa only [not_not] using hzero N
  filter_upwards [ae_all_iff.mpr hnon] with ω hw
  by_contra hf
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hf
  exact hw N hN
