-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyInfiniteCountTopV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:15:34.01464+00:00
-- url     : https://prove2.me/submissions/dfd6753d-c746-4945-9cac-07c8e05bd1af

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Theorems.Thm_ProbabilityTheory_map_prmPartialCount
import Theorems.Thm_Kyprianou_Ch02_pointFamilyPartialRatesAtTopV1
import Theorems.Thm_Kyprianou_Ch02_pointFamilyPrmPartialCountLeV1
import Theorems.Thm_Kyprianou_Ch02_poissonMeasureIicTendstoZeroV1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

private theorem poissonFinitePrefixLawForcesInfiniteLocal
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

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ A : Set E, MeasurableSet A → m A = ⊤ →
       ∀ᵐ ω ∂P, ProbabilityTheory.poissonRandomMeasure K Y ω A = ⊤ := by
  classical
  intro A hA hInf
  let C : ℕ → Ω → ℕ := fun n => ProbabilityTheory.prmPartialCount K Y A n
  let rate : ℕ → NNReal := fun n =>
    ∑ k ∈ Finset.range (n + 1), (m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal
  have hC : ∀ n, Measurable (C n) := by
    intro n
    change Measurable (fun ω =>
      ∑ k ∈ Finset.range (n + 1), ProbabilityTheory.thinnedCount K Y A k ω)
    exact Finset.measurable_sum _ fun k _ =>
      ProbabilityTheory.measurable_thinnedCount
        (hd.measurable_count k) (hd.measurable_point k) hA
  have hlaw : ∀ n, P.map (C n) = poissonMeasure (rate n) := by
    intro n
    exact ProbabilityTheory.map_prmPartialCount hd hA n
  have hdom : ∀ n ω,
      (C n ω : ENNReal) ≤ ProbabilityTheory.poissonRandomMeasure K Y ω A := by
    intro n ω
    exact Kyprianou.Ch02.pointFamilyPrmPartialCountLeV1 K Y A hA n ω
  have hrate : Tendsto rate atTop atTop :=
    Kyprianou.Ch02.pointFamilyPartialRatesAtTopV1 m A hA hInf
  exact poissonFinitePrefixLawForcesInfiniteLocal
    P (fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A)
    C rate hC hlaw hdom hrate
