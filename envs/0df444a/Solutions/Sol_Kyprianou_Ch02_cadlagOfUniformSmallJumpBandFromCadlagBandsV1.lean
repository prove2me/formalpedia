-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagOfUniformSmallJumpBandFromCadlagBandsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:05:12.883137+00:00
-- url     : https://prove2.me/submissions/fc6c703c-0e81-40b3-a820-b35b6900e68d

import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealOfLocalUniformLimitsV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hband : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
        (fun (t : ℝ≥0) => compensatedSmallJumpBand P levyMeasure N ε t ω))
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)) :
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω)
              (nhdsWithin t (Set.Iio t)) (nhds l))
    := by
  classical
  have hchoice (k : ℕ) :
      ∃ ε : ℕ → ℝ,
        (∀ n, 0 < ε n ∧ ε n < 1) ∧
        (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ∀ t : ℝ≥0, t ≤ (k + 1 : ℝ≥0) →
              |compensatedSmallJumpBand P levyMeasure N (ε n) t ω - M t ω| < δ) := by
    obtain ⟨ε, _, hε, _, hu⟩ := huniform (k + 1) (by positivity)
    exact ⟨ε, hε, hu⟩
  choose ε hε hu using hchoice
  have hcad (k : ℕ) :
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        ProbabilityTheory.IsCadlag
          (fun (t : ℝ≥0) =>
            compensatedSmallJumpBand P levyMeasure N (ε k n) t ω) := by
    exact ae_all_iff.mpr (fun n =>
      hband (ε k n) (hε k n).1 (hε k n).2)
  have hgood (k : ℕ) :
      ∀ᵐ ω ∂P,
        (∀ n : ℕ, ProbabilityTheory.IsCadlag
          (fun (t : ℝ≥0) =>
            compensatedSmallJumpBand P levyMeasure N (ε k n) t ω)) ∧
        (∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ∀ t : ℝ≥0, t ≤ (k + 1 : ℝ≥0) →
              |compensatedSmallJumpBand P levyMeasure N (ε k n) t ω - M t ω| < δ) := by
    filter_upwards [hcad k, hu k] with ω hw hconv
    exact ⟨hw, hconv⟩
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ,
      (∀ n : ℕ, ProbabilityTheory.IsCadlag
        (fun (t : ℝ≥0) =>
          compensatedSmallJumpBand P levyMeasure N (ε k n) t ω)) ∧
      (∀ δ : ℝ, 0 < δ →
        ∃ n₀ : ℕ, ∀ n ≥ n₀,
          ∀ t : ℝ≥0, t ≤ (k + 1 : ℝ≥0) →
            |compensatedSmallJumpBand P levyMeasure N (ε k n) t ω - M t ω| < δ) :=
    ae_all_iff.mpr hgood
  filter_upwards [hall] with ω hw
  have happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - M t ω| < δ := by
    intro T _
    obtain ⟨k, hk⟩ := exists_nat_gt T
    have hTk : T ≤ (k + 1 : ℝ≥0) := by
      exact le_trans hk.le (by exact_mod_cast Nat.le_succ k)
    refine ⟨(fun n t => compensatedSmallJumpBand P levyMeasure N (ε k n) t ω),
      (hw k).1, ?_⟩
    intro δ hδ
    obtain ⟨n₀, hn⟩ := (hw k).2 δ hδ
    exact ⟨n₀, fun n hn0 t ht => hn n hn0 t (ht.trans hTk)⟩
  have hpath := Kyprianou.Ch02.cadlagNNRealOfLocalUniformLimitsV1
    (fun t => M t ω) happrox
  exact ⟨fun t => (hpath t).1, fun t _ => (hpath t).2⟩

