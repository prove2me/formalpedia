-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.exists_tendsto_of_local_holder_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:35:40.808496+00:00
-- url     : https://prove2.me/submissions/e7972405-d105-4b09-96e0-56f6d2b734e5

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- **Limit existence from local Hölder.** If `f` is α-Hölder on `A ∩ (t−ρ, t+ρ)`
for some `ρ > 0`, `K ≥ 0`, then `f` has a limit along `𝓝[A] t` (`A` dense). The
limit-along-dyadics is what `extendFrom` needs to build the continuous path. -/
lemma solution {A : Set ℝ} (hA : Dense A) {f : ℝ → ℝ}
    {α : ℝ} (hα : 0 < α) (t : ℝ)
    (hloc : ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ A, ∀ s' ∈ A,
      s ∈ Set.Ioo (t - ρ) (t + ρ) → s' ∈ Set.Ioo (t - ρ) (t + ρ) →
        |f s - f s'| ≤ K * |s - s'| ^ α) :
    ∃ y, Filter.Tendsto f (𝓝[A] t) (nhds y) := by
  obtain ⟨K, ρ, hρ, hK, hHol⟩ := hloc
  have hFne : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hA t)
  have hcauchy : Cauchy (Filter.map f (𝓝[A] t)) := by
    rw [Metric.cauchy_iff]
    refine ⟨hFne.map _, fun ε hε => ?_⟩
    -- choose `ρ' ≤ ρ` with `K·(2ρ')^α < ε`
    obtain ⟨ρ', hρ'0, hρ'ρ, hρ'b⟩ :
        ∃ ρ', 0 < ρ' ∧ ρ' ≤ ρ ∧ K * (2 * ρ') ^ α < ε := by
      have hδ : 0 < (ε / (K + 1)) ^ (1 / α) :=
        Real.rpow_pos_of_pos (by positivity) _
      refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α) / 3), lt_min hρ (by positivity),
        min_le_left _ _, ?_⟩
      have h2 : 2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3) < (ε / (K + 1)) ^ (1 / α) := by
        have := min_le_right ρ ((ε / (K + 1)) ^ (1 / α) / 3)
        linarith
      have hpow : (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α < ε / (K + 1) := by
        have h1 := Real.rpow_lt_rpow (by positivity) h2 hα
        rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
          rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (K + 1)), one_div,
              inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]] at h1
      calc K * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α
          ≤ (K + 1) * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ < (K + 1) * (ε / (K + 1)) := by
            apply mul_lt_mul_of_pos_left hpow (by positivity)
        _ = ε := by field_simp
    refine ⟨f '' (A ∩ Set.Ioo (t - ρ') (t + ρ')), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset ?_ (Set.subset_preimage_image f _)
      exact inter_mem_nhdsWithin A
        (Ioo_mem_nhds (by linarith) (by linarith))
    · rintro x ⟨s, ⟨hsA, hsI⟩, rfl⟩ y ⟨s', ⟨hs'A, hs'I⟩, rfl⟩
      have hIs : s ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hsI.1; linarith, by have := hsI.2; linarith⟩
      have hIs' : s' ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hs'I.1; linarith, by have := hs'I.2; linarith⟩
      have hb := hHol s hsA s' hs'A hIs hIs'
      have hss' : |s - s'| ≤ 2 * ρ' := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 := hsI.1; have h2 := hs'I.2; linarith
        · have h1 := hsI.2; have h2 := hs'I.1; linarith
      rw [Real.dist_eq]
      calc |f s - f s'| ≤ K * |s - s'| ^ α := hb
        _ ≤ K * (2 * ρ') ^ α := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact Real.rpow_le_rpow (abs_nonneg _) hss' hα.le
        _ < ε := hρ'b
  obtain ⟨y, hy⟩ := CompleteSpace.complete hcauchy
  exact ⟨y, hy⟩
