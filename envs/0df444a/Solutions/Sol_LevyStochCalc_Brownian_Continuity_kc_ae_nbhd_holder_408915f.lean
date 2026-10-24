-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:41:35.511057+00:00
-- url     : https://prove2.me/submissions/bfc72691-16e3-463a-87bf-52a19b9945a4

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
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_interval_holder_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- Every integer is a dyadic rational (`n = 0`). -/
lemma LevyStochCalc.Brownian.Continuity.intCast_mem_dyadicRationals (k : ℤ) : (k : ℝ) ∈ dyadicRationals := by
  refine ⟨k, 0, ?_⟩
  simp
end
end
end
end

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
/-- **Neighbourhood Hölder.** For a.e. path, every point `t` has an open
neighbourhood on whose dyadics `X(·)ω` is α-Hölder. At a point near an integer
`c`, pairs straddling `c` are handled by chaining through `c` (`X c` is defined
since `c` is dyadic), using the two adjacent unit-interval bounds. This is the
hypothesis of `exists_tendsto_of_local_holder`. -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals,
      ∀ s' ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by
  filter_upwards [LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_408915f P X hX hα0 hαpq] with ω hIH
  intro t
  set c : ℤ := ⌊t + 1 / 2⌋ with hc
  obtain ⟨KL, NL, hKL0, hHL⟩ := hIH (c - 1)
  obtain ⟨K₀, N₀, hK₀0, hH₀⟩ := hIH c
  have hcdy : (c : ℝ) ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals := LevyStochCalc.Brownian.Continuity.intCast_mem_dyadicRationals c
  -- `t` lies within `1/2` of `c`.
  have htlo : (c : ℝ) - 1 / 2 ≤ t := by
    have := Int.floor_le (t + 1 / 2); linarith
  have hthi : t < (c : ℝ) + 1 / 2 := by
    have := Int.lt_floor_add_one (t + 1 / 2); linarith
  refine ⟨2 * (KL + K₀),
    min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2), ?_, by positivity, ?_⟩
  · have : (0 : ℝ) < min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) := by positivity
    exact lt_min (by positivity) (by norm_num)
  · set ρ := min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2) with hρ
    have hρ12 : ρ ≤ 1 / 2 := min_le_right _ _
    have hrhoNL : 2 * ρ ≤ (1 / 2 : ℝ) ^ NL := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ NL := min_le_left _ _
      linarith
    have hρN₀ : 2 * ρ ≤ (1 / 2 : ℝ) ^ N₀ := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ N₀ := min_le_right _ _
      linarith
    -- ordered-pair core
    have key : ∀ a b, a ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals → b ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals →
        (c : ℝ) - 1 < a → a ≤ b → b < (c : ℝ) + 1 → |a - b| ≤ 2 * ρ →
        |X a ω - X b ω| ≤ 2 * (KL + K₀) * |a - b| ^ α := by
      intro a b ha hb halo hab bhi habs
      have habsL : |a - b| ≤ (1 / 2 : ℝ) ^ NL := le_trans habs hrhoNL
      have habs₀ : |a - b| ≤ (1 / 2 : ℝ) ^ N₀ := le_trans habs hρN₀
      rcases le_or_gt b (c : ℝ) with hbc | hbc
      · -- both in [c-1, c]
        have h := hHL a ha b hb (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) habsL
        have : KL ≤ 2 * (KL + K₀) := by nlinarith
        calc |X a ω - X b ω| ≤ KL * |a - b| ^ α := h
          _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
      · rcases le_or_gt (c : ℝ) a with hca | hca
        · -- both in [c, c+1]
          have h := hH₀ a ha b hb (by linarith) (by linarith)
            (by linarith) (by linarith) habs₀
          have : K₀ ≤ 2 * (KL + K₀) := by nlinarith
          calc |X a ω - X b ω| ≤ K₀ * |a - b| ^ α := h
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                apply mul_le_mul_of_nonneg_right this (by positivity)
        · -- straddle: a < c < b, chain through c
          have hac_le : |a - (c : ℝ)| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have hcb_le : |(c : ℝ) - b| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have h1 := hHL a ha (c : ℝ) hcdy (by push_cast; linarith) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) (le_trans hac_le habsL)
          have h2 := hH₀ (c : ℝ) hcdy b hb (by linarith) (by linarith)
            (by linarith) (by linarith) (le_trans hcb_le habs₀)
          have hacα : |a - (c : ℝ)| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hac_le hα0.le
          have hcbα : |(c : ℝ) - b| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hcb_le hα0.le
          calc |X a ω - X b ω|
              ≤ |X a ω - X (c : ℝ) ω| + |X (c : ℝ) ω - X b ω| := abs_sub_le _ _ _
            _ ≤ KL * |a - (c : ℝ)| ^ α + K₀ * |(c : ℝ) - b| ^ α := by gcongr
            _ ≤ KL * |a - b| ^ α + K₀ * |a - b| ^ α := by gcongr
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                nlinarith [Real.rpow_nonneg (abs_nonneg (a - b)) α]
    intro s hs s' hs' hsb hs'b
    have hsbnd : (c : ℝ) - 1 < s ∧ s < (c : ℝ) + 1 :=
      ⟨by have := hsb.1; linarith, by have := hsb.2; linarith⟩
    have hs'bnd : (c : ℝ) - 1 < s' ∧ s' < (c : ℝ) + 1 :=
      ⟨by have := hs'b.1; linarith, by have := hs'b.2; linarith⟩
    have hdist : |s - s'| ≤ 2 * ρ := by
      rw [abs_le]; constructor
      · have := hsb.1; have := hs'b.2; linarith
      · have := hsb.2; have := hs'b.1; linarith
    rcases le_total s s' with hss | hss
    · exact key s s' hs hs' hsbnd.1 hss hs'bnd.2 hdist
    · rw [abs_sub_comm, abs_sub_comm s s']
      exact key s' s hs' hs hs'bnd.1 hss hsbnd.2 (by rw [abs_sub_comm] at hdist; exact hdist)
