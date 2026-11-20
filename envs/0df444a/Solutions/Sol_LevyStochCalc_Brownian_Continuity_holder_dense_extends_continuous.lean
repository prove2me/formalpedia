-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.holder_dense_extends_continuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:40:05.793753+00:00
-- url     : https://prove2.me/submissions/931b33fa-95ee-4a76-9797-958e6254926d

import Definitions.Def_LevyStochCalc_Brownian_Construction_F000
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity


theorem _root_.solution {α K δ₀ : ℝ}
    (hα : 0 < α) (_hK : 0 < K) (hδ₀ : 0 < δ₀)
    (D : Set ℝ) (h_dense : Dense D)
    (f : ℝ → ℝ)
    (h_holder_dyadic : ∀ s ∈ D, ∀ t ∈ D, |s - t| ≤ δ₀ →
      |f s - f t| ≤ K * |s - t| ^ α) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ s ∈ D, g s = f s := by
  have h_e : IsUniformInducing (Subtype.val : D → ℝ) := isUniformEmbedding_subtype_val.isUniformInducing
  have h_d : DenseRange (Subtype.val : D → ℝ) := h_dense.denseRange_val
  have h_f : UniformContinuous (fun x : D => f x) := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    set c := ε / (K + 1) with hc
    have hcpos : 0 < c := div_pos hε (by linarith)
    refine ⟨min δ₀ (c ^ (1 / α)), lt_min hδ₀ (by positivity), ?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rw [Subtype.dist_eq, Real.dist_eq] at hab
    rw [Real.dist_eq]
    have h1 : |a - b| ≤ δ₀ := (lt_of_lt_of_le hab (min_le_left _ _)).le
    have h2 : |a - b| ≤ c ^ (1 / α) := (lt_of_lt_of_le hab (min_le_right _ _)).le
    have hpow : |a - b| ^ α ≤ c := by
      calc |a - b| ^ α ≤ (c ^ (1 / α)) ^ α := Real.rpow_le_rpow (abs_nonneg _) h2 hα.le
        _ = c := by rw [← Real.rpow_mul hcpos.le, one_div_mul_cancel hα.ne', Real.rpow_one]
    calc |f a - f b| ≤ K * |a - b| ^ α := h_holder_dyadic a ha b hb h1
      _ ≤ K * c := mul_le_mul_of_nonneg_left hpow _hK.le
      _ < ε := by
        rw [hc, mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  refine ⟨_, (uniformContinuous_uniformly_extend h_e h_d h_f).continuous, fun s hs => ?_⟩
  exact uniformly_extend_of_ind h_e h_d h_f ⟨s, hs⟩

end LevyStochCalc.Brownian.Continuity
