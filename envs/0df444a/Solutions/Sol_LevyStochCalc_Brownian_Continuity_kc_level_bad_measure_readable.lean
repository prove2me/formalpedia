-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:14.019865+00:00
-- url     : https://prove2.me/submissions/210e29f7-44c5-42fe-b9f5-4fb6f007d7f3

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_exponent_identity_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_markov_bound_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Real-threshold form of the tail bound: for `lam > 0`,
`P {ω | lam < |X s ω − X t ω|} ≤ M · edist s t ^ q / (ofReal lam) ^ p`. -/
lemma LevyStochCalc.Brownian.Continuity.kolmogorov_real_tail_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | lam < |X s ω - X t ω|}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / ENNReal.ofReal lam ^ p := by
  refine le_trans (measure_mono ?_)
    (kolmogorov_markov_bound_readable P X hX s t
      (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
/-- **Lemma A: per-level bad-set bound.** The union over level-`n` dyadic
intervals in `[0,1]` of the events `{ |increment| > ((1/2)^α)^n }` has measure
`≤ ofReal((M:ℝ)·ρⁿ)` with `ρ = (1/2)^{q−αp−1}`. (Borel–Cantelli summability
follows when `αp < q−1`, i.e. `ρ < 1`.) -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hrn0 : 0 < r ^ n := pow_pos hr0 n
  have hhalf_n : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hrnp0 : (0 : ℝ) < (r ^ n) ^ p := Real.rpow_pos_of_pos hrn0 p
  -- Per-interval Markov term, converted to `ofReal`.
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      P {ω | r ^ n < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|}
        ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (r ^ n) ^ p) := by
    intro k _
    have hb := LevyStochCalc.Brownian.Continuity.kolmogorov_real_tail_bound P X hX
      (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n) hrn0
    refine le_trans hb (le_of_eq ?_)
    have hedist : edist (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [edist_dist, Real.dist_eq]
      congr 1
      rw [show ((k : ℝ) + 1) / 2 ^ n - (k : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n from by
        rw [div_pow, one_pow]; ring]
      exact abs_of_pos hhalf_n
    rw [hedist, ENNReal.ofReal_rpow_of_pos hhalf_n,
        ENNReal.ofReal_rpow_of_pos hrn0, ← ENNReal.ofReal_coe_nnreal (p := M),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos hrnp0]
  refine le_trans (measure_biUnion_finset_le (Finset.range (2 ^ n)) _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) from by
        rw [← ENNReal.ofReal_natCast]; norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 1
  rw [hr_def, show (2 : ℝ) ^ n
        * ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p)
      = (M : ℝ) * ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q
          / (((1 / 2 : ℝ) ^ α) ^ n) ^ p) from by ring,
      LevyStochCalc.Brownian.Continuity.kc_exponent_identity_readable]
