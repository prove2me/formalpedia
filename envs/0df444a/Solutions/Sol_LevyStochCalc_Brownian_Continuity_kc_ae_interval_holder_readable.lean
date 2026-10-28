-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:23.706145+00:00
-- url     : https://prove2.me/submissions/bc20bdcd-0415-4828-98dd-5ca7869f1ad7

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadic_holder_chaining_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_increment_bound_readable

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
/-- Dyadic rationals are closed under adding an integer. -/
lemma LevyStochCalc.Brownian.Continuity.add_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x + (j : ℝ) ∈ dyadicRationals := by
  obtain ⟨k, n, rfl⟩ := hx
  refine ⟨k + j * 2 ^ n, n, ?_⟩
  rw [zpow_neg, zpow_natCast]
  push_cast
  field_simp
/-- Dyadic rationals are closed under subtracting an integer. -/
lemma LevyStochCalc.Brownian.Continuity.sub_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x - (j : ℝ) ∈ dyadicRationals := by
  have := add_intCast_mem_dyadicRationals hx (-j)
  simpa [sub_eq_add_neg] using this
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
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Translation invariance of the Kolmogorov condition.** If `X` satisfies
the Kolmogorov condition, so does the time-shifted process `s ↦ X (s + a)`
(the bound depends only on `edist s t = edist (s+a) (t+a)`). Used to transport
the `[0,1]` construction to every interval `[j, j+1]`. -/
lemma LevyStochCalc.Brownian.Continuity.isKolmogorovProcess_comp_add_right
    {P : Measure Ω} (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (a : ℝ) :
    ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + a) ω) P p q M where
  measurablePair s t := hX.measurablePair (s + a) (t + a)
  kolmogorovCondition s t := by
    have he : edist s t = edist (s + a) (t + a) := by
      rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
          show (s + a) - (t + a) = s - t from by ring]
    rw [he]
    exact hX.kolmogorovCondition (s + a) (t + a)
  p_pos := hX.p_pos
  q_pos := hX.q_pos
/-- **Per-interval a.s. Hölder.** For `αp < q − 1`, almost every path is
α-Hölder (at small scales) on the dyadics of every unit interval `[j, j+1]`.
Obtained by transporting `dyadic_holder_chaining` (on `[0,1]`) to `[j,j+1]` via
the time-shifted process `X(·+j)` (translation-invariant Kolmogorov condition),
intersected over the countable family `j : ℤ`. -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ s ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals, ∀ t ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals,
        (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
        |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  have hXj : ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + (j : ℝ)) ω) P p q M :=
    LevyStochCalc.Brownian.Continuity.isKolmogorovProcess_comp_add_right X hX j
  filter_upwards [LevyStochCalc.Brownian.Continuity.kc_ae_increment_bound_readable P (fun s ω => X (s + (j : ℝ)) ω) hXj hαpq] with ω hω
  obtain ⟨N, hN⟩ := hω
  obtain ⟨K, hK0, hKbound⟩ :=
    LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining_readable (f := fun u => X (u + (j : ℝ)) ω) (α := α) (C := 1) (N := N)
      hα0 (by norm_num) (fun n hn k hk0 hk1 => by
        rw [one_mul]
        simp only [Int.cast_add, Int.cast_one]
        exact hN n hn k hk0 hk1)
  refine ⟨K, N, hK0, fun s hs t ht hjs hsj1 hjt htj1 hst => ?_⟩
  have hu : s - (j : ℝ) ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals := LevyStochCalc.Brownian.Continuity.sub_intCast_mem_dyadicRationals hs j
  have hv : t - (j : ℝ) ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals := LevyStochCalc.Brownian.Continuity.sub_intCast_mem_dyadicRationals ht j
  have hKb := hKbound (s - (j : ℝ)) hu (t - (j : ℝ)) hv (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by rw [show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring]; exact hst)
  rw [show s - (j : ℝ) + (j : ℝ) = s from by ring,
      show t - (j : ℝ) + (j : ℝ) = t from by ring,
      show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring] at hKb
  exact hKb
