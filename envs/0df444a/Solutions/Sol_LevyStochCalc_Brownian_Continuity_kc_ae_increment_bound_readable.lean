-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_ae_increment_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:29.681072+00:00
-- url     : https://prove2.me/submissions/ff3d9d53-dd5d-40da-8636-f20925feaa7d

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_level_bad_measure_readable

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
/-- **Lemma B: a.s. dyadic increment bound (Borel–Cantelli).** When
`α·p < q − 1`, almost every path has, for some level `N`, all consecutive
level-`n` dyadic increments in `[0,1]` bounded by `((1/2)^α)^n` for every
`n ≥ N`. This supplies the hypothesis of `dyadic_holder_chaining`. -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|
        ≤ ((1 / 2 : ℝ) ^ α) ^ n := by
  set ρ : ℝ := (1 / 2 : ℝ) ^ (q - α * p - 1) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  set A : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (2 ^ n),
      {ω | ((1 / 2 : ℝ) ^ α) ^ n
          < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|} with hA_def
  have hAle : ∀ n, P (A n) ≤ ENNReal.ofReal ((M : ℝ) * ρ ^ n) := fun n =>
    LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_readable P X hX n
  have hsummable_real : Summable (fun n => (M : ℝ) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have htsum_ne : (∑' n, P (A n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable_real]
    exact ENNReal.ofReal_ne_top
  have hlimsup : P (Filter.limsup A Filter.atTop) = 0 :=
    measure_limsup_atTop_eq_zero htsum_ne
  have hae : ∀ᵐ ω ∂P, ω ∉ Filter.limsup A Filter.atTop := by
    rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hlimsup
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently,
      Filter.eventually_atTop] at hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn k hk0 hk1 => ?_⟩
  have hωn : ω ∉ A n := hN n hn
  rw [hA_def] at hωn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hωn
  have hk'mem : k.toNat ∈ Finset.range (2 ^ n) := by
    rw [Finset.mem_range]
    have hcast2 : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
    omega
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  have hb := hωn k.toNat hk'mem
  rw [hcast] at hb
  exact hb
