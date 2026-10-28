-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:38.682863+00:00
-- url     : https://prove2.me/submissions/55f4160f-5912-4697-a0ed-151d808fc3bd

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Continuity
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_dense_dyadicRationals_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_exists_tendsto_of_local_holder_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_nbhd_holder_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_modification_ae_eq_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Continuity.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Kolmogorov–Chentsov continuous modification.** A real-valued process
satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` with `q > 1` admits a
modification with continuous paths (Karatzas–Shreve 2.2.8 / Le Gall 2.9). The
modification is the dyadic `extendFrom` of `X`; continuity comes from a.s. local
Hölder regularity (`kc_ae_nbhd_holder`) via `extendFrom`, and the modification
property from `kolmogorov_modification_ae_eq`. The Hölder exponent is
`α := (q−1)/(2p)` (`0 < α`, `αp < q−1`). -/
theorem solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have hp : 0 < p := hX.p_pos
  set α : ℝ := (q - 1) / (2 * p) with hα_def
  have hα0 : 0 < α := by rw [hα_def]; exact div_pos (by linarith) (by linarith)
  have hαpq : α * p < q - 1 := by
    have h2p : 0 < 2 * p := by linarith
    rw [hα_def, div_mul_eq_mul_div, div_lt_iff₀ h2p]
    nlinarith [mul_pos (show (0:ℝ) < q - 1 from by linarith) hp]
  set Y : ℝ → Ω → ℝ :=
    fun t ω => extendFrom LevyStochCalc.Brownian.Continuity.dyadicRationals (fun s => X s ω) t with hY_def
  have hnbhd := LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_readable P X hX hα0 hαpq
  have hcont : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) := by
    filter_upwards [hnbhd] with ω hω
    exact continuous_extendFrom LevyStochCalc.Brownian.Continuity.dense_dyadicRationals_readable
      (fun t => LevyStochCalc.Brownian.Continuity.exists_tendsto_of_local_holder_readable LevyStochCalc.Brownian.Continuity.dense_dyadicRationals_readable hα0 t (hω t))
  refine ⟨Y, hcont, ?_⟩
  refine LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq_readable P X hX Y hcont ?_
  intro s hs
  filter_upwards [hnbhd] with ω hω
  -- `Y s ω = extendFrom dyadicRationals (· ↦ X · ω) s = X s ω`
  refine extendFrom_eq (subset_closure hs) ?_
  obtain ⟨K, ρ, hρ, hK0, hHol⟩ := hω s
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α)),
    lt_min hρ (Real.rpow_pos_of_pos (by positivity) _), fun u hu hdu => ?_⟩
  have huρ : u ∈ Set.Ioo (s - ρ) (s + ρ) := by
    rw [Real.dist_eq] at hdu
    have := lt_of_lt_of_le hdu (min_le_left _ _)
    rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩
  have hsρ : s ∈ Set.Ioo (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  have hb := hHol u hu s hs huρ hsρ
  have hdu2 : |u - s| < (ε / (K + 1)) ^ (1 / α) := by
    rw [← Real.dist_eq]; exact lt_of_lt_of_le hdu (min_le_right _ _)
  have hpow : |u - s| ^ α < ε / (K + 1) := by
    have h1 := Real.rpow_lt_rpow (abs_nonneg _) hdu2 hα0
    rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hα0),
          Real.rpow_one]] at h1
  rw [Real.dist_eq]
  calc |X u ω - X s ω| ≤ K * |u - s| ^ α := hb
    _ ≤ (K + 1) * |u - s| ^ α := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (K + 1) * (ε / (K + 1)) := by apply mul_lt_mul_of_pos_left hpow (by positivity)
    _ = ε := by field_simp
