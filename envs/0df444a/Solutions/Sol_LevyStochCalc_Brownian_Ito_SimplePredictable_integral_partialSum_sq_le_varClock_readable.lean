-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le_varClock_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:26.874742+00:00
-- url     : https://prove2.me/submissions/de3ed090-c9c8-41b2-b973-2bbfb1d2beb3

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_sq_succ_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_zero (ω : Ω) : G.partialSum W 0 ω = 0 := by simp [partialSum]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_zero (c : Fin G.N → ℝ) : G.varClock c 0 = 0 := by simp [varClock]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_succ (c : Fin G.N → ℝ) {k : ℕ} (hk : k < G.N) :
    G.varClock c (k + 1) = G.varClock c k
      + c ⟨k, hk⟩ ^ 2 * (G.partition (⟨k, hk⟩ : Fin G.N).succ
        - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  unfold varClock
  rw [Finset.sum_range_succ, dif_pos hk]
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
section Moments
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
/-- A coefficient bounded by `c` has even moments at most the matching power of `c`. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_xi_even_le {c : ℝ} (i : Fin G.N)
    (hci : ∀ ω, |G.ξ i ω| ≤ c) (m : ℕ) :
    ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ c ^ (2 * m) := by
  have hnn : ∀ ω, (0 : ℝ) ≤ (G.ξ i ω) ^ (2 * m) := fun ω => by
    rw [pow_mul]; positivity
  have hcnn : (0 : ℝ) ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  have hpow : ∀ ω, (G.ξ i ω) ^ (2 * m) ≤ c ^ (2 * m) := fun ω => by
    have h : |G.ξ i ω| ^ (2 * m) ≤ c ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (hci ω) _
    rwa [← abs_pow, abs_of_nonneg (hnn ω)] at h
  have hint : Integrable (fun ω => (G.ξ i ω) ^ (2 * m)) P := by
    refine (integrable_const (c ^ (2 * m))).mono
      ((G.ξ_measurable _).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω), abs_of_nonneg hcnn]
    exact hpow ω
  calc ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ ∫ _ω : Ω, c ^ (2 * m) ∂P :=
        integral_mono hint (integrable_const _) hpow
    _ = c ^ (2 * m) := by simp
include hℱ h_adapt hC0 hC in
/-- Second moment of a partial sum against a per-tile coefficient bound. -/
theorem solution {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    rw [G.integral_partialSum_sq_succ_readable W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    have h2 : ∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P ≤ c ⟨n, hn⟩ ^ 2 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 1
    linarith [mul_le_mul_of_nonneg_right h2 hΔ0]
