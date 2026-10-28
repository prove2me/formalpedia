-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:15.313982+00:00
-- url     : https://prove2.me/submissions/458105f2-1b9f-4b92-832a-b346bc6d393c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_dense_dyadicRationals_readable
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_markov_bound_readable

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
/-- For every `t : ℝ`, there is a sequence of dyadic rationals strictly
increasing to `t`. Wrapper around `Dense.exists_seq_strictMono_tendsto` +
`dense_dyadicRationals`. -/
lemma LevyStochCalc.Brownian.Continuity.exists_seq_dyadic_tendsto (t : ℝ) :
    ∃ u : ℕ → ℝ, StrictMono u
      ∧ (∀ n, u n ∈ Set.Iio t ∩ dyadicRationals)
      ∧ Filter.Tendsto u Filter.atTop (nhds t) :=
  dense_dyadicRationals_readable.exists_seq_strictMono_tendsto t
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
/-- **Step 3: extended process equals X a.s. at each t.**

By the Kolmogorov condition (Markov inequality), `X_{t_n} → X_t` in probability
as `t_n → t`. Combined with the a.s.-pointwise dyadic limit (Y is continuous
and equals X on dyadics), the extended process equals X almost surely at
each `t`.

Sub-steps:
1. **Continuity in probability of X**: `X t_n → X t` in probability via Markov
   + Kolmogorov condition.
2. **Y_{t_n} → Y_t** almost surely as t_n → t along any sequence (since Y is
   continuous a.s.).
3. **X_{t_n} = Y_{t_n}** for dyadic t_n (hypothesis).
4. Combine: at each fixed t, X_t = Y_t a.s. (limit of equal-a.s. sequences,
   one converging in probability the other a.s., are equal a.s.). -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by
  intro t
  -- Step 1: pick dyadic sequence u_n strictly increasing to t.
  obtain ⟨u, _hu_mono, hu_dyadic, hu_tendsto⟩ := LevyStochCalc.Brownian.Continuity.exists_seq_dyadic_tendsto t
  -- Step 2: each X(s) is measurable (from Mathlib's IsKolmogorovProcess.measurable
  -- which needs MeasurableSpace + BorelSpace + SecondCountableTopology on E = ℝ,
  -- all of which ℝ has).
  have h_X_meas : ∀ s : ℝ, Measurable (X s) := fun s => hX.measurable s
  -- Step 3: Chebyshev / Markov on the Kolmogorov moment bound gives
  -- convergence-in-measure of X(u n) → X(t).
  have hp_pos : 0 < p := hX.p_pos
  have hq_pos : 0 < q := hX.q_pos
  -- Direct Markov: P {ω | δ^p ≤ edist^p} ≤ (∫⁻ edist^p) / δ^p
  --   ≤ M·edist(u n,t)^q/δ^p.
  -- For real-valued X, edist (X s ω) (X t ω) = ‖X s ω - X t ω‖ₑ (PseudoEMetric on ℝ
  -- via |·|), so this is convergence of (X (u n)) → X t in measure.
  have h_TIM : MeasureTheory.TendstoInMeasure P (fun n => X (u n)) Filter.atTop (X t) := by
    intro δ hδ
    -- Handle δ = ⊤ separately: edist : ENNReal-valued from real-valued X is
    -- always < ⊤, so {ω | ⊤ ≤ edist} is empty, P = 0, tendsto trivially.
    by_cases hδ_top : δ = ⊤
    · subst hδ_top
      simp_rw [top_le_iff]
      have h_set_empty : ∀ n,
          {ω | edist (X (u n) ω) (X t ω) = ⊤} = ∅ := by
        intro n; ext ω
        simp
      simp_rw [h_set_empty]
      simp
    -- Now δ ≠ ⊤. Step D: edist (u n) t → 0 from u n → t.
    have h_edist_tendsto : Filter.Tendsto (fun n => edist (u n) t)
        Filter.atTop (nhds 0) :=
      (tendsto_iff_edist_tendsto_0.mp hu_tendsto)
    -- Step E: edist (u n) t ^ q → 0 (continuity of x^q at 0, with 0^q = 0 for q > 0).
    have h_pow_tendsto : Filter.Tendsto (fun n => edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := h_edist_tendsto.ennrpow_const q
      rwa [ENNReal.zero_rpow_of_pos hq_pos] at this
    -- Step F: M · edist^q → 0 (M ≠ ⊤ since M : ℝ≥0).
    have hM_ne_top : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h_M_pow_tendsto : Filter.Tendsto
        (fun n => (M : ℝ≥0∞) * edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul h_pow_tendsto (Or.inr hM_ne_top)
      simpa using this
    -- Step G: divide the per-pair Markov bound by δ^p (δ^p ≠ 0 for the
    -- constant-division tendsto below).
    have hδp_pos : 0 < δ ^ p := by
      apply ENNReal.rpow_pos_of_nonneg hδ
      exact hp_pos.le
    -- The bound on P {δ ≤ edist}: the per-pair Markov/Chebyshev tail bound.
    have h_set_bound : ∀ n, P {ω | δ ≤ edist (X (u n) ω) (X t ω)}
        ≤ ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p :=
      fun n => LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_readable P X hX (u n) t hδ hδ_top
    -- Step G applied: (M · edist^q) / δ^p → 0 from h_M_pow_tendsto (constant division).
    have h_bound_tendsto : Filter.Tendsto
        (fun n => ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.div_const h_M_pow_tendsto (Or.inr hδp_pos.ne')
      simpa using this
    -- Step H: squeeze 0 ≤ P {δ ≤ edist} ≤ bound → 0.
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_bound_tendsto (fun _ => bot_le) h_set_bound
  -- Step 4: extract a.s.-converging subsequence.
  obtain ⟨ns, _hns_mono, hns_ae⟩ := h_TIM.exists_seq_tendsto_ae
  -- Step 5: combine on the full-measure intersection.
  -- A := {ω : Continuous Y(·) ω}              (from h_continuous, P-full)
  -- B_k := {ω : Y(u (ns k)) ω = X(u (ns k)) ω}  (from h_dyadic_eq, P-full)
  -- C := {ω : X(u (ns k)) ω → X(t) ω}           (from hns_ae, P-full)
  -- D := A ∩ ⋂_k B_k ∩ C  (countable intersection of full sets = full)
  -- On D: Y(u (ns k)) ω = X(u (ns k)) ω → X(t) ω.
  --       Also Y(u (ns k)) ω → Y(t) ω (by continuity of Y at t along u (ns k) → t).
  --       By uniqueness of limits in ℝ: Y(t) ω = X(t) ω.
  filter_upwards [h_continuous, hns_ae,
    MeasureTheory.ae_all_iff.mpr (fun k => h_dyadic_eq (u (ns k)) (hu_dyadic (ns k)).2)]
    with ω h_Y_cont h_X_tendsto h_eq_seq
  -- u (ns k) → t (subsequence of u → t via StrictMono ns → atTop atTop)
  have h_subseq_tendsto : Filter.Tendsto (fun k => u (ns k)) Filter.atTop (nhds t) :=
    hu_tendsto.comp _hns_mono.tendsto_atTop
  -- Y is continuous at t (from a.s. continuity)
  have h_Y_tendsto : Filter.Tendsto (fun k => Y (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) :=
    (h_Y_cont.tendsto t).comp h_subseq_tendsto
  -- So X(u (ns k)) ω → Y(t) ω (substitute Y(u (ns k)) ω = X(u (ns k)) ω),
  -- and also → X(t) ω. By uniqueness of limits in ℝ, Y(t) ω = X(t) ω.
  have h_X_to_Y : Filter.Tendsto (fun k => X (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) := by
    have h_eq : (fun k => X (u (ns k)) ω) = fun k => Y (u (ns k)) ω := by
      funext k
      exact (h_eq_seq k).symm
    rw [h_eq]
    exact h_Y_tendsto
  exact tendsto_nhds_unique h_X_to_Y h_X_tendsto
