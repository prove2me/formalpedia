-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:44.873453+00:00
-- url     : https://prove2.me/submissions/180c96a0-dac3-4137-a942-5d6e37932613

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoVersionExists
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_continuous_modification_stochasticIntegralBrownian_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoVersionExists.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A measurable null set outside which an almost-everywhere property holds. -/
theorem LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hsub, hmeas, hzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  exact ⟨N, hmeas, hzero, fun ω hω => by_contra fun hp => hω (hsub hp)⟩
theorem LevyStochCalc.Brownian.Ito.dyadicApprox_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : dyadicApprox n u ≤ u := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicApprox, div_le_iff₀ h2]
  exact Nat.floor_le (by positivity)
theorem LevyStochCalc.Brownian.Ito.sub_dyadicApprox_lt (u : ℝ) (n : ℕ) : u - dyadicApprox n u < 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl := Nat.lt_floor_add_one (u * 2 ^ n)
  rw [dyadicApprox, sub_lt_iff_lt_add,
    show (1 : ℝ) / 2 ^ n + (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
      = ((⌊u * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n by ring, lt_div_iff₀ h2]
  linarith
theorem LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox {u : ℝ} (hu : 0 ≤ u) :
    Filter.Tendsto (fun n : ℕ => dyadicApprox n u) Filter.atTop (nhds u) := by
  have hlo : ∀ n : ℕ, u - 1 / 2 ^ n ≤ dyadicApprox n u := fun n => by
    have := sub_dyadicApprox_lt u n
    linarith
  have hhi : ∀ n : ℕ, dyadicApprox n u ≤ u := dyadicApprox_le hu
  have hpow : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  have hsub : Filter.Tendsto (fun n : ℕ => u - 1 / 2 ^ n) Filter.atTop (nhds u) := by
    simpa using (tendsto_const_nhds (x := u) (f := Filter.atTop (α := ℕ))).sub hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds hlo hhi
section Exists
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ hC0 hCH in
/-- **A continuous adapted modification of the Itô integral exists** when the filtration is
constant before time `0` and contains the measurable null sets. -/
theorem solution
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω : Ω, Continuous fun t => Y t ω)
      ∧ (∀ u : ℝ, Measurable[ℱ u] (Y u))
      ∧ ∀ t : ℝ, 0 ≤ t → Y t =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  obtain ⟨Y, hYcont, hYmod⟩ :=
    LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian_readable W ℱ hℱ H hm hp hq hC0 hCH
  obtain ⟨N₁, hN₁meas, hN₁zero, hN₁cont⟩ := LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae hYcont
  -- the modification agrees with the integral at every nonnegative dyadic time
  have hdnn : ∀ p : ℕ × ℕ, (0 : ℝ) ≤ ((p.1 : ℝ) / 2 ^ p.2) := fun p => by positivity
  choose Nd hNdmeas hNdzero hNdout using fun p : ℕ × ℕ =>
    LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae (hYmod ((p.1 : ℝ) / 2 ^ p.2) (hdnn p))
  set N : Set Ω := N₁ ∪ ⋃ p : ℕ × ℕ, Nd p with hNdef
  have hNmeas : MeasurableSet N :=
    hN₁meas.union (MeasurableSet.iUnion fun p => hNdmeas p)
  have hNzero : P N = 0 :=
    MeasureTheory.measure_union_null hN₁zero
      (MeasureTheory.measure_iUnion_null fun p => hNdzero p)
  have hNcont : ∀ ω : Ω, ω ∉ N → Continuous fun t => Y t ω := fun ω hω =>
    hN₁cont ω fun h => hω (Or.inl h)
  have hNdyad : ∀ (p : ℕ × ℕ) (ω : Ω), ω ∉ N →
      Y ((p.1 : ℝ) / 2 ^ p.2) ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq ((p.1 : ℝ) / 2 ^ p.2) ω :=
    fun p ω hω => hNdout p ω fun h => hω (Or.inr (Set.mem_iUnion.mpr ⟨p, h⟩))
  -- `ℱ t` contains `ℱ 0` at every time, hence contains `N`
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hNm : ∀ t : ℝ, MeasurableSet[ℱ t] N := fun t =>
    hle0 t N (hnull N hNmeas hNzero)
  -- the truncated modification is adapted, as a pointwise limit along dyadic times
  have hYind : ∀ u : ℝ, 0 ≤ u →
      Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ) else Y u ω := by
    intro u hu
    have hstep : ∀ n : ℕ, Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ)
        else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
      intro n
      have hSI : Measurable[ℱ u]
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u)) := by
        have h1 := (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq
          (LevyStochCalc.Brownian.Ito.dyadicApprox n u)).measurable
        exact fun A hA => ℱ.mono (LevyStochCalc.Brownian.Ito.dyadicApprox_le hu n) _ (h1 hA)
      exact Measurable.ite (hNm u) measurable_const hSI
    have hlim : Filter.Tendsto (fun (n : ℕ) (ω : Ω) => if ω ∈ N then (0 : ℝ)
          else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω)
        Filter.atTop (nhds fun ω => if ω ∈ N then (0 : ℝ) else Y u ω) := by
      rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ N
      · simp only [hω, if_true]
        exact tendsto_const_nhds
      · simp only [hω, if_false]
        have heq : (fun n : ℕ => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω) = fun n => Y (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
          funext n
          exact (hNdyad (⌊u * 2 ^ n⌋₊, n) ω hω).symm
        rw [heq]
        exact Filter.Tendsto.comp ((hNcont ω hω).continuousAt (x := u))
          (LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox hu)
    letI : MeasurableSpace Ω := ℱ u
    exact measurable_of_tendsto_metrizable hstep hlim
  refine ⟨fun t ω => if ω ∈ N then 0 else Y (max t 0) ω, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using continuous_const
    · simp only [hω, if_false]
      exact (hNcont ω hω).comp (continuous_id.max continuous_const)
  · intro u
    rcases le_or_gt 0 u with hu | hu
    · simp only [max_eq_left hu]
      exact hYind u hu
    · simp only [max_eq_right hu.le]
      exact fun A hA => hle0 u _ (hYind 0 le_rfl hA)
  · intro t ht
    filter_upwards [hYmod t ht,
      MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω hωN
    rw [if_neg hωN, max_eq_left ht]
    exact hω
