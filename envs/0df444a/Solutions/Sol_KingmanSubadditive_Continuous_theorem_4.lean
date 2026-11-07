-- Prove2me | solution 1 for KingmanSubadditive.Continuous.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:48:41.364207+00:00
-- url     : https://prove2.me/submissions/b556ef73-f440-40ac-b1b5-ca393393280b

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process
import Theorems.Thm_KingmanSubadditive_Continuous_skeleton_limit
import Theorems.Thm_KingmanSubadditive_Continuous_sandwich
import Theorems.Thm_KingmanSubadditive_Continuous_oscillation_vanishes

open MeasureTheory Filter Topology
open KingmanSubadditive.Continuous

/-- Pointwise bound behind the sandwich argument. -/
theorem kingman_thm4_pointwise {S : Type*} [MeasurableSpace S]
    (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (ξ : S → ℝ) (ω : S) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hnt : (n : ℝ) ≤ t) (htn : t < (n : ℝ) + 1)
    (hfin : oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω < ⊤) :
    |x 0 t ω / t - ξ ω| ≤
      (2 * |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω| + |x 0 n ω / n - ξ ω| +
        |ξ ω| / n) +
      (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal / n := by
  set O := (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal with hO
  have hO0 : 0 ≤ O := ENNReal.toReal_nonneg
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 0 ≤ |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω| := abs_nonneg _
  have h3 : 0 ≤ |ξ ω| / n := div_nonneg (abs_nonneg _) hnpos.le
  have h4 : 0 ≤ O / n := div_nonneg hO0 hnpos.le
  rcases eq_or_lt_of_le hnt with heq | hlt
  · subst heq
    linarith
  obtain ⟨hlo, hhi⟩ := sandwich P x hproc n hn t hlt htn ω hfin
  rw [← hO] at hlo hhi
  set X := x 0 t ω
  set A := x 0 ((n : ℝ) + 1) ω
  set B := x 0 (n : ℝ) ω
  set z := ξ ω
  have htpos : 0 < t := by linarith
  have hn1' : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have e1 : |A / ((n : ℝ) + 1) - z| = |A - ((n : ℝ) + 1) * z| / ((n : ℝ) + 1) := by
    rw [show A / ((n : ℝ) + 1) - z = (A - ((n : ℝ) + 1) * z) / ((n : ℝ) + 1) by
      field_simp, abs_div, abs_of_pos hn1']
  have e2 : |B / n - z| = |B - n * z| / n := by
    rw [show B / n - z = (B - n * z) / n by field_simp, abs_div, abs_of_pos hnpos]
  have e3 : |X / t - z| = |X - t * z| / t := by
    rw [show X / t - z = (X - t * z) / t by field_simp, abs_div, abs_of_pos htpos]
  have hz1 : |(t - n) * z| ≤ |z| := by
    rw [abs_mul]
    have : |t - n| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg z, abs_nonneg (t - n)]
  have hz2 : |((n : ℝ) + 1 - t) * z| ≤ |z| := by
    rw [abs_mul]
    have : |(n : ℝ) + 1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg z, abs_nonneg ((n : ℝ) + 1 - t)]
  have key : |X - t * z| ≤ |A - ((n : ℝ) + 1) * z| + |B - n * z| + |z| + O := by
    have a1 := le_abs_self (B - n * z)
    have a2 := neg_abs_le (A - ((n : ℝ) + 1) * z)
    have a3 := neg_abs_le ((t - n) * z)
    have a4 := neg_abs_le (((n : ℝ) + 1 - t) * z)
    have a5 := abs_nonneg (A - ((n : ℝ) + 1) * z)
    have a6 := abs_nonneg (B - n * z)
    rw [abs_le]
    constructor
    · linarith
    · linarith
  rw [e3, e1, e2]
  have hA0 := abs_nonneg (A - ((n : ℝ) + 1) * z)
  have step1 : |X - t * z| / t ≤ |X - t * z| / n :=
    div_le_div_of_nonneg_left (abs_nonneg _) hnpos hnt
  have step2 : |A - ((n : ℝ) + 1) * z| / n ≤
      2 * (|A - ((n : ℝ) + 1) * z| / ((n : ℝ) + 1)) := by
    rw [div_le_iff₀ hnpos]
    have : 2 * (|A - ((n : ℝ) + 1) * z| / ((n : ℝ) + 1)) * n =
        |A - ((n : ℝ) + 1) * z| * (2 * n / ((n : ℝ) + 1)) := by ring
    rw [this]
    have : (1 : ℝ) ≤ 2 * n / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hn1']; linarith
    nlinarith
  have step3 : |X - t * z| / n ≤
      |A - ((n : ℝ) + 1) * z| / n + |B - n * z| / n + |z| / n + O / n := by
    rw [← add_div, ← add_div, ← add_div]
    exact div_le_div_of_nonneg_right key hnpos.le
  linarith

/-- For a nonnegative function, the Bochner integral is bounded by the real part of the
lower Lebesgue integral (no measurability needed). -/
theorem kingman_thm4_integral_le {S : Type*} [MeasurableSpace S] (P : Measure S)
    (f : S → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∫ ω, f ω ∂P ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal := by
  by_cases hi : Integrable f P
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hi.aestronglyMeasurable]
  · rw [integral_undef hi]
    exact ENNReal.toReal_nonneg

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∃ ξ : S → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ => x 0 t ω / t) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun t : ℝ => ∫ ω, |x 0 t ω / t - ξ ω| ∂P)
        atTop (𝓝 0) ∧
      (∫ ω, ξ ω ∂P) = gamma P x := by
  obtain ⟨ξ, hξ, hae, hL1, hmean⟩ := skeleton_limit P x hproc hsep a b ha hab hosc
  obtain ⟨hosc_ae, hosc_L1⟩ := oscillation_vanishes P x hproc hsep a b ha hab hosc
  set Om : ℕ → S → ENNReal := fun n ω => oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω
    with hOm
  set v : ℕ → S → ℝ := fun n ω =>
    2 * |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω| + |x 0 n ω / n - ξ ω| + |ξ ω| / n
    with hv
  have hint := hproc.2.2.2.1
  -- the floor map
  have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hfloor : ∀ᶠ t : ℝ in atTop, 1 ≤ ⌊t⌋₊ ∧ ((⌊t⌋₊ : ℕ) : ℝ) ≤ t ∧
      t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact ⟨Nat.le_floor (by simpa using ht), Nat.floor_le (by linarith),
      Nat.lt_floor_add_one t⟩
  -- finiteness of oscillation from `Om n / n → 0`
  have hfinite : ∀ (u : ℕ → ENNReal), Tendsto (fun n : ℕ => u n / (n : ENNReal)) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop, u n < ⊤ := by
    intro u hu
    filter_upwards [hu.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with n hn hn1
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n)] at hn
    exact absurd hn (by simp)
  have hshift : ∀ (f : ℕ → ℝ), Tendsto f atTop (𝓝 0) →
      Tendsto (fun n : ℕ => f (n + 1)) atTop (𝓝 0) := fun f hf =>
    hf.comp (tendsto_add_atTop_nat 1)
  refine ⟨ξ, hξ, ?_, ?_, hmean⟩
  · -- almost sure convergence
    filter_upwards [hae, hosc_ae] with ω h1 h2
    have he : Tendsto (fun n : ℕ => |x 0 n ω / (n : ℝ) - ξ ω|) atTop (𝓝 0) := by
      have := (h1.sub_const (ξ ω)).abs
      simpa using this
    have he' : Tendsto (fun n : ℕ => |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω|)
        atTop (𝓝 0) := by
      have := hshift _ he
      simpa using this
    have hvlim : Tendsto (fun n => v n ω) atTop (𝓝 0) := by
      have := ((he'.const_mul 2).add he).add (tendsto_const_div_atTop_nhds_zero_nat |ξ ω|)
      simpa [hv] using this
    have hOlim : Tendsto (fun n : ℕ => (Om n ω).toReal / n) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
      refine this.congr (fun n => ?_)
      simp [Function.comp, ENNReal.toReal_div, Om]
    have hW := (hvlim.add hOlim).comp hfl
    rw [zero_add] at hW
    have hfinω := hfl.eventually (hfinite (fun n => Om n ω) h2)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hW
    filter_upwards [hfloor, hfinω] with t ⟨hn, hnt, htn⟩ hfin
    rw [Real.norm_eq_abs]
    exact kingman_thm4_pointwise P x hproc ξ ω _ hn t hnt htn hfin
  · -- convergence in mean
    have hvint : ∀ n : ℕ, 1 ≤ n → Integrable (v n) P := by
      intro n hn
      have i1 : Integrable (x 0 ((n : ℝ) + 1)) P := hint _ (by positivity)
      have i2 : Integrable (x 0 (n : ℝ)) P := hint _ (by exact_mod_cast hn)
      exact ((((i1.div_const _).sub hξ).abs.const_mul 2).add
        ((i2.div_const _).sub hξ).abs).add (hξ.abs.div_const _)
    have hvval : ∀ n : ℕ, 1 ≤ n → ∫ ω, v n ω ∂P =
        2 * ∫ ω, |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω| ∂P +
          ∫ ω, |x 0 n ω / n - ξ ω| ∂P + (∫ ω, |ξ ω| ∂P) / n := by
      intro n hn
      have i1 : Integrable (x 0 ((n : ℝ) + 1)) P := hint _ (by positivity)
      have i2 : Integrable (x 0 (n : ℝ)) P := hint _ (by exact_mod_cast hn)
      simp only [hv]
      rw [integral_add, integral_add, integral_const_mul, integral_div]
      · exact (((i1.div_const _).sub hξ).abs.const_mul 2)
      · exact ((i2.div_const _).sub hξ).abs
      · exact (((i1.div_const _).sub hξ).abs.const_mul 2).add ((i2.div_const _).sub hξ).abs
      · exact hξ.abs.div_const _
    have hL1' : Tendsto (fun n : ℕ => ∫ ω, |x 0 ((n : ℝ) + 1) ω / ((n : ℝ) + 1) - ξ ω| ∂P)
        atTop (𝓝 0) := by
      have := hshift _ hL1
      simpa using this
    have hvlim : Tendsto (fun n => ∫ ω, v n ω ∂P) atTop (𝓝 0) := by
      have := ((hL1'.const_mul 2).add hL1).add
        (tendsto_const_div_atTop_nhds_zero_nat (∫ ω, |ξ ω| ∂P))
      simp only [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [hvval n hn]
    set w : ℕ → ENNReal := fun n =>
      ENNReal.ofReal (∫ ω, v n ω ∂P) + ∫⁻ ω, Om n ω / (n : ENNReal) ∂P with hw
    have hwlim : Tendsto w atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (∫ ω, v n ω ∂P)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).comp hvlim
        simpa [Function.comp_def] using this
      have := h1.add hosc_L1
      simpa [hw] using this
    have hwfin : ∀ᶠ n in atTop, w n ≠ ⊤ :=
      (hwlim.eventually (gt_mem_nhds zero_lt_one)).mono fun n hn =>
        ne_top_of_lt hn
    have hwR := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hwlim).comp hfl
    simp only [ENNReal.toReal_zero] at hwR
    refine squeeze_zero' (Eventually.of_forall fun t =>
      integral_nonneg fun ω => abs_nonneg _) ?_ hwR
    filter_upwards [hfloor, hfl.eventually hwfin] with t ⟨hn, hnt, htn⟩ hwf
    set n := ⌊t⌋₊
    have hnpos : (0 : ℝ) < n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine (kingman_thm4_integral_le P _ (fun ω => abs_nonneg _)).trans ?_
    simp only [Function.comp]
    apply ENNReal.toReal_mono hwf
    have hpt : ∀ ω, ENNReal.ofReal |x 0 t ω / t - ξ ω| ≤
        ENNReal.ofReal (v n ω) + Om n ω / (n : ENNReal) := by
      intro ω
      by_cases hfin : Om n ω < ⊤
      · have hb := kingman_thm4_pointwise P x hproc ξ ω n hn t hnt htn hfin
        have hv0 : 0 ≤ v n ω := by simp only [hv]; positivity
        have hO0 : 0 ≤ (Om n ω).toReal / n := by positivity
        calc ENNReal.ofReal |x 0 t ω / t - ξ ω|
            ≤ ENNReal.ofReal (v n ω + (Om n ω).toReal / n) := ENNReal.ofReal_le_ofReal hb
          _ = ENNReal.ofReal (v n ω) + ENNReal.ofReal ((Om n ω).toReal / n) :=
              ENNReal.ofReal_add hv0 hO0
          _ = ENNReal.ofReal (v n ω) + Om n ω / (n : ENNReal) := by
              congr 1
              rw [← ENNReal.toReal_natCast n, ← ENNReal.toReal_div, ENNReal.ofReal_toReal]
              exact ENNReal.div_ne_top hfin.ne (by
                have : (1 : ENNReal) ≤ n := by exact_mod_cast hn
                exact (lt_of_lt_of_le zero_lt_one this).ne')
      · rw [not_lt, top_le_iff] at hfin
        rw [hfin, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n), add_top]
        exact le_top
    calc ∫⁻ ω, ENNReal.ofReal |x 0 t ω / t - ξ ω| ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (v n ω) + Om n ω / (n : ENNReal)) ∂P := lintegral_mono hpt
      _ = ∫⁻ ω, ENNReal.ofReal (v n ω) ∂P + ∫⁻ ω, Om n ω / (n : ENNReal) ∂P :=
          lintegral_add_left' (hvint n hn).aemeasurable.ennreal_ofReal _
      _ = w n := by
          rw [hw]
          congr 1
          exact (ofReal_integral_eq_lintegral_ofReal (hvint n hn)
            (Eventually.of_forall fun ω => by simp only [hv]; positivity)).symm
