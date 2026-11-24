-- Prove2me | solution 3 for Kyprianou.exercise2_7_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:49:33.542956+00:00
-- url     : https://prove2.me/submissions/62f18b8f-1511-4d50-94ed-8719ba563107

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3
import Theorems.Thm_Kyprianou_smallJumpLimitCadlagCorrected
import Theorems.Thm_Kyprianou_sumOfIndependentLevyProcesses
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise27Helpers

/-! ### Section 1: Basic Lévy-measure and Lévy-process utilities -/

private lemma levyMeasure_sigmaFinite {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν) :
    SigmaFinite ν := by
  let S : ℕ → Set ℝ := fun n =>
    if n = 0 then {0} else {x : ℝ | (1 : ℝ) / (n : ℝ) ≤ |x|}
  refine ⟨⟨{
    set := S
    set_mem := fun _ => trivial
    finite := fun n => by
      dsimp only [S]
      split_ifs with hn
      · rw [hν.1]; exact ENNReal.zero_lt_top
      · exact hν.measure_setOf_abs_ge_lt_top (by positivity)
    spanning := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x = 0
      · exact ⟨0, by simp [S, hx]⟩
      · have hpos : 0 < |x| := abs_pos.mpr hx
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / |x|)
        refine ⟨n + 1, ?_⟩
        simp only [S, Nat.succ_ne_zero, ↓reduceIte, Set.mem_setOf_eq]
        have h1 : 1 / |x| < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        rw [div_lt_iff₀ hpos] at h1
        rw [div_le_iff₀ (by positivity)]
        linarith
  }⟩⟩

private lemma levyMeasure_abs_gt_lt_top {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    {r : ℝ} (hr : 0 < r) : ν {x : ℝ | r < |x|} < ⊤ := by
  have hsub : {x : ℝ | r < |x|} ⊆ {x : ℝ | r ≤ |x|} := fun x hx => le_of_lt (Set.mem_setOf.mp hx)
  exact lt_of_le_of_lt (measure_mono hsub) (hν.measure_setOf_abs_ge_lt_top hr)

private lemma levyProcess_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : ProbabilityTheory.IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (X t) P := by
  have h := (hX.stationary_increments 0 t).aemeasurable_snd
  have heq : ProbabilityTheory.increment X 0 t = X t := by
    funext ω; simp [ProbabilityTheory.increment, hX.start_zero]
  rwa [heq] at h

private lemma levyProcess_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : ProbabilityTheory.IsLevyProcess X P) (q : ℝ≥0) :
    ProbabilityTheory.IsLevyProcess (fun u ω => X (q + u) ω - X q ω) P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (fun ω => X (q + t) ω - X q ω)) ξ = charFun (P.map (X t)) ξ := by
  let Y : ℝ≥0 → Ω → ℝ := fun u ω => X (q + u) ω - X q ω
  have hinc : ∀ u v : ℝ≥0, ProbabilityTheory.increment Y u v =
      ProbabilityTheory.increment X (q + u) (q + v) := by
    intro u v; funext ω; simp [Y, ProbabilityTheory.increment]
  have hY : ProbabilityTheory.IsLevyProcess Y P := {
    start_zero := by funext ω; simp [Y]
    indep_increments := by
      intro n t ht
      have hmono : Monotone (fun k : Fin (n + 1) => q + t k) := fun i j hij =>
        add_le_add_right (ht hij) q
      have h := hX.indep_increments n (fun k => q + t k) hmono
      have hfun : (fun k : Fin n => ProbabilityTheory.increment Y (t k.castSucc) (t k.succ)) =
          (fun k : Fin n => ProbabilityTheory.increment X (q + t k.castSucc) (q + t k.succ)) := by
        funext k; exact hinc _ _
      rwa [hfun]
    stationary_increments := by
      intro s h
      rw [hinc s (s + h), hinc 0 h, add_zero, ← add_assoc]
      exact (hX.stationary_increments (q + s) h).trans (hX.stationary_increments q h).symm
    cadlag_ae := by
      filter_upwards [hX.cadlag_ae] with ω hω u
      have hadd_cont : Continuous (fun v : ℝ≥0 => q + v) := continuous_const.add continuous_id
      constructor
      · have h1 := (hω (q + u)).1
        have hmap : Tendsto (fun v : ℝ≥0 => q + v) (nhdsWithin u (Set.Ici u))
            (nhdsWithin (q + u) (Set.Ici (q + u))) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨(hadd_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
          filter_upwards [self_mem_nhdsWithin] with v hv
          exact add_le_add_right hv q
        exact (h1.tendsto.comp hmap).sub tendsto_const_nhds
      · obtain ⟨l, hl⟩ := (hω (q + u)).2
        refine ⟨l - X q ω, ?_⟩
        have hmap : Tendsto (fun v : ℝ≥0 => q + v) (nhdsWithin u (Set.Iio u))
            (nhdsWithin (q + u) (Set.Iio (q + u))) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨(hadd_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
          filter_upwards [self_mem_nhdsWithin] with v hv
          exact add_lt_add_right hv q
        exact (hl.comp hmap).sub tendsto_const_nhds
  }
  refine ⟨hY, fun t ξ => ?_⟩
  have hid := hX.stationary_increments q t
  have heq : ProbabilityTheory.increment X 0 t = X t := by
    funext ω; simp [ProbabilityTheory.increment, hX.start_zero]
  rw [heq] at hid
  change charFun (P.map (ProbabilityTheory.increment X q (q + t))) ξ = charFun (P.map (X t)) ξ
  rw [hid.map_eq]

private lemma norm_exp_I_mul_sub_one_sub_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ θ ^ 2 / 2 := by
  have h1 : ∀ t : ℝ, ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
    intro t
    have hderiv : ∀ x : ℝ, HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I))
        (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := fun x => by
      have hmul : HasDerivAt (fun r : ℝ => (r : ℂ) * Complex.I) Complex.I x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
      simpa using hmul.cexp
    have hbound : ∀ x ∈ convexHull ℝ ({0, t} : Set ℝ),
        ‖Complex.exp ((x : ℂ) * Complex.I) * Complex.I‖ ≤ 1 := fun x _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I))
      (f' := fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I) * Complex.I)
      (s := convexHull ℝ ({0, t} : Set ℝ))
      (fun x _ => (hderiv x).hasDerivWithinAt) hbound (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (by simp : (0 : ℝ) ∈ ({0, t} : Set ℝ)))
      (subset_convexHull ℝ _ (by simp : t ∈ ({0, t} : Set ℝ)))
    simpa [Real.norm_eq_abs] using hmvt
  have hnonneg : ∀ r : ℝ, 0 ≤ r →
      ‖Complex.exp ((r : ℂ) * Complex.I) - 1 - (r : ℂ) * Complex.I‖ ≤ r ^ 2 / 2 := by
    intro r hr
    have hFTC : Complex.exp ((r : ℂ) * Complex.I) - 1 - (r : ℂ) * Complex.I =
        ∫ s in (0 : ℝ)..r, (Complex.exp ((s : ℂ) * Complex.I) - 1) * Complex.I := by
      let F : ℝ → ℂ := fun u => Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I
      have hFderiv : ∀ x ∈ Set.uIcc (0 : ℝ) r,
          HasDerivAt F ((Complex.exp ((x : ℂ) * Complex.I) - 1) * Complex.I) x := fun x _ => by
        have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
        have hd : HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I)
            (Complex.exp ((x : ℂ) * Complex.I) * Complex.I - Complex.I) x :=
          (hmul.cexp.sub_const 1).sub hmul
        have heq : Complex.exp ((x : ℂ) * Complex.I) * Complex.I - Complex.I =
            (Complex.exp ((x : ℂ) * Complex.I) - 1) * Complex.I := by ring
        rwa [heq] at hd
      have hcont : Continuous (fun s : ℝ => (Complex.exp ((s : ℂ) * Complex.I) - 1) * Complex.I) :=
        ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).sub
          continuous_const).mul continuous_const
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv
        (hcont.intervalIntegrable 0 r)
      simpa [F] using hint.symm
    rw [hFTC]
    have hle := intervalIntegral.norm_integral_le_of_norm_le hr
      (μ := volume)
      (f := fun s : ℝ => (Complex.exp ((s : ℂ) * Complex.I) - 1) * Complex.I)
      (g := fun s : ℝ => s)
      (Eventually.of_forall fun s hs => by
        rw [norm_mul, Complex.norm_I, mul_one]
        exact (h1 s).trans (by rw [abs_of_pos hs.1]))
      (continuous_id.intervalIntegrable 0 r)
    have hint_id : ∫ s in (0 : ℝ)..r, s = r ^ 2 / 2 := by
      rw [integral_id]; ring
    linarith
  by_cases h0 : 0 ≤ θ
  · exact hnonneg θ h0
  · have hneg : 0 ≤ -θ := by linarith
    have hconj : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I) =
        Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 1 - ((-θ : ℝ) : ℂ) * Complex.I := by
      simp [← Complex.exp_conj]
    have hnorm_eq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ =
        ‖Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 1 - ((-θ : ℝ) : ℂ) * Complex.I‖ := by
      rw [← hconj, RCLike.norm_conj]
    rw [hnorm_eq]
    simpa [neg_sq] using hnonneg (-θ) hneg

private lemma norm_levyCompensatedIntegrand_le (ξ x : ℝ) :
    ‖ProbabilityTheory.levyCompensatedIntegrand ξ x‖ ≤
      max 2 (ξ ^ 2 / 2) * min 1 (x ^ 2) := by
  unfold ProbabilityTheory.levyCompensatedIntegrand
  by_cases hx : |x| < 1
  · rw [if_pos hx, mul_one]
    have h1 : ‖Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I‖ ≤ (x * ξ) ^ 2 / 2 := by
      have hcast : ((x * ξ : ℝ) : ℂ) * Complex.I = (x : ℂ) * (ξ : ℂ) * Complex.I := by push_cast; rfl
      rw [← hcast]
      exact norm_exp_I_mul_sub_one_sub_le (x * ξ)
    have hxsq : x ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (abs_nonneg x) hx.le 2
      simpa [sq_abs] using this
    rw [min_eq_right hxsq]
    have hle : (x * ξ) ^ 2 / 2 = (ξ ^ 2 / 2) * x ^ 2 := by ring
    rw [hle] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x))
  · rw [if_neg hx, mul_zero, sub_zero]
    have hge : 1 ≤ |x| := le_of_not_gt hx
    have hxsq : 1 ≤ x ^ 2 := by
      have := pow_le_pow_left₀ zero_le_one hge 2
      simpa [sq_abs] using this
    rw [min_eq_left hxsq, mul_one]
    calc ‖Complex.exp (↑x * ↑ξ * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑x * ↑ξ * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          have hcast : (x : ℂ) * (ξ : ℂ) * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by
            push_cast; rfl
          rw [hcast, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
      _ ≤ max 2 (ξ ^ 2 / 2) := le_max_left _ _

private lemma integrable_levyCompensatedIntegrand {ν : Measure ℝ}
    (hν : ProbabilityTheory.IsLevyMeasure ν) (ξ : ℝ) :
    Integrable (ProbabilityTheory.levyCompensatedIntegrand ξ) ν := by
  have hmeas : Measurable (ProbabilityTheory.levyCompensatedIntegrand ξ) := by
    unfold ProbabilityTheory.levyCompensatedIntegrand
    have h1 : Measurable (fun x : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I)) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.mul measurable_const).mul measurable_const)
    have h2 : Measurable (fun x : ℝ => if |x| < 1 then (1 : ℂ) else 0) :=
      Measurable.ite (continuous_abs.measurable measurableSet_Iio) measurable_const measurable_const
    exact (h1.sub measurable_const).sub
      (((Complex.continuous_ofReal.measurable.mul measurable_const).mul measurable_const).mul h2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  let C : ℝ := max 2 (ξ ^ 2 / 2)
  have hCnn : 0 ≤ C := le_trans (by norm_num) (le_max_left _ _)
  have hle : ∀ x : ℝ, ‖ProbabilityTheory.levyCompensatedIntegrand ξ x‖ₑ ≤
      ENNReal.ofReal C * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
    rw [← ENNReal.ofReal_mul hCnn, enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (norm_levyCompensatedIntegrand_le ξ x)
  calc ∫⁻ x, ‖ProbabilityTheory.levyCompensatedIntegrand ξ x‖ₑ ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := lintegral_mono hle
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
          (measurable_const.min (measurable_id.pow_const 2)))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2

private lemma levyTripleExponent_re_le (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (ξ : ℝ) :
    (Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ).re ≤
      -((σ : ℝ) ^ 2 * ξ ^ 2 / 2) := by
  unfold Kyprianou.Ch01.levyTripleExponent
  have hint : Integrable (ProbabilityTheory.levyCompensatedIntegrand ξ) ν :=
    integrable_levyCompensatedIntegrand hν ξ
  have hre_int : (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν).re =
      ∫ x, (ProbabilityTheory.levyCompensatedIntegrand ξ x).re ∂ν :=
    (Complex.reCLM.integral_comp_comm hint).symm
  have hre_nonpos : ∫ x, (ProbabilityTheory.levyCompensatedIntegrand ξ x).re ∂ν ≤ 0 := by
    refine integral_nonpos fun x => ?_
    unfold ProbabilityTheory.levyCompensatedIntegrand
    have hcast : (x : ℂ) * (ξ : ℂ) * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; rfl
    rw [hcast]
    by_cases hx : |x| < 1
    · rw [if_pos hx, mul_one]
      change (Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I).re ≤ 0
      simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re,
        Complex.mul_I_re, Complex.ofReal_im, neg_zero, sub_zero]
      linarith [Real.cos_le_one (x * ξ)]
    · rw [if_neg hx, mul_zero, sub_zero]
      change (Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1).re ≤ 0
      simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
      linarith [Real.cos_le_one (x * ξ)]
  simp only [Complex.add_re, Complex.sub_re, Complex.I_mul_re, Complex.ofReal_im,
    Complex.ofReal_re, NNReal.coe_pow]
  rw [hre_int]
  linarith

/-! ### Section 2: Càdlàg countable jump characterization and null-measurability -/

private def jumpEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (threshold : ℝ) : Set Ω :=
  {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
    ∃ l : ℝ, Tendsto (fun u => X u ω) (nhdsWithin s (Set.Iio s)) (nhds l) ∧
      threshold < |X s ω - l|}

private def denseGrid (t : ℝ≥0) : Set ℝ≥0 :=
  {q : ℝ≥0 | (∃ r : ℚ, (r : ℝ) = (q : ℝ)) ∧ q ≤ t} ∪ {t}

private lemma denseGrid_countable (t : ℝ≥0) : (denseGrid t).Countable := by
  refine Set.Countable.union ?_ (Set.countable_singleton t)
  have hsub : {q : ℝ≥0 | (∃ r : ℚ, (r : ℝ) = (q : ℝ)) ∧ q ≤ t} ⊆
      Set.range (fun r : ℚ => Real.toNNReal (r : ℝ)) := by
    rintro q ⟨⟨r, hr⟩, _⟩
    refine ⟨r, ?_⟩
    ext
    simp [hr]
  exact (Set.countable_range _).mono hsub

private lemma cadlag_jump_iff_grid {f : ℝ≥0 → ℝ} (hf : ProbabilityTheory.IsCadlag f)
    (t : ℝ≥0) {threshold : ℝ} (hthresh : 0 < threshold) :
    (∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
      ∃ l : ℝ, Tendsto f (nhdsWithin s (Set.Iio s)) (nhds l) ∧ threshold < |f s - l|) ↔
    (∃ k : ℕ, ∀ m : ℕ, ∃ q₁ ∈ denseGrid t, ∃ q₂ ∈ denseGrid t,
      0 < (q₂ : ℝ) - (q₁ : ℝ) ∧ (q₂ : ℝ) - (q₁ : ℝ) < 1 / ((m : ℝ) + 1) ∧
        threshold + 1 / ((k : ℝ) + 1) < |f q₂ - f q₁|) := by
  constructor
  · rintro ⟨s, hs0, hst, l, hl, hjump⟩
    have hgap : 0 < |f s - l| - threshold := sub_pos.mpr hjump
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / (|f s - l| - threshold))
    have hk_bound : 2 / ((k : ℝ) + 1) < |f s - l| - threshold := by
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h1 : 2 / (|f s - l| - threshold) < (k : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hgap] at h1
      rw [div_lt_iff₀ hpos]
      linarith
    refine ⟨k, fun m => ?_⟩
    let δ : ℝ := 1 / (2 * ((k : ℝ) + 1))
    have hδ : 0 < δ := by positivity
    let η : ℝ := 1 / (2 * ((m : ℝ) + 1))
    have hη : 0 < η := by positivity
    -- Pick rational `q₁ < s` close to `s` with `|f q₁ - l| < δ`
    have hl_ev := (Metric.tendsto_nhds.mp hl δ hδ)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hl_ev
    obtain ⟨r₁, hr₁, hball₁⟩ := hl_ev
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
    let a₁ : ℝ := max 0 (max ((s : ℝ) - η) ((s : ℝ) - r₁))
    have ha₁_lt : a₁ < (s : ℝ) := max_lt hs_pos (max_lt (by linarith) (by linarith))
    obtain ⟨rat₁, hrat₁_gt, hrat₁_lt⟩ := exists_rat_btwn ha₁_lt
    have hrat₁_nn : 0 ≤ (rat₁ : ℝ) := le_trans (le_max_left _ _) hrat₁_gt.le
    let q₁ : ℝ≥0 := ⟨(rat₁ : ℝ), hrat₁_nn⟩
    have hq₁_lt_s : q₁ < s := by exact_mod_cast hrat₁_lt
    have hq₁_grid : q₁ ∈ denseGrid t := Or.inl ⟨⟨rat₁, rfl⟩, hq₁_lt_s.le.trans hst⟩
    have hq₁_close : |f q₁ - l| < δ := by
      have hdist : dist q₁ s < r₁ := by
        rw [NNReal.dist_eq]
        change |(rat₁ : ℝ) - (s : ℝ)| < r₁
        rw [abs_of_neg (sub_neg.mpr hrat₁_lt)]
        have : (s : ℝ) - r₁ < (rat₁ : ℝ) := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hrat₁_gt
        linarith
      simpa [Real.dist_eq] using hball₁ hdist hq₁_lt_s
    have hq₁_dist_s : (s : ℝ) - (q₁ : ℝ) < η := by
      have : (s : ℝ) - η < (rat₁ : ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hrat₁_gt
      change (s : ℝ) - (rat₁ : ℝ) < η
      linarith
    -- Pick `q₂ ∈ denseGrid t` with `s ≤ q₂`, `q₂ - s < η`, and `|f q₂ - f s| < δ`
    have hq₂_ex : ∃ q₂ ∈ denseGrid t, s ≤ q₂ ∧ (q₂ : ℝ) - (s : ℝ) < η ∧ |f q₂ - f s| < δ := by
      by_cases hst_eq : s = t
      · subst hst_eq
        refine ⟨s, Or.inr rfl, le_rfl, by simpa using hη, by simpa using hδ⟩
      · have hs_lt_t : (s : ℝ) < (t : ℝ) := by exact_mod_cast lt_of_le_of_ne hst hst_eq
        have hr_ev := Metric.tendsto_nhds.mp (hf s).1.tendsto δ hδ
        rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hr_ev
        obtain ⟨r₂, hr₂, hball₂⟩ := hr_ev
        let b₂ : ℝ := min (t : ℝ) (min ((s : ℝ) + η) ((s : ℝ) + r₂))
        have hs_lt_b₂ : (s : ℝ) < b₂ := lt_min hs_lt_t (lt_min (by linarith) (by linarith))
        obtain ⟨rat₂, hrat₂_gt, hrat₂_lt⟩ := exists_rat_btwn hs_lt_b₂
        have hrat₂_nn : 0 ≤ (rat₂ : ℝ) := le_trans s.coe_nonneg hrat₂_gt.le
        let q₂ : ℝ≥0 := ⟨(rat₂ : ℝ), hrat₂_nn⟩
        have hq₂_ge_s : s ≤ q₂ := by exact_mod_cast hrat₂_gt.le
        have hq₂_le_t : q₂ ≤ t := by
          exact_mod_cast (hrat₂_lt.le.trans (min_le_left _ _))
        have hq₂_grid : q₂ ∈ denseGrid t := Or.inl ⟨⟨rat₂, rfl⟩, hq₂_le_t⟩
        have hq₂_close : |f q₂ - f s| < δ := by
          have hdist : dist q₂ s < r₂ := by
            rw [NNReal.dist_eq]
            change |(rat₂ : ℝ) - (s : ℝ)| < r₂
            rw [abs_of_pos (sub_pos.mpr hrat₂_gt)]
            have : (rat₂ : ℝ) < (s : ℝ) + r₂ := lt_of_lt_of_le hrat₂_lt ((min_le_right _ _).trans (min_le_right _ _))
            linarith
          simpa [Real.dist_eq] using hball₂ hdist hq₂_ge_s
        have hq₂_dist : (q₂ : ℝ) - (s : ℝ) < η := by
          have : (rat₂ : ℝ) < (s : ℝ) + η := lt_of_lt_of_le hrat₂_lt ((min_le_right _ _).trans (min_le_left _ _))
          change (rat₂ : ℝ) - (s : ℝ) < η
          linarith
        exact ⟨q₂, hq₂_grid, hq₂_ge_s, hq₂_dist, hq₂_close⟩
    obtain ⟨q₂, hq₂_grid, hq₂_ge_s, hq₂_dist, hq₂_close⟩ := hq₂_ex
    refine ⟨q₁, hq₁_grid, q₂, hq₂_grid, ?_, ?_, ?_⟩
    · have : (q₁ : ℝ) < (s : ℝ) := hrat₁_lt
      have : (s : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂_ge_s
      linarith
    · have h2η : η + η = 1 / ((m : ℝ) + 1) := by dsimp only [η]; field_simp; ring
      linarith
    · have htri : |f s - l| ≤ |f s - f q₂| + |f q₂ - f q₁| + |f q₁ - l| := by
        have heq : f s - l = (f s - f q₂) + (f q₂ - f q₁) + (f q₁ - l) := by ring
        rw [heq]
        calc |(f s - f q₂) + (f q₂ - f q₁) + (f q₁ - l)|
            ≤ |(f s - f q₂) + (f q₂ - f q₁)| + |f q₁ - l| := abs_add_le _ _
          _ ≤ |f s - f q₂| + |f q₂ - f q₁| + |f q₁ - l| := by
              linarith [abs_add_le (f s - f q₂) (f q₂ - f q₁)]
      rw [abs_sub_comm (f s) (f q₂)] at htri
      have h2δ : 2 * δ = 1 / ((k : ℝ) + 1) := by dsimp only [δ]; field_simp
      have h4δ : 2 / ((k : ℝ) + 1) = 4 * δ := by dsimp only [δ]; field_simp; ring
      linarith
  · rintro ⟨k, hk⟩
    choose q₁ hq₁_mem q₂ hq₂_mem hpos hlt hjump using hk
    have hq₁_le : ∀ m : ℕ, q₁ m ∈ Set.Icc (0 : ℝ≥0) t := fun m => by
      refine ⟨zero_le', ?_⟩
      rcases hq₁_mem m with ⟨_, hle⟩ | rfl
      · exact hle
      · exact le_rfl
    obtain ⟨s, hs_mem, φ, hφ_mono, hφ_tend⟩ :=
      (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).tendsto_subseq hq₁_le
    -- Also `q₂ (φ n) → s`
    have hq₂_tend : Tendsto (fun n => q₂ (φ n)) atTop (nhds s) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h1 := Metric.tendsto_nhds.mp hφ_tend (ε / 2) (by linarith)
      have hinv : Tendsto (fun n : ℕ => 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (nhds 0) := by
        have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
          simpa [one_div, Function.comp_def] using
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact h0.comp hφ_mono.tendsto_atTop
      have h2 := hinv.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
      filter_upwards [h1, h2] with n hn1 hn2
      have hdiff : dist (q₂ (φ n)) (q₁ (φ n)) < ε / 2 := by
        rw [NNReal.dist_eq, abs_of_pos (hpos (φ n))]
        exact (hlt (φ n)).trans hn2
      have hn1' : dist (q₁ (φ n)) s < ε / 2 := hn1
      exact lt_of_le_of_lt (dist_triangle _ (q₁ (φ n)) _) (by linarith)
    -- Show eventually `q₁ (φ n) < s` and `s ≤ q₂ (φ n)`
    obtain ⟨l, hl⟩ := (hf s).2
    have hnot_freq_ge : ¬ ∃ᶠ n in atTop, s ≤ q₁ (φ n) := by
      intro hfreq
      obtain ⟨ψ, hψ_mono, hψ⟩ := Filter.extraction_of_frequently_atTop hfreq
      have h1 : Tendsto (fun n => f (q₁ (φ (ψ n)))) atTop (nhds (f s)) := by
        have hsub : Tendsto (fun n => q₁ (φ (ψ n))) atTop (nhdsWithin s (Set.Ici s)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hφ_tend.comp hψ_mono.tendsto_atTop) (Eventually.of_forall hψ)
        exact (hf s).1.tendsto.comp hsub
      have h2 : Tendsto (fun n => f (q₂ (φ (ψ n)))) atTop (nhds (f s)) := by
        have hsub : Tendsto (fun n => q₂ (φ (ψ n))) atTop (nhdsWithin s (Set.Ici s)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hq₂_tend.comp hψ_mono.tendsto_atTop) (Eventually.of_forall fun n => by
              have hlt' : (q₁ (φ (ψ n)) : ℝ) < (q₂ (φ (ψ n)) : ℝ) := sub_pos.mp (hpos (φ (ψ n)))
              exact (hψ n).trans (by exact_mod_cast hlt'.le))
        exact (hf s).1.tendsto.comp hsub
      have hdiff0 : Tendsto (fun n => |f (q₂ (φ (ψ n))) - f (q₁ (φ (ψ n)))|) atTop (nhds 0) := by
        simpa [Function.comp_def] using continuous_abs.continuousAt.tendsto.comp (h2.sub h1)
      have hge : threshold + 1 / ((k : ℝ) + 1) ≤ 0 :=
        ge_of_tendsto hdiff0 (Eventually.of_forall fun n => (hjump (φ (ψ n))).le)
      have hpos' : 0 < threshold + 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hnot_freq_lt : ¬ ∃ᶠ n in atTop, q₂ (φ n) < s := by
      intro hfreq
      obtain ⟨ψ, hψ_mono, hψ⟩ := Filter.extraction_of_frequently_atTop hfreq
      have h1 : Tendsto (fun n => f (q₁ (φ (ψ n)))) atTop (nhds l) := by
        have hsub : Tendsto (fun n => q₁ (φ (ψ n))) atTop (nhdsWithin s (Set.Iio s)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hφ_tend.comp hψ_mono.tendsto_atTop) (Eventually.of_forall fun n => by
              have hlt' : (q₁ (φ (ψ n)) : ℝ) < (q₂ (φ (ψ n)) : ℝ) := sub_pos.mp (hpos (φ (ψ n)))
              exact lt_trans (by exact_mod_cast hlt') (hψ n))
        exact hl.comp hsub
      have h2 : Tendsto (fun n => f (q₂ (φ (ψ n)))) atTop (nhds l) := by
        have hsub : Tendsto (fun n => q₂ (φ (ψ n))) atTop (nhdsWithin s (Set.Iio s)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hq₂_tend.comp hψ_mono.tendsto_atTop) (Eventually.of_forall hψ)
        exact hl.comp hsub
      have hdiff0 : Tendsto (fun n => |f (q₂ (φ (ψ n))) - f (q₁ (φ (ψ n)))|) atTop (nhds 0) := by
        simpa [Function.comp_def] using continuous_abs.continuousAt.tendsto.comp (h2.sub h1)
      have hge : threshold + 1 / ((k : ℝ) + 1) ≤ 0 :=
        ge_of_tendsto hdiff0 (Eventually.of_forall fun n => (hjump (φ (ψ n))).le)
      have hpos' : 0 < threshold + 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hev₁ : ∀ᶠ n in atTop, q₁ (φ n) < s := by
      simpa [Filter.not_frequently] using hnot_freq_ge
    have hev₂ : ∀ᶠ n in atTop, s ≤ q₂ (φ n) := by
      simpa [Filter.not_frequently] using hnot_freq_lt
    obtain ⟨n₀, hn₀⟩ := hev₁.exists
    have hs_pos : 0 < s := lt_of_le_of_lt zero_le' hn₀
    have hf₁ : Tendsto (fun n => f (q₁ (φ n))) atTop (nhds l) :=
      hl.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_tend hev₁)
    have hf₂ : Tendsto (fun n => f (q₂ (φ n))) atTop (nhds (f s)) :=
      (hf s).1.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq₂_tend hev₂)
    have hlim : Tendsto (fun n => |f (q₂ (φ n)) - f (q₁ (φ n))|) atTop (nhds |f s - l|) :=
      continuous_abs.continuousAt.tendsto.comp (hf₂.sub hf₁)
    have hle : threshold + 1 / ((k : ℝ) + 1) ≤ |f s - l| :=
      ge_of_tendsto hlim (Eventually.of_forall fun n => (hjump (φ n)).le)
    have hlt_jump : threshold < |f s - l| := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact ⟨s, hs_pos, hs_mem.2, l, hl, hlt_jump⟩

private def gridJumpSet (t : ℝ≥0) (threshold : ℝ) : Set (denseGrid t → ℝ) :=
  ⋃ k : ℕ, ⋂ m : ℕ, ⋃ (q₁ : denseGrid t), ⋃ (q₂ : denseGrid t),
    if 0 < (q₂.1 : ℝ) - (q₁.1 : ℝ) ∧ (q₂.1 : ℝ) - (q₁.1 : ℝ) < 1 / ((m : ℝ) + 1) then
      {g : denseGrid t → ℝ | threshold + 1 / ((k : ℝ) + 1) < |g q₂ - g q₁|}
    else ∅

private lemma gridJumpSet_measurableSet (t : ℝ≥0) (threshold : ℝ) :
    MeasurableSet (gridJumpSet t threshold) := by
  haveI : Countable (denseGrid t) := (denseGrid_countable t).to_subtype
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun m =>
    MeasurableSet.iUnion fun q₁ => MeasurableSet.iUnion fun q₂ => ?_
  split_ifs
  · have hmeas : Measurable (fun g : denseGrid t → ℝ => |g q₂ - g q₁|) :=
      continuous_abs.measurable.comp ((measurable_pi_apply q₂).sub (measurable_pi_apply q₁))
    exact hmeas measurableSet_Ioi
  · exact MeasurableSet.empty

private lemma jumpEvent_ae_eq_preimage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) {threshold : ℝ} (hthresh : 0 < threshold) :
    jumpEvent X t threshold =ᵐ[P]
      (fun ω (q : denseGrid t) => X q.1 ω) ⁻¹' gridJumpSet t threshold := by
  filter_upwards [hX.cadlag_ae] with ω hω
  change (ω ∈ jumpEvent X t threshold) = (ω ∈ (fun ω (q : denseGrid t) => X q.1 ω) ⁻¹' gridJumpSet t threshold)
  apply propext
  rw [jumpEvent, Set.mem_setOf_eq, cadlag_jump_iff_grid hω t hthresh]
  simp only [Set.mem_preimage, gridJumpSet, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun m => ?_⟩
    obtain ⟨q₁, hq₁, q₂, hq₂, hpos, hlt, hj⟩ := hk m
    refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, ?_⟩
    rw [if_pos ⟨hpos, hlt⟩]
    exact hj
  · rintro ⟨k, hk⟩
    refine ⟨k, fun m => ?_⟩
    obtain ⟨q₁, q₂, h⟩ := hk m
    by_cases hcond : 0 < (q₂.1 : ℝ) - (q₁.1 : ℝ) ∧ (q₂.1 : ℝ) - (q₁.1 : ℝ) < 1 / ((m : ℝ) + 1)
    · rw [if_pos hcond] at h
      exact ⟨q₁.1, q₁.2, q₂.1, q₂.2, hcond.1, hcond.2, h⟩
    · rw [if_neg hcond] at h
      exact absurd h (Set.notMem_empty _)

private lemma jumpEvent_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) {threshold : ℝ} (hthresh : 0 < threshold) :
    NullMeasurableSet (jumpEvent X t threshold) P := by
  have : Countable (denseGrid t) := (denseGrid_countable t).to_subtype
  have hae : AEMeasurable (fun ω (q : denseGrid t) => X q.1 ω) P :=
    aemeasurable_pi_iff.mpr fun q => levyProcess_aemeasurable hX q.1
  have hnm : NullMeasurableSet
      ((fun ω (q : denseGrid t) => X q.1 ω) ⁻¹' gridJumpSet t threshold) P :=
    ⟨hae.mk _ ⁻¹' gridJumpSet t threshold,
     hae.measurable_mk (gridJumpSet_measurableSet t threshold),
     by
       filter_upwards [hae.ae_eq_mk] with ω hω
       change (ω ∈ (fun ω (q : denseGrid t) => X q.1 ω) ⁻¹' gridJumpSet t threshold) =
         (ω ∈ hae.mk _ ⁻¹' gridJumpSet t threshold)
       simp only [Set.mem_preimage, hω]⟩
  exact hnm.congr (jumpEvent_ae_eq_preimage hX t hthresh).symm

/-! ### Law invariance of Lévy processes on countable grids -/

private lemma fin_process_eq_psum_increments {Ω : Type*} {n : ℕ}
    (t : Fin n → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX0 : X 0 = fun _ => 0) :
    let s : Fin (n + 1) → ℝ≥0 := fun k => if h : k.1 = 0 then 0 else t ⟨k.1 - 1, by omega⟩
    let psum : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ i.1), v k
    (fun ω (i : Fin n) => X (t i) ω) =
      psum ∘ (fun ω (k : Fin n) => ProbabilityTheory.increment X (s k.castSucc) (s k.succ) ω) := by
  intro s psum
  funext ω i
  simp only [Function.comp_apply, psum]
  have hsum : ∀ m (hm : m < n),
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ m),
        ProbabilityTheory.increment X (s k.castSucc) (s k.succ) ω) =
        X (t ⟨m, hm⟩) ω := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hfilt : Finset.univ.filter (fun k : Fin n => k.1 ≤ 0) = {⟨0, hm⟩} := by
        ext k; simp [Fin.ext_iff]
      rw [hfilt, Finset.sum_singleton]
      have hs0 : s (⟨0, hm⟩ : Fin n).castSucc = 0 := by simp [s]
      have hs1 : s (⟨0, hm⟩ : Fin n).succ = t ⟨0, hm⟩ := by simp [s]
      simp only [ProbabilityTheory.increment, hs0, hs1, hX0, sub_zero]
    | succ m ih =>
      intro hm
      have hfilt : Finset.univ.filter (fun k : Fin n => k.1 ≤ m + 1) =
          insert ⟨m + 1, hm⟩ (Finset.univ.filter (fun k : Fin n => k.1 ≤ m)) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m + 1, hm⟩ : Fin n) ∉ Finset.univ.filter (fun k : Fin n => k.1 ≤ m) := by
        simp
      rw [hfilt, Finset.sum_insert hnotmem, ih (Nat.lt_of_succ_lt hm)]
      have hs1 : s (⟨m + 1, hm⟩ : Fin n).castSucc = t ⟨m, Nat.lt_of_succ_lt hm⟩ := by
        simp [s]
      have hs2 : s (⟨m + 1, hm⟩ : Fin n).succ = t ⟨m + 1, hm⟩ := by
        simp [s]
      simp only [ProbabilityTheory.increment, hs1, hs2]
      ring
  exact (hsum i.1 i.2).symm

private lemma levyProcess_fin_map_eq
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ℝ≥0 → Ω₁ → ℝ} {X₂ : ℝ≥0 → Ω₂ → ℝ}
    (hX₁ : ProbabilityTheory.IsLevyProcess X₁ P₁)
    (hX₂ : ProbabilityTheory.IsLevyProcess X₂ P₂)
    (hmarg : ∀ t : ℝ≥0, P₁.map (X₁ t) = P₂.map (X₂ t))
    (n : ℕ) (t : Fin n → ℝ≥0) (ht : Monotone t) :
    P₁.map (fun ω (i : Fin n) => X₁ (t i) ω) =
      P₂.map (fun ω (i : Fin n) => X₂ (t i) ω) := by
  let s : Fin (n + 1) → ℝ≥0 := fun k =>
    if h : k.1 = 0 then 0 else t ⟨k.1 - 1, by omega⟩
  have hs_mono : Monotone s := by
    intro i j hij
    dsimp only [s]
    split_ifs with hi hj
    · exact le_rfl
    · exact zero_le'
    · exfalso; have : i.1 ≤ j.1 := hij; omega
    · exact ht (by show i.1 - 1 ≤ j.1 - 1; have : i.1 ≤ j.1 := hij; omega)
  let inc₁ : Fin n → Ω₁ → ℝ := fun k => ProbabilityTheory.increment X₁ (s k.castSucc) (s k.succ)
  let inc₂ : Fin n → Ω₂ → ℝ := fun k => ProbabilityTheory.increment X₂ (s k.castSucc) (s k.succ)
  have hinc_aem₁ : ∀ k : Fin n, AEMeasurable (inc₁ k) P₁ := fun k =>
    (levyProcess_aemeasurable hX₁ (s k.succ)).sub (levyProcess_aemeasurable hX₁ (s k.castSucc))
  have hinc_aem₂ : ∀ k : Fin n, AEMeasurable (inc₂ k) P₂ := fun k =>
    (levyProcess_aemeasurable hX₂ (s k.succ)).sub (levyProcess_aemeasurable hX₂ (s k.castSucc))
  have hind₁ := hX₁.indep_increments n s hs_mono
  have hind₂ := hX₂.indep_increments n s hs_mono
  have hinc_map : ∀ k : Fin n, P₁.map (inc₁ k) = P₂.map (inc₂ k) := fun k => by
    have hle : s k.castSucc ≤ s k.succ := hs_mono (Fin.castSucc_le_succ k)
    let δ : ℝ≥0 := s k.succ - s k.castSucc
    have hadd : s k.castSucc + δ = s k.succ := add_tsub_cancel_of_le hle
    have h1 := (hX₁.stationary_increments (s k.castSucc) δ).map_eq
    have h2 := (hX₂.stationary_increments (s k.castSucc) δ).map_eq
    have h01 : ProbabilityTheory.increment X₁ 0 δ = X₁ δ := by
      funext ω; simp [ProbabilityTheory.increment, hX₁.start_zero]
    have h02 : ProbabilityTheory.increment X₂ 0 δ = X₂ δ := by
      funext ω; simp [ProbabilityTheory.increment, hX₂.start_zero]
    rw [hadd, h01] at h1
    rw [hadd, h02] at h2
    change P₁.map (ProbabilityTheory.increment X₁ (s k.castSucc) (s k.succ)) =
      P₂.map (ProbabilityTheory.increment X₂ (s k.castSucc) (s k.succ))
    rw [h1, h2, hmarg δ]
  have hpi_eq : P₁.map (fun ω k => inc₁ k ω) = P₂.map (fun ω k => inc₂ k ω) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hinc_aem₁).mp hind₁,
      (iIndepFun_iff_map_fun_eq_pi_map hinc_aem₂).mp hind₂]
    congr 1; funext k; exact hinc_map k
  let psum : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ i.1), v k
  have hpsum_meas : Measurable psum :=
    measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun k _ => measurable_pi_apply k
  have htele₁ := fin_process_eq_psum_increments t X₁ hX₁.start_zero
  have htele₂ := fin_process_eq_psum_increments t X₂ hX₂.start_zero
  rw [htele₁, htele₂,
    ← AEMeasurable.map_map_of_aemeasurable hpsum_meas.aemeasurable (aemeasurable_pi_iff.mpr hinc_aem₁),
    ← AEMeasurable.map_map_of_aemeasurable hpsum_meas.aemeasurable (aemeasurable_pi_iff.mpr hinc_aem₂),
    hpi_eq]

private lemma levyProcess_countable_map_eq
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ℝ≥0 → Ω₁ → ℝ} {X₂ : ℝ≥0 → Ω₂ → ℝ}
    (hX₁ : ProbabilityTheory.IsLevyProcess X₁ P₁)
    (hX₂ : ProbabilityTheory.IsLevyProcess X₂ P₂)
    (hmarg : ∀ t : ℝ≥0, P₁.map (X₁ t) = P₂.map (X₂ t))
    (D : Set ℝ≥0) [Countable D] :
    P₁.map (fun ω (q : D) => X₁ q.1 ω) = P₂.map (fun ω (q : D) => X₂ q.1 ω) := by
  have hae₁ : AEMeasurable (fun ω (q : D) => X₁ q.1 ω) P₁ :=
    aemeasurable_pi_iff.mpr fun q => levyProcess_aemeasurable hX₁ q.1
  have hae₂ : AEMeasurable (fun ω (q : D) => X₂ q.1 ω) P₂ :=
    aemeasurable_pi_iff.mpr fun q => levyProcess_aemeasurable hX₂ q.1
  haveI : IsProbabilityMeasure (P₁.map (fun ω (q : D) => X₁ q.1 ω)) :=
    Measure.isProbabilityMeasure_map hae₁
  haveI : IsProbabilityMeasure (P₂.map (fun ω (q : D) => X₂ q.1 ω)) :=
    Measure.isProbabilityMeasure_map hae₂
  refine Measure.ext_of_generateFrom_of_iUnion (measurableCylinders fun _ : D => ℝ)
    (fun _ => Set.univ) (generateFrom_measurableCylinders.symm)
    isPiSystem_measurableCylinders (Set.iUnion_const Set.univ)
    (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top _ _) ?_
  intro C hC
  rw [mem_measurableCylinders] at hC
  obtain ⟨S, T, hTm, rfl⟩ := hC
  -- Sort `S : Finset D` into a monotone `Fin S.card → ℝ≥0`
  let e : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let t : Fin S.card → ℝ≥0 := fun i => (e i).1.1
  have ht : Monotone t := fun i j hij => by
    change ((e i).1 : ℝ≥0) ≤ ((e j).1 : ℝ≥0)
    exact e.monotone hij
  have hfin := levyProcess_fin_map_eq hX₁ hX₂ hmarg S.card t ht
  let proj : (Fin S.card → ℝ) → (S → ℝ) := fun v x => v (e.symm x)
  have hproj_meas : Measurable proj :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (e.symm x)
  have hS_eq : P₁.map (fun ω (x : S) => X₁ x.1.1 ω) = P₂.map (fun ω (x : S) => X₂ x.1.1 ω) := by
    have hcomp₁ : (fun ω (x : S) => X₁ x.1.1 ω) = proj ∘ (fun ω i => X₁ (t i) ω) := by
      funext ω x; simp [proj, t]
    have hcomp₂ : (fun ω (x : S) => X₂ x.1.1 ω) = proj ∘ (fun ω i => X₂ (t i) ω) := by
      funext ω x; simp [proj, t]
    rw [hcomp₁, hcomp₂,
      ← AEMeasurable.map_map_of_aemeasurable hproj_meas.aemeasurable
        (aemeasurable_pi_iff.mpr fun i => levyProcess_aemeasurable hX₁ (t i)),
      ← AEMeasurable.map_map_of_aemeasurable hproj_meas.aemeasurable
        (aemeasurable_pi_iff.mpr fun i => levyProcess_aemeasurable hX₂ (t i)),
      hfin]
  have hcyl_eq : cylinder S T = (Finset.restrict (π := fun _ : D => ℝ) S) ⁻¹' T := rfl
  have hrest_meas : Measurable (Finset.restrict (π := fun _ : D => ℝ) S) :=
    Finset.measurable_restrict S
  rw [hcyl_eq, Measure.map_apply_of_aemeasurable hae₁ (hrest_meas hTm),
    Measure.map_apply_of_aemeasurable hae₂ (hrest_meas hTm)]
  have hpre₁ : (fun ω (q : D) => X₁ q.1 ω) ⁻¹' (Finset.restrict S ⁻¹' T) =
      (fun ω (x : S) => X₁ x.1.1 ω) ⁻¹' T := rfl
  have hpre₂ : (fun ω (q : D) => X₂ q.1 ω) ⁻¹' (Finset.restrict S ⁻¹' T) =
      (fun ω (x : S) => X₂ x.1.1 ω) ⁻¹' T := rfl
  rw [hpre₁, hpre₂,
    ← Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_iff.mpr fun x : S => levyProcess_aemeasurable hX₁ x.1.1) hTm,
    ← Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_iff.mpr fun x : S => levyProcess_aemeasurable hX₂ x.1.1) hTm,
    hS_eq]

private lemma levyProcess_jumpEvent_measure_eq
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ℝ≥0 → Ω₁ → ℝ} {X₂ : ℝ≥0 → Ω₂ → ℝ}
    (hX₁ : ProbabilityTheory.IsLevyProcess X₁ P₁)
    (hX₂ : ProbabilityTheory.IsLevyProcess X₂ P₂)
    (hmarg : ∀ s : ℝ≥0, P₁.map (X₁ s) = P₂.map (X₂ s))
    (t : ℝ≥0) {threshold : ℝ} (hthresh : 0 < threshold) :
    P₁ (jumpEvent X₁ t threshold) = P₂ (jumpEvent X₂ t threshold) := by
  haveI : Countable (denseGrid t) := (denseGrid_countable t).to_subtype
  rw [measure_congr (jumpEvent_ae_eq_preimage hX₁ t hthresh),
    measure_congr (jumpEvent_ae_eq_preimage hX₂ t hthresh)]
  have hae₁ : AEMeasurable (fun ω (q : denseGrid t) => X₁ q.1 ω) P₁ :=
    aemeasurable_pi_iff.mpr fun q => levyProcess_aemeasurable hX₁ q.1
  have hae₂ : AEMeasurable (fun ω (q : denseGrid t) => X₂ q.1 ω) P₂ :=
    aemeasurable_pi_iff.mpr fun q => levyProcess_aemeasurable hX₂ q.1
  rw [← Measure.map_apply_of_aemeasurable hae₁ (gridJumpSet_measurableSet t threshold),
    ← Measure.map_apply_of_aemeasurable hae₂ (gridJumpSet_measurableSet t threshold),
    levyProcess_countable_map_eq hX₁ hX₂ hmarg (denseGrid t)]

/-! ### Section 3: Part (1) (`P {∃ s ∈ (0, t], |ΔX_s| > threshold} = 1 - exp(-t * ν{|x| > threshold})`) -/

private lemma one_sub_exp_sub_mul_exp_le_half_sq {x : ℝ} (hx : 0 ≤ x) :
    1 - Real.exp (-x) - x * Real.exp (-x) ≤ x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun u => u ^ 2 / 2 - 1 + (1 + u) * Real.exp (-u)
  have hderiv : ∀ u : ℝ, HasDerivAt g (u * (1 - Real.exp (-u))) u := fun u => by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2 - 1) ((2 : ℕ) * u ^ (2 - 1) / 2) u :=
      ((hasDerivAt_pow 2 u).div_const 2).sub_const (1 : ℝ)
    have h2 : HasDerivAt (fun y : ℝ => 1 + y) (0 + 1) u :=
      (hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-u) * (-1)) u :=
      (hasDerivAt_id u).neg.exp
    have h4 := h1.add (h2.mul h3)
    have hval : (2 : ℕ) * u ^ (2 - 1) / 2 + ((0 + 1) * Real.exp (-u) + (1 + u) * (Real.exp (-u) * -1)) =
        u * (1 - Real.exp (-u)) := by norm_num; ring
    rwa [hval] at h4
  have hmono : MonotoneOn g (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
      (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt)
      (fun u hu => by
        rw [(hderiv u).deriv]
        have hu0 : 0 ≤ u := le_of_lt (by simpa [interior_Ici] using hu)
        have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        exact mul_nonneg hu0 (by linarith))
  have h0x : g 0 ≤ g x := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0] at h0x
  dsimp only [g] at h0x
  linarith

private lemma poissonMeasureENN_apply_nat (μ : ℝ≥0) (k : ℕ) :
    LevyStochCalc.Poisson.poissonMeasureENN μ {(k : ℝ≥0∞)} =
      ENNReal.ofReal (Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ k / (k.factorial : ℝ)) := by
  unfold LevyStochCalc.Poisson.poissonMeasureENN
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (k : ℝ≥0∞))]
  have hpre : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {(k : ℝ≥0∞)} = {k} := by
    ext n; simp
  rw [hpre, ProbabilityTheory.poissonMeasure, Measure.sum_apply _ (measurableSet_singleton k),
    tsum_eq_single k]
  · simp [ProbabilityTheory.poissonPMFReal]
  · intro n hn
    have hnot : n ∉ ({k} : Set ℕ) := by simpa using hn
    simp [Measure.dirac_apply' _ (measurableSet_singleton k), Set.indicator_of_notMem hnot]

private lemma poissonMeasureENN_range_compl (μ : ℝ≥0) :
    LevyStochCalc.Poisson.poissonMeasureENN μ (Set.range ((↑) : ℕ → ℝ≥0∞))ᶜ = 0 := by
  unfold LevyStochCalc.Poisson.poissonMeasureENN
  have hm : MeasurableSet (Set.range ((↑) : ℕ → ℝ≥0∞))ᶜ :=
    (Set.countable_range _).measurableSet.compl
  rw [Measure.map_apply (measurable_of_countable _) hm]
  have hempty : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' (Set.range ((↑) : ℕ → ℝ≥0∞))ᶜ = ∅ := by
    ext n; simp
  rw [hempty, measure_empty]

private lemma poissonMeasureENN_Ici_two_le (μ : ℝ≥0) :
    LevyStochCalc.Poisson.poissonMeasureENN μ (Set.Ici (2 : ℝ≥0∞)) ≤
      ENNReal.ofReal ((μ : ℝ) ^ 2 / 2) := by
  have hprob : IsProbabilityMeasure (LevyStochCalc.Poisson.poissonMeasureENN μ) := by
    unfold LevyStochCalc.Poisson.poissonMeasureENN
    exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have h0 : LevyStochCalc.Poisson.poissonMeasureENN μ {0} = ENNReal.ofReal (Real.exp (-(μ : ℝ))) := by
    simpa using poissonMeasureENN_apply_nat μ 0
  have h1 : LevyStochCalc.Poisson.poissonMeasureENN μ {1} =
      ENNReal.ofReal (Real.exp (-(μ : ℝ)) * (μ : ℝ)) := by
    simpa using poissonMeasureENN_apply_nat μ 1
  have hdisj : Disjoint ({0} : Set ℝ≥0∞) {1} := by simp
  have h01 : LevyStochCalc.Poisson.poissonMeasureENN μ ({0} ∪ {1}) =
      ENNReal.ofReal (Real.exp (-(μ : ℝ)) + (μ : ℝ) * Real.exp (-(μ : ℝ))) := by
    rw [measure_union hdisj (measurableSet_singleton 1), h0, h1,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le μ.coe_nonneg)]
    congr 1; ring
  have hsub : Set.Ici (2 : ℝ≥0∞) ⊆ ({0} ∪ {1} : Set ℝ≥0∞)ᶜ := by
    intro x hx hmem
    rcases hmem with rfl | rfl
    · exact absurd hx (by norm_num)
    · exact absurd hx (by norm_num)
  have hle1 : LevyStochCalc.Poisson.poissonMeasureENN μ (Set.Ici (2 : ℝ≥0∞)) ≤
      1 - ENNReal.ofReal (Real.exp (-(μ : ℝ)) + (μ : ℝ) * Real.exp (-(μ : ℝ))) := by
    calc LevyStochCalc.Poisson.poissonMeasureENN μ (Set.Ici (2 : ℝ≥0∞))
        ≤ LevyStochCalc.Poisson.poissonMeasureENN μ ({0} ∪ {1} : Set ℝ≥0∞)ᶜ := measure_mono hsub
      _ = 1 - LevyStochCalc.Poisson.poissonMeasureENN μ ({0} ∪ {1}) := by
          rw [measure_compl ((measurableSet_singleton 0).union (measurableSet_singleton 1))
            (measure_ne_top _ _), measure_univ]
      _ = 1 - ENNReal.ofReal (Real.exp (-(μ : ℝ)) + (μ : ℝ) * Real.exp (-(μ : ℝ))) := by rw [h01]
  have hsub_eq : 1 - ENNReal.ofReal (Real.exp (-(μ : ℝ)) + (μ : ℝ) * Real.exp (-(μ : ℝ))) =
      ENNReal.ofReal (1 - Real.exp (-(μ : ℝ)) - (μ : ℝ) * Real.exp (-(μ : ℝ))) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (add_nonneg (Real.exp_pos _).le (mul_nonneg μ.coe_nonneg (Real.exp_pos _).le))]
    congr 1; ring
  rw [hsub_eq] at hle1
  exact hle1.trans (ENNReal.ofReal_le_ofReal (one_sub_exp_sub_mul_exp_le_half_sq μ.coe_nonneg))

private lemma prm_nat_valued_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {R : Set (ℝ × ℝ)} (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ k : ℕ, N.N ω R = (k : ℝ≥0∞) := by
  have hm : MeasurableSet (Set.range ((↑) : ℕ → ℝ≥0∞))ᶜ :=
    (Set.countable_range _).measurableSet.compl
  have h0 : P {ω | ¬ ∃ k : ℕ, N.N ω R = (k : ℝ≥0∞)} = 0 := by
    have hpre : {ω | ¬ ∃ k : ℕ, N.N ω R = (k : ℝ≥0∞)} =
        (fun ω => N.N ω R) ⁻¹' (Set.range ((↑) : ℕ → ℝ≥0∞))ᶜ := by
      ext ω; simp [Set.mem_range, eq_comm]
    rw [hpre, ← Measure.map_apply (N.measurable_eval hRm) hm, N.poisson_law hRm hRfin]
    exact poissonMeasureENN_range_compl _
  exact ae_iff.mpr h0

private lemma prm_no_double_jump_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {D : Set ℝ} (hDm : MeasurableSet D) (hDfin : ν D < ⊤)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ∀ k : Fin (2 ^ m),
      N.N ω (Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
          (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) ×ˢ D) ≤ 1 := by
  let J : (m : ℕ) → Fin (2 ^ m) → Set (ℝ × ℝ) := fun m k =>
    Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
      (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) ×ˢ D
  have hJm : ∀ m k, MeasurableSet (J m k) := fun _ _ => measurableSet_Ioc.prod hDm
  let lam : ℝ := (ν D).toReal
  have hJint : ∀ m k, LevyStochCalc.Poisson.referenceIntensity ν (J m k) =
      ENNReal.ofReal (2 * (t : ℝ) / (2 : ℝ) ^ m) * ν D := fun m k => by
    unfold LevyStochCalc.Poisson.referenceIntensity
    dsimp only [J]
    have hsub_ici : Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
        (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) ⊆ Set.Ici (0 : ℝ) :=
      fun _ hx => le_trans (by positivity) (le_of_lt hx.1)
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.mpr hsub_ici, Real.volume_Ioc]
    congr 2
    push_cast; ring
  have hJfin : ∀ m k, LevyStochCalc.Poisson.referenceIntensity ν (J m k) ≠ ⊤ := fun m k => by
    rw [hJint]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin.ne
  have hnat_all : ∀ᵐ ω ∂P, ∀ (m : ℕ) (k : Fin (2 ^ m)), ∃ n : ℕ, N.N ω (J m k) = (n : ℝ≥0∞) :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => prm_nat_valued_ae N (hJm m k) (hJfin m k)
  let Bad : ℕ → Set Ω := fun m => ⋃ k : Fin (2 ^ m), {ω | (2 : ℝ≥0∞) ≤ N.N ω (J m k)}
  have hBad_le : ∀ m : ℕ, P (Bad m) ≤ ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / (2 : ℝ) ^ m) := by
    intro m
    have hterm : ∀ k : Fin (2 ^ m),
        P {ω | (2 : ℝ≥0∞) ≤ N.N ω (J m k)} ≤
          ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / ((2 : ℝ) ^ m) ^ 2) := fun k => by
      have hpre : {ω | (2 : ℝ≥0∞) ≤ N.N ω (J m k)} = (fun ω => N.N ω (J m k)) ⁻¹' Set.Ici 2 := rfl
      rw [hpre, ← Measure.map_apply (N.measurable_eval (hJm m k)) measurableSet_Ici,
        N.poisson_law (hJm m k) (hJfin m k)]
      refine (poissonMeasureENN_Ici_two_le _).trans (ENNReal.ofReal_le_ofReal ?_)
      have htr : ((LevyStochCalc.Poisson.referenceIntensity ν (J m k)).toNNReal : ℝ) =
          2 * (t : ℝ) / (2 : ℝ) ^ m * lam := by
        change (LevyStochCalc.Poisson.referenceIntensity ν (J m k)).toReal = _
        rw [hJint, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      rw [htr]; ring_nf; exact le_rfl
    calc P (Bad m)
        ≤ ∑ k : Fin (2 ^ m), P {ω | (2 : ℝ≥0∞) ≤ N.N ω (J m k)} := by
            have := measure_biUnion_finset_le (μ := P) (Finset.univ : Finset (Fin (2 ^ m)))
              (fun k : Fin (2 ^ m) => {ω | (2 : ℝ≥0∞) ≤ N.N ω (J m k)})
            simpa [Bad] using this
      _ ≤ ∑ _k : Fin (2 ^ m), ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / ((2 : ℝ) ^ m) ^ 2) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = ((2 ^ m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / ((2 : ℝ) ^ m) ^ 2) := by simp
      _ = ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) * (2 * ((t : ℝ) * lam) ^ 2 / ((2 : ℝ) ^ m) ^ 2)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ = ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / (2 : ℝ) ^ m) := by
          congr 1; push_cast
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m]
  have hinter_zero : P (⋂ m : ℕ, Bad m) = 0 := by
    have htend : Tendsto (fun m : ℕ => ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / (2 : ℝ) ^ m))
        atTop (nhds 0) := by
      have hgeom : Tendsto (fun m : ℕ => (2 * ((t : ℝ) * lam) ^ 2) * (1 / 2 : ℝ) ^ m)
          atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
          (by norm_num) (by norm_num)).const_mul (2 * ((t : ℝ) * lam) ^ 2)
      have heq : (fun m : ℕ => ENNReal.ofReal (2 * ((t : ℝ) * lam) ^ 2 / (2 : ℝ) ^ m)) =
          fun m => ENNReal.ofReal ((2 * ((t : ℝ) * lam) ^ 2) * (1 / 2 : ℝ) ^ m) := by
        funext m; congr 1; simp [div_eq_mul_inv, inv_pow]
      rw [heq]
      have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hgeom
      simpa [Function.comp_def, ENNReal.ofReal_zero] using hc
    exact le_antisymm
      (ge_of_tendsto' htend fun m => (measure_mono (Set.iInter_subset Bad m)).trans (hBad_le m))
      zero_le'
  have hex_good : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∉ Bad m := by
    rw [ae_iff]
    have hset : {ω | ¬ ∃ m : ℕ, ω ∉ Bad m} = ⋂ m : ℕ, Bad m := by
      ext ω; simp
    rw [hset]; exact hinter_zero
  filter_upwards [hex_good, hnat_all] with ω ⟨m, hm⟩ hnat
  refine ⟨m, fun k => ?_⟩
  have hlt2 : N.N ω (J m k) < 2 := by
    by_contra hge
    exact hm (Set.mem_iUnion.mpr ⟨k, le_of_not_gt hge⟩)
  obtain ⟨n, hn⟩ := hnat m k
  rw [hn] at hlt2 ⊢
  have hn_lt : n < 2 := by exact_mod_cast hlt2
  have hn_le : n ≤ 1 := by omega
  exact_mod_cast hn_le

private lemma Ioc_subset_overlapping_dyadic {t u s : ℝ≥0} (ht : 0 < t) (hus : u < s) (hst : s ≤ t)
    (m : ℕ) (hclose : (s : ℝ) - (u : ℝ) < (t : ℝ) / (2 : ℝ) ^ m) :
    ∃ k : Fin (2 ^ m),
      Set.Ioc (u : ℝ) (s : ℝ) ⊆
        Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
          (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  let k_nat : ℕ := ⌊((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m⌋₊
  have hk_lt : k_nat < 2 ^ m := by
    have hu_lt : (u : ℝ) < (t : ℝ) := by exact_mod_cast (hus.trans_le hst)
    have hfrac : (u : ℝ) / (t : ℝ) < 1 := (div_lt_one htpos).mpr hu_lt
    have hmul : ((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m < ((2 ^ m : ℕ) : ℝ) := by
      push_cast; linarith [mul_lt_mul_of_pos_right hfrac h2m]
    exact (Nat.floor_lt (mul_nonneg (div_nonneg u.coe_nonneg htpos.le) h2m.le)).mpr hmul
  refine ⟨⟨k_nat, hk_lt⟩, fun x hx => ⟨?_, ?_⟩⟩
  · have hfl : (k_nat : ℝ) ≤ ((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m :=
      Nat.floor_le (mul_nonneg (div_nonneg u.coe_nonneg htpos.le) h2m.le)
    have h1 : (k_nat : ℝ) * (t : ℝ) / (2 : ℝ) ^ m ≤ (u : ℝ) := by
      rw [div_le_iff₀ h2m]
      have h2 := mul_le_mul_of_nonneg_right hfl htpos.le
      have h3 : ((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m * (t : ℝ) = (u : ℝ) * (2 : ℝ) ^ m := by
        field_simp [htpos.ne']
      linarith
    exact lt_of_le_of_lt h1 hx.1
  · have hfl : ((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m < (k_nat : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : (u : ℝ) < ((k_nat : ℝ) + 1) * (t : ℝ) / (2 : ℝ) ^ m := by
      rw [lt_div_iff₀ h2m]
      have h2 := mul_lt_mul_of_pos_right hfl htpos
      have h3 : ((u : ℝ) / (t : ℝ)) * (2 : ℝ) ^ m * (t : ℝ) = (u : ℝ) * (2 : ℝ) ^ m := by
        field_simp [htpos.ne']
      linarith
    have h2 : (((k_nat + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) =
        ((k_nat : ℝ) + 1) * (t : ℝ) / (2 : ℝ) ^ m + (t : ℝ) / (2 : ℝ) ^ m := by
      push_cast; ring
    linarith [hx.2]

private lemma measurable_sub_comap_le {Ω₀ : Type*} {m : MeasurableSpace Ω₀}
    {f g : Ω₀ → ℝ} (hf : MeasurableSpace.comap f inferInstance ≤ m)
    (hg : MeasurableSpace.comap g inferInstance ≤ m) :
    @Measurable Ω₀ ℝ m _ (fun ω => f ω - g ω) := by
  letI : MeasurableSpace Ω₀ := m
  have h1 : Measurable f := (comap_measurable f).mono hf le_rfl
  have h2 : Measurable g := (comap_measurable g).mono hg le_rfl
  exact h1.sub h2

private lemma brownian_increments_iIndepFun {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] (B : LevyStochCalc.Brownian.BrownianMotion P₀) :
    ∀ (n : ℕ) (ts : Fin (n + 1) → ℝ≥0), Monotone ts →
      iIndepFun (fun k : Fin n => fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) P₀ := by
  intro n
  induction n with
  | zero =>
    intro ts _
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    subst hS; simp
  | succ n ih =>
    intro ts hts
    let ts' : Fin (n + 1) → ℝ≥0 := fun k => ts k.castSucc
    have hts' : Monotone ts' := fun i j hij => hts (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hind_prev := ih ts' hts'
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    let lastIdx : Fin (n + 1) := Fin.last n
    by_cases hmem : lastIdx ∈ S
    · -- Split `S = insert lastIdx S'` where `S' = S.erase lastIdx`
      let S' : Finset (Fin (n + 1)) := S.erase lastIdx
      have hnotmem : lastIdx ∉ S' := Finset.notMem_erase _ _
      have hS_eq : S = insert lastIdx S' := (Finset.insert_erase hmem).symm
      -- Embed `S'` into `Fin n`
      let S_prev : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k.castSucc ∈ S'
      have hprev_inter : (⋂ k ∈ S', (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ⋂ k ∈ S_prev, (fun ω₀ => B.W (ts' k.succ : ℝ) ω₀ - B.W (ts' k.castSucc : ℝ) ω₀) ⁻¹' sets k.castSucc := by
        ext ω₀
        simp only [Set.mem_iInter, Set.mem_preimage, S_prev, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h k hk
          have heq1 : ts' k.succ = ts k.castSucc.succ := rfl
          have heq2 : ts' k.castSucc = ts k.castSucc.castSucc := rfl
          rw [heq1, heq2]; exact h k.castSucc hk
        · intro h k hk
          have hne : k ≠ lastIdx := fun heq => hnotmem (heq ▸ hk)
          have hlt : k.1 < n := by
            have := k.2
            have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
            omega
          let k' : Fin n := ⟨k.1, hlt⟩
          have hk' : k'.castSucc = k := Fin.ext rfl
          have hk'm : k'.castSucc ∈ S' := hk' ▸ hk
          have hstep := h k' hk'm
          simpa [ts', hk'] using hstep
      have hprev_prod : ∏ k ∈ S', P₀ ((fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ∏ k ∈ S_prev, P₀ ((fun ω₀ => B.W (ts' k.succ : ℝ) ω₀ - B.W (ts' k.castSucc : ℝ) ω₀) ⁻¹' sets k.castSucc) := by
        refine Finset.prod_bij (fun k (hk : k ∈ S') =>
            (⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hnotmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩ : Fin n))
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            have heq : (⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hnotmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩ : Fin n).castSucc = k := Fin.ext rfl
            rwa [heq]⟩)
          (fun k₁ _ k₂ _ heq => Fin.ext (congrArg (Fin.val : Fin n → ℕ) heq))
          (fun k hk => ⟨k.castSucc, (Finset.mem_filter.mp hk).2, Fin.ext rfl⟩)
          (fun k hk => by
            let k' : Fin n := ⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hnotmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩
            have heq : k'.castSucc = k := Fin.ext rfl
            have heq_s : ts' k'.succ = ts k.succ := by
              change ts k'.succ.castSucc = ts k.succ
              congr 1
            have heq_c : ts' k'.castSucc = ts k.castSucc := by
              change ts k'.castSucc.castSucc = ts k.castSucc
              congr 1
            show P₀ ((fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
              P₀ ((fun ω₀ => B.W (ts' k'.succ : ℝ) ω₀ - B.W (ts' k'.castSucc : ℝ) ω₀) ⁻¹' sets k'.castSucc)
            rw [heq_s, heq_c, heq])
      have hprev_eq : P₀ (⋂ k ∈ S', (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ∏ k ∈ S', P₀ ((fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) := by
        rw [hprev_inter, hprev_prod]
        exact (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind_prev) S_prev
          (fun k hk => hsets k.castSucc (Finset.mem_of_mem_erase (Finset.mem_filter.mp hk).2))
      -- Now split `lastIdx` from `S'`
      rw [hS_eq, Finset.prod_insert hnotmem]
      have hinter_split : (⋂ k ∈ insert lastIdx S',
            (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ((fun ω₀ => B.W (ts lastIdx.succ : ℝ) ω₀ - B.W (ts lastIdx.castSucc : ℝ) ω₀) ⁻¹' sets lastIdx) ∩
            (⋂ k ∈ S', (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) := by
        ext ω₀; simp
      rw [hinter_split, ← hprev_eq]
      let A := ⋂ k ∈ S', (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k
      let C := (fun ω₀ => B.W (ts lastIdx.succ : ℝ) ω₀ - B.W (ts lastIdx.castSucc : ℝ) ω₀) ⁻¹' sets lastIdx
      change P₀ (C ∩ A) = P₀ C * P₀ A
      rcases eq_or_lt_of_le (hts (Fin.castSucc_le_succ lastIdx)) with heq | hlt
      · -- Degenerate increment `= 0`
        have hC_const : C = (fun _ : Ω₀ => (0 : ℝ)) ⁻¹' sets lastIdx := by
          ext ω₀; simp [C, heq]
        by_cases h0 : (0 : ℝ) ∈ sets lastIdx
        · have hCu : C = Set.univ := by rw [hC_const]; ext ω₀; simp [h0]
          rw [hCu, Set.univ_inter, measure_univ, one_mul]
        · have hCe : C = ∅ := by rw [hC_const]; ext ω₀; simp [h0]
          rw [hCe, Set.empty_inter, measure_empty, zero_mul]
      · -- Strict increment: use `B.joint_increment_independent`
        have hind_joint := B.joint_increment_independent (ts lastIdx.castSucc).coe_nonneg
          (show (ts lastIdx.castSucc : ℝ) < (ts lastIdx.succ : ℝ) by exact_mod_cast hlt)
        have hA_meas : MeasurableSet[⨆ j ∈ Set.Iic (ts lastIdx.castSucc : ℝ),
            MeasurableSpace.comap (B.W j) inferInstance] A := by
          refine MeasurableSet.biInter S'.countable_toSet fun k hk => ?_
          have hne : k ≠ lastIdx := fun heq => hnotmem (heq ▸ hk)
          have hk_le : k.succ ≤ lastIdx.castSucc := by
            show k.1 + 1 ≤ n
            have := k.2
            have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
            omega
          have h1_le : (ts k.succ : ℝ) ≤ (ts lastIdx.castSucc : ℝ) := by exact_mod_cast hts hk_le
          have h2_le : (ts k.castSucc : ℝ) ≤ (ts lastIdx.castSucc : ℝ) := by
            exact_mod_cast hts ((Fin.castSucc_le_succ k).trans hk_le)
          have hsub_meas : @Measurable Ω₀ ℝ
              (⨆ j ∈ Set.Iic (ts lastIdx.castSucc : ℝ), MeasurableSpace.comap (B.W j) inferInstance) _
              (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) :=
            measurable_sub_comap_le
              (le_biSup (fun j => MeasurableSpace.comap (B.W j) inferInstance) h1_le)
              (le_biSup (fun j => MeasurableSpace.comap (B.W j) inferInstance) h2_le)
          exact hsub_meas (hsets k (Finset.mem_of_mem_erase hk))
        have hC_meas : MeasurableSet[MeasurableSpace.comap
            (fun ω₀ => B.W (ts lastIdx.succ : ℝ) ω₀ - B.W (ts lastIdx.castSucc : ℝ) ω₀) inferInstance] C :=
          ⟨sets lastIdx, hsets lastIdx hmem, rfl⟩
        have hmul : P₀ (A ∩ C) = P₀ A * P₀ C := by
          have h := hind_joint A C hA_meas hC_meas
          simpa using h
        rw [Set.inter_comm, hmul, mul_comm]
    · -- `lastIdx ∉ S`: reduce directly to `ih`
      let S_prev : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k.castSucc ∈ S
      have hprev_inter : (⋂ k ∈ S, (fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ⋂ k ∈ S_prev, (fun ω₀ => B.W (ts' k.succ : ℝ) ω₀ - B.W (ts' k.castSucc : ℝ) ω₀) ⁻¹' sets k.castSucc := by
        ext ω₀
        simp only [Set.mem_iInter, Set.mem_preimage, S_prev, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h k hk; exact h k.castSucc hk
        · intro h k hk
          have hne : k ≠ lastIdx := fun heq => hmem (heq ▸ hk)
          have hlt : k.1 < n := by
            have := k.2; have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h'); omega
          let k' : Fin n := ⟨k.1, hlt⟩
          have hk' : k'.castSucc = k := Fin.ext rfl
          simpa [ts', hk'] using h k' (hk' ▸ hk)
      have hprev_prod : ∏ k ∈ S, P₀ ((fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
          ∏ k ∈ S_prev, P₀ ((fun ω₀ => B.W (ts' k.succ : ℝ) ω₀ - B.W (ts' k.castSucc : ℝ) ω₀) ⁻¹' sets k.castSucc) := by
        refine Finset.prod_bij (fun k (hk : k ∈ S) =>
            (⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩ : Fin n))
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            have heq : (⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩ : Fin n).castSucc = k := Fin.ext rfl
            rwa [heq]⟩)
          (fun k₁ _ k₂ _ heq => Fin.ext (congrArg (Fin.val : Fin n → ℕ) heq))
          (fun k hk => ⟨k.castSucc, (Finset.mem_filter.mp hk).2, Fin.ext rfl⟩)
          (fun k hk => by
            let k' : Fin n := ⟨k.1, by
              have hne : k ≠ lastIdx := fun heq => hmem (heq ▸ hk)
              have hne' : k.1 ≠ n := fun h' => hne (Fin.ext h')
              have := k.2; omega⟩
            have heq : k'.castSucc = k := Fin.ext rfl
            have heq_s : ts' k'.succ = ts k.succ := by
              change ts k'.succ.castSucc = ts k.succ
              congr 1
            have heq_c : ts' k'.castSucc = ts k.castSucc := by
              change ts k'.castSucc.castSucc = ts k.castSucc
              congr 1
            show P₀ ((fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) ⁻¹' sets k) =
              P₀ ((fun ω₀ => B.W (ts' k'.succ : ℝ) ω₀ - B.W (ts' k'.castSucc : ℝ) ω₀) ⁻¹' sets k'.castSucc)
            rw [heq_s, heq_c, heq])
      rw [hprev_inter, hprev_prod]
      exact (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind_prev) S_prev
        (fun k hk => hsets k.castSucc (Finset.mem_filter.mp hk).2)

private lemma brownian_levy_component (σ : ℝ≥0) (c_drift : ℝ) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (X_gauss : ℝ≥0 → Ω₀ → ℝ),
      ProbabilityTheory.IsLevyProcess X_gauss P₀ ∧
      (∀ s : ℝ≥0, Measurable (X_gauss s)) ∧
      (∀ᵐ ω₀ ∂P₀, Continuous (fun s : ℝ≥0 => X_gauss s ω₀)) ∧
      (∀ (s : ℝ≥0) (ξ : ℝ),
        charFun (P₀.map (X_gauss s)) ξ =
          Complex.exp ((((s : ℝ) : ℂ)) *
            ((c_drift : ℂ) * (ξ : ℂ) * Complex.I -
              (((σ ^ 2 : ℝ≥0) : ℝ) : ℂ) * ((ξ : ℂ) ^ 2) / 2))) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨B⟩⟩ := LevyStochCalc.Brownian.BrownianMotion.exists_readable
  letI : MeasurableSpace Ω₀ := mΩ₀
  letI : IsProbabilityMeasure P₀ := hP₀
  let X_gauss : ℝ≥0 → Ω₀ → ℝ := fun s ω₀ => (σ : ℝ) * (B.W (s : ℝ) ω₀ - B.W 0 ω₀) + c_drift * (s : ℝ)
  have hmeas : ∀ s : ℝ≥0, Measurable (X_gauss s) := fun s =>
    (measurable_const.mul ((B.measurable_eval (s : ℝ)).sub (B.measurable_eval 0))).add measurable_const
  have hcont : ∀ᵐ ω₀ ∂P₀, Continuous (fun s : ℝ≥0 => X_gauss s ω₀) := by
    filter_upwards [B.continuous_paths] with ω₀ hω₀
    exact (continuous_const.mul ((hω₀.comp NNReal.continuous_coe).sub continuous_const)).add
      (continuous_const.mul NNReal.continuous_coe)
  have hlevy : ProbabilityTheory.IsLevyProcess X_gauss P₀ := {
    start_zero := by funext ω₀; simp [X_gauss]
    indep_increments := by
      intro n ts hts
      have hind := brownian_increments_iIndepFun B n ts hts
      let aff : Fin n → ℝ → ℝ := fun k x => (σ : ℝ) * x + c_drift * ((ts k.succ : ℝ) - (ts k.castSucc : ℝ))
      have haff : ∀ k, Measurable (aff k) := fun _ => (measurable_const.mul measurable_id).add measurable_const
      have hcomp := hind.comp aff haff
      have heq : (fun k => aff k ∘ fun ω₀ => B.W (ts k.succ : ℝ) ω₀ - B.W (ts k.castSucc : ℝ) ω₀) =
          fun k => ProbabilityTheory.increment X_gauss (ts k.castSucc) (ts k.succ) := by
        funext k ω₀; simp only [Function.comp_apply, aff, ProbabilityTheory.increment, X_gauss]; ring
      rwa [heq] at hcomp
    stationary_increments := by
      intro s h
      let f : ℝ → ℝ := fun x => (σ : ℝ) * x + c_drift * (h : ℝ)
      have hf : Measurable f := (measurable_const.mul measurable_id).add measurable_const
      have heq1 : ProbabilityTheory.increment X_gauss s (s + h) =
          f ∘ fun ω₀ => B.W ((s + h : ℝ≥0) : ℝ) ω₀ - B.W (s : ℝ) ω₀ := by
        funext ω₀; simp only [Function.comp_apply, f, ProbabilityTheory.increment, X_gauss]; push_cast; ring
      have heq2 : ProbabilityTheory.increment X_gauss 0 h =
          f ∘ fun ω₀ => B.W (h : ℝ) ω₀ - B.W 0 ω₀ := by
        funext ω₀; simp only [Function.comp_apply, f, ProbabilityTheory.increment, X_gauss]; push_cast; ring
      rw [heq1, heq2]
      refine IdentDistrib.comp ?_ hf
      refine ⟨((B.measurable_eval _).sub (B.measurable_eval _)).aemeasurable,
        ((B.measurable_eval _).sub (B.measurable_eval _)).aemeasurable, ?_⟩
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ h) with rfl | hh
      · simp
      · have h1 := B.increment_gaussian s.coe_nonneg (show (s : ℝ) < ((s + h : ℝ≥0) : ℝ) by
          push_cast; linarith [show (0 : ℝ) < (h : ℝ) from by exact_mod_cast hh])
        have h2 := B.increment_gaussian le_rfl (show (0 : ℝ) < (h : ℝ) by exact_mod_cast hh)
        rw [h1, h2]
        congr 1; ext; push_cast; ring
    cadlag_ae := by
      filter_upwards [hcont] with ω₀ hω₀ s
      exact ⟨hω₀.continuousAt.continuousWithinAt,
        ⟨X_gauss s ω₀, hω₀.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
  }
  have hchar : ∀ (s : ℝ≥0) (ξ : ℝ),
      charFun (P₀.map (X_gauss s)) ξ =
        Complex.exp ((((s : ℝ) : ℂ)) *
          ((c_drift : ℂ) * (ξ : ℂ) * Complex.I -
            (((σ ^ 2 : ℝ≥0) : ℝ) : ℂ) * ((ξ : ℂ) ^ 2) / 2)) := by
    intro s ξ
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with rfl | hs
    · have h0 : X_gauss 0 = fun _ => 0 := by funext ω₀; simp [X_gauss]
      rw [h0, Measure.map_const, measure_univ, one_smul, charFun_dirac]
      simp
    · let f : ℝ → ℝ := fun x => (σ : ℝ) * x + c_drift * (s : ℝ)
      have hf : Measurable f := (measurable_const.mul measurable_id).add measurable_const
      have hX_eq : X_gauss s = f ∘ fun ω₀ => B.W (s : ℝ) ω₀ - B.W 0 ω₀ := rfl
      have hW_meas : Measurable (fun ω₀ => B.W (s : ℝ) ω₀ - B.W 0 ω₀) :=
        (B.measurable_eval (s : ℝ)).sub (B.measurable_eval 0)
      have hW_law : P₀.map (fun ω₀ => B.W (s : ℝ) ω₀ - B.W 0 ω₀) =
          ProbabilityTheory.gaussianReal 0 s := by
        have h := B.increment_gaussian le_rfl (show (0 : ℝ) < (s : ℝ) by exact_mod_cast hs)
        rw [h]
        congr 1
        exact NNReal.eq (sub_zero (s : ℝ))
      rw [hX_eq, ← Measure.map_map hf hW_meas, hW_law, charFun_apply_real]
      have hcont_exp : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
      rw [integral_map hf.aemeasurable hcont_exp.aestronglyMeasurable]
      have hpull : (fun x : ℝ => Complex.exp ((ξ : ℂ) * ((f x : ℝ) : ℂ) * Complex.I)) =
          fun x : ℝ => Complex.exp (((s : ℝ) : ℂ) * (c_drift : ℂ) * (ξ : ℂ) * Complex.I) *
            Complex.exp ((((σ : ℝ) * ξ : ℝ) : ℂ) * (x : ℂ) * Complex.I) := by
        funext x; dsimp only [f]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hpull, integral_const_mul, ← charFun_apply_real,
        ProbabilityTheory.charFun_gaussianReal, ← Complex.exp_add]
      congr 1; push_cast; ring
  exact ⟨Ω₀, mΩ₀, P₀, hP₀, X_gauss, hlevy, hmeas, hcont, hchar⟩

private lemma smallJump_levy_component
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (X_small : ℝ≥0 → Ω₁ → ℝ),
      ProbabilityTheory.IsLevyProcess X_small P₁ ∧
      (∀ s : ℝ≥0, Measurable (X_small s)) ∧
      (∀ᵐ ω₁ ∂P₁, {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => X_small u ω₁) s}.Countable) ∧
      (∀ᵐ ω₁ ∂P₁, ∀ s : ℝ≥0, 0 < s → s ≤ t → ∀ l : ℝ,
        Tendsto (fun u => X_small u ω₁) (nhdsWithin s (Set.Iio s)) (nhds l) →
        |X_small s ω₁ - l| ≤ r) ∧
      (∀ (s : ℝ≥0) (ξ : ℝ),
        charFun (P₁.map (X_small s)) ξ =
          Complex.exp ((((s : ℝ) : ℂ)) *
            ∫ x in {x : ℝ | |x| ≤ r},
              (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 -
                Complex.I * (((ξ * x : ℝ) : ℂ))) ∂ν)) := by
  let B_small : Set ℝ := {x : ℝ | |x| ≤ r}
  have hBs_meas : MeasurableSet B_small := continuous_abs.measurable measurableSet_Iic
  let c : ℝ := 1 / (2 * r)
  have hc_pos : 0 < c := by positivity
  have h2r_pos : 0 < 2 * r := by positivity
  let sc : ℝ → ℝ := fun x => c * x
  have hsc_meas : Measurable sc := measurable_const.mul measurable_id
  let ν_sc : Measure ℝ := (ν.restrict B_small).map sc
  have hν_sc : ProbabilityTheory.IsLevyMeasure ν_sc := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_apply hsc_meas (measurableSet_singleton 0)]
      have hpre : sc ⁻¹' {0} = {0} := by
        ext x; simp [sc, hc_pos.ne']
      rw [hpre]
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hν.1)) zero_le'
    · have hmeas_min : Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id.pow_const 2))
      rw [lintegral_map hmeas_min hsc_meas]
      let K : ℝ := max 1 (c ^ 2)
      have hK_nn : 0 ≤ K := le_trans (by norm_num) (le_max_left 1 (c ^ 2))
      have hpt : ∀ x : ℝ, ENNReal.ofReal (min 1 ((sc x) ^ 2)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
        rw [← ENNReal.ofReal_mul hK_nn]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsc2 : (sc x) ^ 2 = c ^ 2 * x ^ 2 := by dsimp only [sc]; ring
        rw [hsc2]
        by_cases hx : x ^ 2 ≤ 1
        · rw [min_eq_right hx]
          exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right 1 (c ^ 2)) (sq_nonneg x))
        · push Not at hx
          rw [min_eq_left hx.le, mul_one]
          exact (min_le_left _ _).trans (le_max_left 1 (c ^ 2))
      calc ∫⁻ x, ENNReal.ofReal (min 1 ((sc x) ^ 2)) ∂(ν.restrict B_small)
          ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) ∂(ν.restrict B_small) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal K * ∫⁻ x in B_small, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
            lintegral_const_mul _ hmeas_min
        _ ≤ ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
            have hle : ∫⁻ x in B_small, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν ≤
                ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
              simpa [Measure.restrict_univ] using lintegral_mono_set (μ := ν) (Set.subset_univ B_small)
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2
  haveI : SigmaFinite ν_sc := levyMeasure_sigmaFinite hν_sc
  have hν_sc_supp : ν_sc {y : ℝ | (1 : ℝ) / 2 < |y|} = 0 := by
    have hm : MeasurableSet {y : ℝ | (1 : ℝ) / 2 < |y|} := continuous_abs.measurable measurableSet_Ioi
    rw [Measure.map_apply hsc_meas hm, Measure.restrict_apply (hsc_meas hm)]
    have hempty : sc ⁻¹' {y : ℝ | (1 : ℝ) / 2 < |y|} ∩ B_small = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and, B_small, sc]
      intro hgt hle
      rw [abs_mul, abs_of_pos hc_pos] at hgt
      have h1 : c * |x| ≤ c * r := mul_le_mul_of_nonneg_left hle hc_pos.le
      have h2 : c * r = 1 / 2 := by dsimp only [c]; field_simp [hr.ne']
      linarith
    rw [hempty, measure_empty]
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, ⟨N₁⟩⟩ := Kyprianou.poissonRandomMeasureExists ν_sc
  letI : MeasurableSpace Ω₁ := mΩ₁
  letI : IsProbabilityMeasure P₁ := hP₁
  obtain ⟨M, ℱ, hM_levy, _, hM_mart, _, _, hM_cnt, hM_unif⟩ :=
    Kyprianou.smallJumpLimitCadlagCorrected P₁ ν_sc hν_sc N₁
  have hM_meas : ∀ s : ℝ≥0, Measurable (M s) := fun s =>
    ((hM_mart.stronglyAdapted s).mono (ℱ.le s)).measurable
  let X_small : ℝ≥0 → Ω₁ → ℝ := fun s ω₁ => (2 * r) * M s ω₁
  have hXs_meas : ∀ s : ℝ≥0, Measurable (X_small s) := fun s =>
    measurable_const.mul (hM_meas s)
  have hXs_levy : ProbabilityTheory.IsLevyProcess X_small P₁ := {
    start_zero := by funext ω₁; simp [X_small, hM_levy.start_zero]
    indep_increments := by
      intro n ts hts
      have hind := hM_levy.indep_increments n ts hts
      have hcomp := hind.comp (fun _ x => (2 * r) * x) (fun _ => measurable_const.mul measurable_id)
      have heq : (fun k : Fin n => (fun x => (2 * r) * x) ∘ ProbabilityTheory.increment M (ts k.castSucc) (ts k.succ)) =
          fun k : Fin n => ProbabilityTheory.increment X_small (ts k.castSucc) (ts k.succ) := by
        funext k ω₁; simp only [Function.comp_apply, ProbabilityTheory.increment, X_small]; ring
      rwa [heq] at hcomp
    stationary_increments := by
      intro s h
      let f : ℝ → ℝ := fun x => (2 * r) * x
      have hf : Measurable f := measurable_const.mul measurable_id
      have hcomp := (hM_levy.stationary_increments s h).comp hf
      have heq1 : f ∘ ProbabilityTheory.increment M s (s + h) =
          ProbabilityTheory.increment X_small s (s + h) := by
        funext ω₁; simp only [Function.comp_apply, f, ProbabilityTheory.increment, X_small]; ring
      have heq2 : f ∘ ProbabilityTheory.increment M 0 h =
          ProbabilityTheory.increment X_small 0 h := by
        funext ω₁; simp only [Function.comp_apply, f, ProbabilityTheory.increment, X_small]; ring
      rwa [heq1, heq2] at hcomp
    cadlag_ae := by
      filter_upwards [hM_levy.cadlag_ae] with ω₁ hω₁ s
      refine ⟨continuousWithinAt_const.mul (hω₁ s).1, ?_⟩
      obtain ⟨l, hl⟩ := (hω₁ s).2
      exact ⟨(2 * r) * l, hl.const_mul (2 * r)⟩
  }
  have hXs_cnt : ∀ᵐ ω₁ ∂P₁, {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => X_small u ω₁) s}.Countable := by
    filter_upwards [hM_cnt] with ω₁ hω₁
    have hsub : {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => X_small u ω₁) s} ⊆
        {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => M u ω₁) s} := by
      intro s hs hcont
      apply hs
      have heq : (fun u : ℝ≥0 => X_small u ω₁) = fun u => (2 * r) * M u ω₁ := rfl
      rw [heq]
      exact continuousAt_const.mul hcont
    exact hω₁.mono hsub
  -- Bound all jumps of `X_small` on `(0, t]` by `r`
  have hXs_jump_le : ∀ᵐ ω₁ ∂P₁, ∀ s : ℝ≥0, 0 < s → s ≤ t → ∀ l : ℝ,
      Tendsto (fun u => X_small u ω₁) (nhdsWithin s (Set.Iio s)) (nhds l) →
      |X_small s ω₁ - l| ≤ r := by
    obtain ⟨ε, _, hε_bnd, _, hunif_ae⟩ := hM_unif t ht
    let E : ℕ → Set ℝ := fun n => {y : ℝ | ε n ≤ |y| ∧ |y| < 1}
    let D : ℕ → Set ℝ := fun n => {y : ℝ | ε n ≤ |y| ∧ |y| ≤ (1 : ℝ) / 2}
    have hEm : ∀ n, MeasurableSet (E n) := fun n =>
      (continuous_abs.measurable measurableSet_Ici).inter (continuous_abs.measurable measurableSet_Iio)
    have hDm : ∀ n, MeasurableSet (D n) := fun n =>
      (continuous_abs.measurable measurableSet_Ici).inter (continuous_abs.measurable measurableSet_Iic)
    have hDfin : ∀ n, ν_sc (D n) < ⊤ := fun n =>
      lt_of_le_of_lt (measure_mono (fun y hy => hy.1)) (hν_sc.measure_setOf_abs_ge_lt_top (hε_bnd n).1)
    have hED_zero : ∀ n, ∀ᵐ ω₁ ∂P₁, N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0 := by
      intro n
      have hm : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) :=
        measurableSet_Ioc.prod ((hEm n).diff (hDm n))
      have hν0 : ν_sc (E n \ D n) = 0 := by
        refine le_antisymm ((measure_mono fun y hy => ?_).trans (le_of_eq hν_sc_supp)) zero_le'
        have hnot : ¬ (ε n ≤ |y| ∧ |y| ≤ (1 : ℝ) / 2) := hy.2
        have hge : ε n ≤ |y| := hy.1.1
        exact lt_of_not_ge fun hle => hnot ⟨hge, hle⟩
      have hint0 : LevyStochCalc.Poisson.referenceIntensity ν_sc
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0 := by
        unfold LevyStochCalc.Poisson.referenceIntensity
        rw [Measure.prod_prod, hν0, mul_zero]
      have hP0 : P₁ {ω₁ | N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0} = 1 := by
        have hpre : {ω₁ | N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0} =
            (fun ω₁ => N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n))) ⁻¹' {0} := rfl
        rw [hpre, ← Measure.map_apply (N₁.measurable_eval hm) (measurableSet_singleton 0),
          N₁.poisson_law hm (by rw [hint0]; exact ENNReal.zero_ne_top)]
        have h0 := poissonMeasureENN_apply_nat 0 0
        simpa [hint0] using h0
      rw [ae_iff]
      have hmeas0 : MeasurableSet {ω₁ | N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0} :=
        N₁.measurable_eval hm (measurableSet_singleton 0)
      have hcompl : {ω₁ | ¬ N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0} =
          {ω₁ | N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (E n \ D n)) = 0}ᶜ := rfl
      rw [hcompl, measure_compl hmeas0 (measure_ne_top _ _), measure_univ, hP0, tsub_self]
    have hD_fin_ae : ∀ n, ∀ᵐ ω₁ ∂P₁, N₁.N ω₁ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n) < ⊤ := fun n => by
      have hm : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n) := measurableSet_Ioc.prod (hDm n)
      have hfin : LevyStochCalc.Poisson.referenceIntensity ν_sc (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n) ≠ ⊤ := by
        unfold LevyStochCalc.Poisson.referenceIntensity
        rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
          Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) (t : ℝ) ⊆ Set.Ici 0 from fun _ hx => le_of_lt hx.1),
          Real.volume_Ioc, sub_zero]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDfin n).ne
      filter_upwards [prm_nat_valued_ae N₁ hm hfin] with ω₁ ⟨k, hk⟩
      rw [hk]; exact ENNReal.natCast_lt_top k
    have hnodbl : ∀ n, ∀ᵐ ω₁ ∂P₁, ∃ m : ℕ, ∀ k : Fin (2 ^ m),
        N₁.N ω₁ (Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
            (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) ×ˢ D n) ≤ 1 := fun n =>
      prm_no_double_jump_ae N₁ (hDm n) (hDfin n) ht
    filter_upwards [hunif_ae, ae_all_iff.mpr hED_zero, ae_all_iff.mpr hD_fin_ae,
      ae_all_iff.mpr hnodbl] with ω₁ hunif hED hDfin_ω hnd
    intro s hs hst l hl
    -- First show `|M s ω₁ - c * l| ≤ 1 / 2`
    have hlM : Tendsto (fun u => M u ω₁) (nhdsWithin s (Set.Iio s)) (nhds (c * l)) := by
      have heq : (fun u => M u ω₁) = fun u => c * X_small u ω₁ := by
        funext u; dsimp only [X_small, c]; field_simp [hr.ne']
      rw [heq]; exact hl.const_mul c
    have hM_le : |M s ω₁ - c * l| ≤ (1 : ℝ) / 2 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨n₀, hn₀⟩ := hunif (δ / 4) (by positivity)
      let n := n₀
      have hn_unif : ∀ u ≤ t,
          |Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁ - M u ω₁| < δ / 4 :=
        hn₀ n le_rfl
      obtain ⟨m, hm⟩ := hnd n
      -- Drift slope for `S_n`
      let μ_drift : ℝ := ∫ y in E n, y ∂ν_sc
      have hclose_ev : ∀ᶠ u in nhdsWithin s (Set.Iio s),
          |M u ω₁ - c * l| < δ / 4 ∧
          (s : ℝ) - (u : ℝ) < (t : ℝ) / (2 : ℝ) ^ m ∧
          |((s : ℝ) - (u : ℝ)) * μ_drift| < δ / 4 := by
        have h1 : ∀ᶠ u in nhdsWithin s (Set.Iio s), |M u ω₁ - c * l| < δ / 4 := by
          have := hlM.eventually (Metric.ball_mem_nhds (c * l) (by positivity : 0 < δ / 4))
          exact this.mono fun u hu => by simpa [Real.dist_eq] using hu
        have h2 : ∀ᶠ (u : ℝ≥0) in nhdsWithin s (Set.Iio s), (s : ℝ) - (u : ℝ) < (t : ℝ) / (2 : ℝ) ^ m := by
          have htend : Tendsto (fun u : ℝ≥0 => (s : ℝ) - (u : ℝ))
              (nhdsWithin s (Set.Iio s)) (nhds 0) := by
            have h : Tendsto (fun u : ℝ≥0 => (s : ℝ) - (u : ℝ))
                (nhdsWithin s (Set.Iio s)) (nhds ((s : ℝ) - (s : ℝ))) :=
              tendsto_const_nhds.sub ((NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds)
            simpa [sub_self] using h
          have htpos : (0 : ℝ) < (t : ℝ) / (2 : ℝ) ^ m := by
            have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
            positivity
          exact htend.eventually (Iio_mem_nhds htpos)
        have h3 : ∀ᶠ (u : ℝ≥0) in nhdsWithin s (Set.Iio s), |((s : ℝ) - (u : ℝ)) * μ_drift| < δ / 4 := by
          have htend : Tendsto (fun u : ℝ≥0 => |((s : ℝ) - (u : ℝ)) * μ_drift|)
              (nhdsWithin s (Set.Iio s)) (nhds 0) := by
            have h0 : Tendsto (fun u : ℝ≥0 => (s : ℝ) - (u : ℝ))
                (nhdsWithin s (Set.Iio s)) (nhds ((s : ℝ) - (s : ℝ))) :=
              tendsto_const_nhds.sub ((NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds)
            simpa [sub_self] using (h0.mul_const μ_drift).abs
          exact htend.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 4))
        exact h1.and (h2.and h3)
      have hne_nhds : (nhdsWithin s (Set.Iio s)).NeBot := by
        rw [nhdsWithin_neBot]
        intro U hU
        rw [Metric.mem_nhds_iff] at hU
        obtain ⟨ρ, hρ, hball⟩ := hU
        let u : ℝ≥0 := ⟨max 0 ((s : ℝ) - min (ρ / 2) ((s : ℝ) / 2)), le_max_left _ _⟩
        have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
        have hstep : 0 < min (ρ / 2) ((s : ℝ) / 2) := lt_min (by positivity) (by positivity)
        have hu_val : (u : ℝ) = (s : ℝ) - min (ρ / 2) ((s : ℝ) / 2) :=
          max_eq_right (by linarith [min_le_right (ρ / 2) ((s : ℝ) / 2)])
        refine ⟨u, hball ?_, ?_⟩
        · show dist (u : ℝ) (s : ℝ) < ρ
          rw [Real.dist_eq, hu_val]
          have : |((s : ℝ) - min (ρ / 2) ((s : ℝ) / 2)) - (s : ℝ)| = min (ρ / 2) ((s : ℝ) / 2) := by
            rw [show (s : ℝ) - min (ρ / 2) ((s : ℝ) / 2) - (s : ℝ) = -min (ρ / 2) ((s : ℝ) / 2) by ring,
              abs_neg, abs_of_pos hstep]
          rw [this]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        · show u < s
          change (u : ℝ) < (s : ℝ); linarith
      have hboth_ev : ∀ᶠ u in nhdsWithin s (Set.Iio s),
          u < s ∧ |M u ω₁ - c * l| < δ / 4 ∧
          (s : ℝ) - (u : ℝ) < (t : ℝ) / (2 : ℝ) ^ m ∧
          |((s : ℝ) - (u : ℝ)) * μ_drift| < δ / 4 :=
        Filter.Eventually.and self_mem_nhdsWithin hclose_ev
      obtain ⟨u, hu_lt, hu_M, hu_close, hu_drift⟩ := hboth_ev.exists
      have hu_le_t : u ≤ t := hu_lt.le.trans hst
      -- Bound `|S_n s ω₁ - S_n u ω₁| ≤ 1 / 2 + δ / 4`
      have hJ_eq : ∀ v : ℝ≥0, v ≤ t →
          ∫ z in Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ E n, z.2 ∂(N₁.N ω₁) =
            ∫ z in Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁) := fun v hv => by
        have hsub : D n ⊆ E n := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩
        have hzero : N₁.N ω₁ (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ (E n \ D n)) = 0 := by
          refine le_antisymm ((measure_mono ?_).trans (le_of_eq (hED n))) zero_le'
          exact Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hv)) Set.Subset.rfl
        refine setIntegral_congr_set ?_
        rw [ae_eq_set]
        refine ⟨?_, ?_⟩
        · have hdiff : (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ E n) \ (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ D n) =
              Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ (E n \ D n) := by
            ext ⟨x, y⟩; simp only [Set.mem_diff, Set.mem_prod]; tauto
          rw [hdiff]; exact hzero
        · have hempty : (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ D n) \ (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ E n) = ∅ := by
            ext ⟨x, y⟩
            constructor
            · rintro ⟨⟨hx, hy⟩, hnot⟩; exact hnot ⟨hx, hsub hy⟩
            · rintro ⟨⟩
          rw [hempty, measure_empty]
      have hJ_diff : (∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) -
          (∫ z in Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) =
          ∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁) := by
        have hsplit : Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ D n =
            (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n) ∪ (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n) := by
          ext ⟨x, y⟩
          simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc]
          have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.coe_nonneg
          have hus : (u : ℝ) < (s : ℝ) := by exact_mod_cast hu_lt
          constructor
          · rintro ⟨⟨hx0, hxs⟩, hy⟩
            by_cases hxu : x ≤ (u : ℝ)
            · exact Or.inl ⟨⟨hx0, hxu⟩, hy⟩
            · exact Or.inr ⟨⟨lt_of_not_ge hxu, hxs⟩, hy⟩
          · rintro (⟨⟨hx0, hxu⟩, hy⟩ | ⟨⟨hxu, hxs⟩, hy⟩)
            · exact ⟨⟨hx0, hxu.trans hus.le⟩, hy⟩
            · exact ⟨⟨lt_of_le_of_lt hu0 hxu, hxs⟩, hy⟩
        have hdisj : Disjoint (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n) (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n) := by
          rw [Set.disjoint_left]
          intro ⟨x, y⟩ h1 h2
          exact not_lt_of_ge h1.1.2 h2.1.1
        have hint_sub : ∀ A : Set (ℝ × ℝ), A ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n → MeasurableSet A →
            IntegrableOn (fun z : ℝ × ℝ => z.2) A (N₁.N ω₁) := fun A hA hAm => by
          haveI : IsFiniteMeasure ((N₁.N ω₁).restrict A) :=
            ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hA) (hDfin_ω n)⟩
          exact Integrable.of_bound measurable_snd.aestronglyMeasurable ((1 : ℝ) / 2) (by
            filter_upwards [ae_restrict_mem hAm] with z hz
            have hzD : z.2 ∈ D n := (hA hz).2
            simpa [Real.norm_eq_abs] using hzD.2)
        have hsub1 : Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n :=
          Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hu_le_t)) Set.Subset.rfl
        have hsub2 : Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ D n :=
          Set.prod_mono (fun x hx => ⟨lt_of_le_of_lt u.coe_nonneg hx.1,
            hx.2.trans (by exact_mod_cast hst)⟩) Set.Subset.rfl
        rw [hsplit, setIntegral_union hdisj (measurableSet_Ioc.prod (hDm n))
          (hint_sub _ hsub1 (measurableSet_Ioc.prod (hDm n)))
          (hint_sub _ hsub2 (measurableSet_Ioc.prod (hDm n)))]
        ring
      have hJ_abs : |∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)| ≤ (1 : ℝ) / 2 := by
        obtain ⟨k, hk⟩ := Ioc_subset_overlapping_dyadic ht hu_lt hst m hu_close
        have hmeas_le1 : N₁.N ω₁ (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n) ≤ 1 :=
          (measure_mono (Set.prod_mono hk Set.Subset.rfl)).trans (hm k)
        haveI : IsFiniteMeasure ((N₁.N ω₁).restrict (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt hmeas_le1 ENNReal.one_lt_top⟩
        calc |∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)|
            = ‖∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, ‖z.2‖ ∂(N₁.N ω₁) := norm_integral_le_integral_norm _
          _ ≤ ∫ _z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, ((1 : ℝ) / 2) ∂(N₁.N ω₁) := by
              refine integral_mono_ae
                (Integrable.of_bound measurable_snd.norm.aestronglyMeasurable ((1 : ℝ) / 2) (by
                  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (hDm n))] with z hz
                  simpa [Real.norm_eq_abs] using hz.2.2))
                (integrable_const _) ?_
              filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (hDm n))] with z hz
              simpa [Real.norm_eq_abs] using hz.2.2
          _ = (N₁.N ω₁ (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n)).toReal * ((1 : ℝ) / 2) := by
              rw [setIntegral_const, smul_eq_mul]; rfl
          _ ≤ 1 * ((1 : ℝ) / 2) := by
              have htr : (N₁.N ω₁ (Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n)).toReal ≤ 1 := by
                simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmeas_le1
              linarith
          _ = (1 : ℝ) / 2 := one_mul _
      have hSn_diff : |Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁ -
          Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁| ≤ (1 : ℝ) / 2 + δ / 4 := by
        unfold Kyprianou.compensatedSmallJumpBand
        rw [hJ_eq s hst, hJ_eq u hu_le_t]
        have hrew : ((∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - (s : ℝ) * μ_drift) -
            ((∫ z in Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - (u : ℝ) * μ_drift) =
            (∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - ((s : ℝ) - (u : ℝ)) * μ_drift := by
          rw [← hJ_diff]; ring
        change |((∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - (s : ℝ) * μ_drift) -
            ((∫ z in Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - (u : ℝ) * μ_drift)| ≤ _
        rw [hrew]
        calc |(∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)) - ((s : ℝ) - (u : ℝ)) * μ_drift|
            ≤ |∫ z in Set.Ioc (u : ℝ) (s : ℝ) ×ˢ D n, z.2 ∂(N₁.N ω₁)| + |((s : ℝ) - (u : ℝ)) * μ_drift| :=
              abs_sub _ _
          _ ≤ (1 : ℝ) / 2 + δ / 4 := by linarith
      have h1 : |M s ω₁ - Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁| < δ / 4 := by
        rw [abs_sub_comm]; exact hn_unif s hst
      have h2 := hn_unif u hu_le_t
      have htri : |M s ω₁ - c * l| ≤
          |M s ω₁ - Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁| +
          |Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁ -
            Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁| +
          |Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁ - M u ω₁| +
          |M u ω₁ - c * l| := by
        have hstep1 := abs_sub_le (M s ω₁) (Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁) (c * l)
        have hstep2 := abs_sub_le (Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁)
          (Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁) (c * l)
        have hstep3 := abs_sub_le (Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) u ω₁) (M u ω₁) (c * l)
        linarith
      linarith
    have hmul : |X_small s ω₁ - l| = (2 * r) * |M s ω₁ - c * l| := by
      have heq : X_small s ω₁ - l = (2 * r) * (M s ω₁ - c * l) := by
        dsimp only [X_small, c]
        have h2r : (2 * r : ℝ) ≠ 0 := h2r_pos.ne'
        field_simp [h2r]
      rw [heq, abs_mul, abs_of_pos h2r_pos]
    rw [hmul]
    linarith [mul_le_mul_of_nonneg_left hM_le h2r_pos.le]
  -- Compute exact `charFun (P₁.map (X_small s)) ξ` via DCT from `compensatedSmallJumpBand`
  have hXs_char : ∀ (s : ℝ≥0) (ξ : ℝ),
      charFun (P₁.map (X_small s)) ξ =
        Complex.exp ((((s : ℝ) : ℂ)) *
          ∫ x in B_small,
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 -
              Complex.I * (((ξ * x : ℝ) : ℂ))) ∂ν) := by
    intro s ξ
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with rfl | hs
    · have h0 : X_small 0 = fun _ => 0 := by funext ω₁; simp [X_small, hM_levy.start_zero]
      rw [h0, Measure.map_const, measure_univ, one_smul, charFun_dirac]
      simp
    · let η : ℝ := 2 * r * ξ
      have hcont_exp_ξ : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
      have hcont_exp_η : Continuous (fun x : ℝ => Complex.exp ((η : ℂ) * (x : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
      have hXs_cf : charFun (P₁.map (X_small s)) ξ = charFun (P₁.map (M s)) η := by
        let g : ℝ → ℝ := fun x => (2 * r) * x
        have hg : Measurable g := measurable_const.mul measurable_id
        have hcomp : X_small s = g ∘ M s := rfl
        rw [hcomp, ← Measure.map_map hg (hM_meas s), charFun_apply_real,
          integral_map hg.aemeasurable hcont_exp_ξ.aestronglyMeasurable,
          charFun_apply_real]
        congr 1; funext x; dsimp only [g, η]; congr 1; push_cast; ring
      rw [hXs_cf]
      obtain ⟨ε, _, hε_bnd, hε_tend, hunif_s⟩ := hM_unif s hs
      let E : ℕ → Set ℝ := fun n => {y : ℝ | ε n ≤ |y| ∧ |y| < 1}
      have hEm : ∀ n, MeasurableSet (E n) := fun n =>
        (continuous_abs.measurable measurableSet_Ici).inter (continuous_abs.measurable measurableSet_Iio)
      have hEfin : ∀ n, ν_sc (E n) < ⊤ := fun n =>
        lt_of_le_of_lt (measure_mono (fun y hy => hy.1)) (hν_sc.measure_setOf_abs_ge_lt_top (hε_bnd n).1)
      let S : ℕ → Ω₁ → ℝ := fun n ω₁ => Kyprianou.compensatedSmallJumpBand P₁ ν_sc N₁ (ε n) s ω₁
      have hS_meas : ∀ n, Measurable (S n) := fun n =>
        (Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P₁ ν_sc N₁ _
          (measurableSet_Ioc.prod (hEm n))).sub measurable_const
      -- `charFun (P₁.map (S n)) η` from `finiteRegionPoissonIntegralCh02V3`
      have hS_cf : ∀ n : ℕ,
          charFun (P₁.map (S n)) η =
            Complex.exp ((((s : ℝ) : ℂ)) *
              ∫ y in E n,
                (Complex.exp (Complex.I * (((η * y : ℝ) : ℂ))) - 1 -
                  Complex.I * (((η * y : ℝ) : ℂ))) ∂ν_sc) := by
        intro n
        obtain ⟨_, hZ_cf⟩ := Kyprianou.finiteRegionPoissonIntegralCh02V3 P₁ ν_sc N₁ (E n) (hEm n) (hEfin n)
        let Z_n : Ω₁ → ℝ := fun ω₁ => ∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ E n, z.2 ∂(N₁.N ω₁)
        have hZ_meas : Measurable Z_n :=
          Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P₁ ν_sc N₁ _ (measurableSet_Ioc.prod (hEm n))
        let shift_c : ℝ := (s : ℝ) * ∫ y in E n, y ∂ν_sc
        let sh : ℝ → ℝ := fun x => x - shift_c
        have hsh : Measurable sh := measurable_id.sub measurable_const
        have hSn_eq : S n = sh ∘ Z_n := rfl
        rw [hSn_eq, ← Measure.map_map hsh hZ_meas, charFun_apply_real,
          integral_map hsh.aemeasurable hcont_exp_η.aestronglyMeasurable]
        have hpull : (fun x : ℝ => Complex.exp ((η : ℂ) * ((sh x : ℝ) : ℂ) * Complex.I)) =
            fun x : ℝ => Complex.exp (-(Complex.I * (((η * shift_c : ℝ) : ℂ)))) *
              Complex.exp ((η : ℂ) * (x : ℂ) * Complex.I) := by
          funext x; dsimp only [sh]; rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hpull, integral_const_mul, ← charFun_apply_real, hZ_cf s η, ← Complex.exp_add]
        congr 1
        haveI : IsFiniteMeasure (ν_sc.restrict (E n)) := ⟨by rw [Measure.restrict_apply_univ]; exact hEfin n⟩
        have hint1 : Integrable (fun y : ℝ => Complex.exp (Complex.I * (((η * y : ℝ) : ℂ))) - 1)
            (ν_sc.restrict (E n)) :=
          Integrable.of_bound
            ((Complex.continuous_exp.comp (continuous_const.mul
              (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))).sub
              continuous_const).aestronglyMeasurable 2 (Eventually.of_forall fun y => by
                calc ‖Complex.exp (Complex.I * (((η * y : ℝ) : ℂ))) - 1‖
                    ≤ ‖Complex.exp (Complex.I * (((η * y : ℝ) : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                  _ = 2 := by
                      rw [show Complex.I * (((η * y : ℝ) : ℂ)) = ((η * y : ℝ) : ℂ) * Complex.I by ring,
                        Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num)
        have hint_y : Integrable (fun y : ℝ => y) (ν_sc.restrict (E n)) :=
          Integrable.of_bound measurable_id.aestronglyMeasurable 1 (by
            filter_upwards [ae_restrict_mem (hEm n)] with y hy
            simpa [Real.norm_eq_abs] using hy.2.le)
        have hint2 : Integrable (fun y : ℝ => Complex.I * (((η * y : ℝ) : ℂ))) (ν_sc.restrict (E n)) := by
          have heq : (fun y : ℝ => Complex.I * (((η * y : ℝ) : ℂ))) =
              fun y : ℝ => (Complex.I * (η : ℂ)) * (y : ℂ) := by funext y; push_cast; ring
          rw [heq]
          exact (Complex.ofRealCLM.integrable_comp hint_y).const_mul _
        rw [integral_sub hint1 hint2]
        have heq2 : ∫ y in E n, Complex.I * (((η * y : ℝ) : ℂ)) ∂ν_sc =
            Complex.I * (η : ℂ) * ((∫ y in E n, y ∂ν_sc : ℝ) : ℂ) := by
          have heq : (fun y : ℝ => Complex.I * (((η * y : ℝ) : ℂ))) =
              fun y : ℝ => (Complex.I * (η : ℂ)) * (y : ℂ) := by funext y; push_cast; ring
          rw [heq, integral_const_mul]
          congr 1
          exact Complex.ofRealCLM.integral_comp_comm hint_y
        rw [heq2]; dsimp only [shift_c]; push_cast; ring
      -- LHS limit: `charFun (P₁.map (S n)) η → charFun (P₁.map (M s)) η` by DCT
      have hlhs : Tendsto (fun n : ℕ => charFun (P₁.map (S n)) η) atTop
          (nhds (charFun (P₁.map (M s)) η)) := by
        have hrew : ∀ n, charFun (P₁.map (S n)) η =
            ∫ ω₁, Complex.exp ((η : ℂ) * ((S n ω₁ : ℝ) : ℂ) * Complex.I) ∂P₁ := fun n => by
          rw [charFun_apply_real, integral_map (hS_meas n).aemeasurable hcont_exp_η.aestronglyMeasurable]
        have hrewM : charFun (P₁.map (M s)) η =
            ∫ ω₁, Complex.exp ((η : ℂ) * ((M s ω₁ : ℝ) : ℂ) * Complex.I) ∂P₁ := by
          rw [charFun_apply_real, integral_map (hM_meas s).aemeasurable hcont_exp_η.aestronglyMeasurable]
        simp_rw [hrew, hrewM]
        refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
        · intro n
          exact (hcont_exp_η.measurable.comp (hS_meas n)).aestronglyMeasurable
        · intro n
          filter_upwards with ω₁
          rw [show (η : ℂ) * ((S n ω₁ : ℝ) : ℂ) * Complex.I = ((η * S n ω₁ : ℝ) : ℂ) * Complex.I by
            push_cast; ring, Complex.norm_exp_ofReal_mul_I]
        · filter_upwards [hunif_s] with ω₁ hω₁
          have hSn_tend : Tendsto (fun n => S n ω₁) atTop (nhds (M s ω₁)) := by
            rw [Metric.tendsto_atTop]
            intro δ hδ
            obtain ⟨n₀, hn₀⟩ := hω₁ δ hδ
            exact ⟨n₀, fun n hn => by simpa [Real.dist_eq, S] using hn₀ n hn s le_rfl⟩
          exact (hcont_exp_η.tendsto (M s ω₁)).comp hSn_tend
      -- RHS limit: `∫_{E n} (e^{i η y} - 1 - i η y) ∂ν_sc → ∫ (e^{i η y} - 1 - i η y) ∂ν_sc` by DCT
      let F : ℝ → ℂ := fun y =>
        Complex.exp (Complex.I * (((η * y : ℝ) : ℂ))) - 1 - Complex.I * (((η * y : ℝ) : ℂ))
      have hF_cont : Continuous F :=
        ((Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))).sub
          continuous_const).sub (continuous_const.mul
            (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
      have hmin_int : Integrable (fun y : ℝ => min (1 : ℝ) (y ^ 2)) ν_sc := by
        refine ⟨(continuous_const.min (continuous_id.pow 2)).aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        have hrew : (fun y : ℝ => ‖min (1 : ℝ) (y ^ 2)‖ₑ) = fun y => ENNReal.ofReal (min 1 (y ^ 2)) := by
          funext y
          rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))]
        rw [hrew]; exact hν_sc.2
      have hbound_int : Integrable (fun y : ℝ => (η ^ 2 / 2) * min 1 (y ^ 2)) ν_sc :=
        hmin_int.const_mul (η ^ 2 / 2)
      have hν_ae_small : ∀ᵐ y ∂ν_sc, y ≠ 0 ∧ |y| ≤ (1 : ℝ) / 2 := by
        have h1 : ∀ᵐ y ∂ν_sc, y ≠ 0 := by rw [ae_iff]; simpa using hν_sc.1
        have h2 : ∀ᵐ y ∂ν_sc, |y| ≤ (1 : ℝ) / 2 := by
          rw [ae_iff]
          have heq : {y : ℝ | ¬ |y| ≤ (1 : ℝ) / 2} = {y : ℝ | (1 : ℝ) / 2 < |y|} := by
            ext y; simp
          rw [heq]; exact hν_sc_supp
        exact h1.and h2
      have hF_bd : ∀ᵐ y ∂ν_sc, ‖F y‖ ≤ (η ^ 2 / 2) * min 1 (y ^ 2) := by
        filter_upwards [hν_ae_small] with y ⟨_, hy⟩
        have hy2 : y ^ 2 ≤ 1 := by
          have h1 : |y| ≤ 1 := hy.trans (by norm_num)
          have h2 : |y| ^ 2 ≤ 1 := by nlinarith [abs_nonneg y]
          rwa [sq_abs] at h2
        rw [min_eq_right hy2]
        have h := norm_exp_I_mul_sub_one_sub_le (η * y)
        have hrew : F y = Complex.exp (((η * y : ℝ) : ℂ) * Complex.I) - 1 - ((η * y : ℝ) : ℂ) * Complex.I := by
          dsimp only [F]
          rw [mul_comm Complex.I (((η * y : ℝ) : ℂ))]
        rw [hrew]
        refine h.trans (le_of_eq ?_)
        ring
      have hrhs_int : Tendsto (fun n : ℕ => ∫ y in E n, F y ∂ν_sc) atTop (nhds (∫ y, F y ∂ν_sc)) := by
        simp_rw [← integral_indicator (hEm _)]
        refine tendsto_integral_of_dominated_convergence (fun y => (η ^ 2 / 2) * min 1 (y ^ 2))
          (fun n => (hF_cont.aestronglyMeasurable.indicator (hEm n))) hbound_int ?_ ?_
        · intro n
          filter_upwards [hF_bd] with y hy
          by_cases hyn : y ∈ E n
          · simpa [Set.indicator_of_mem hyn] using hy
          · rw [Set.indicator_of_notMem hyn, norm_zero]
            exact mul_nonneg (by positivity) (le_min (by norm_num) (sq_nonneg y))
        · filter_upwards [hν_ae_small] with y ⟨hy0, hy_le⟩
          have hy_pos : 0 < |y| := abs_pos.mpr hy0
          have hy_lt1 : |y| < 1 := lt_of_le_of_lt hy_le (by norm_num)
          have hev : ∀ᶠ n in atTop, y ∈ E n :=
            (hε_tend.eventually (gt_mem_nhds hy_pos)).mono fun n hn => ⟨hn.le, hy_lt1⟩
          exact tendsto_const_nhds.congr' (hev.mono fun n hn => (Set.indicator_of_mem hn F).symm)
      have hrhs : Tendsto (fun n : ℕ => charFun (P₁.map (S n)) η) atTop
          (nhds (Complex.exp ((((s : ℝ) : ℂ)) * ∫ y, F y ∂ν_sc))) := by
        simp_rw [hS_cf]
        exact (Complex.continuous_exp.tendsto _).comp (hrhs_int.const_mul (((s : ℝ) : ℂ)))
      have heq_cf : charFun (P₁.map (M s)) η = Complex.exp ((((s : ℝ) : ℂ)) * ∫ y, F y ∂ν_sc) :=
        tendsto_nhds_unique hlhs hrhs
      rw [heq_cf]
      congr 2
      rw [integral_map hsc_meas.aemeasurable hF_cont.aestronglyMeasurable]
      congr 1; funext x
      dsimp only [F, sc, η, c]
      have hmul : 2 * r * ξ * (1 / (2 * r) * x) = ξ * x := by field_simp [hr.ne']
      rw [hmul]
  exact ⟨Ω₁, mΩ₁, P₁, hP₁, X_small, hXs_levy, hXs_meas, hXs_cnt, hXs_jump_le, hXs_char⟩

private lemma largeJump_levy_component
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₂)
      (X_large : ℝ≥0 → Ω₂ → ℝ) (E_large1 : Set Ω₂) (τ : Ω₂ → ℝ≥0),
      ProbabilityTheory.IsLevyProcess X_large P₂ ∧
      (∀ s : ℝ≥0, Measurable (X_large s)) ∧
      (∀ (s : ℝ≥0) (ξ : ℝ),
        charFun (P₂.map (X_large s)) ξ =
          Complex.exp ((((s : ℝ) : ℂ)) *
            ∫ x in {x : ℝ | r < |x|},
              (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)) ∧
      MeasurableSet E_large1 ∧
      P₂ E_large1 = ENNReal.ofReal (1 - Real.exp (-(t : ℝ) * (ν {x : ℝ | r < |x|}).toReal)) ∧
      Measurable τ ∧
      (∀ x : ℝ≥0, P₂ {ω₂ | ω₂ ∈ E_large1 ∧ τ ω₂ = x} = 0) ∧
      (∀ᵐ ω₂ ∂P₂, ω₂ ∉ E_large1 → ∀ s ≤ t, X_large s ω₂ = 0) ∧
      (∀ᵐ ω₂ ∂P₂, ω₂ ∈ E_large1 →
        0 < τ ω₂ ∧ τ ω₂ ≤ t ∧ (∀ u < τ ω₂, X_large u ω₂ = 0) ∧ r < |X_large (τ ω₂) ω₂|) := by
  haveI : SigmaFinite ν := levyMeasure_sigmaFinite hν
  let B : Set ℝ := {x : ℝ | r < |x|}
  let B_pos : Set ℝ := {x : ℝ | r < x}
  let B_neg : Set ℝ := {x : ℝ | x < -r}
  have hBm : MeasurableSet B := continuous_abs.measurable measurableSet_Ioi
  have hBpm : MeasurableSet B_pos := measurableSet_Ioi
  have hBnm : MeasurableSet B_neg := measurableSet_Iio
  have hBfin : ν B < ⊤ := levyMeasure_abs_gt_lt_top hν hr
  have hBp_sub : B_pos ⊆ B := fun x hx => lt_of_lt_of_le hx (le_abs_self x)
  have hBn_sub : B_neg ⊆ B := fun x hx => by
    have hx' : x < -r := hx
    show r < |x|
    rw [abs_of_neg (lt_trans hx' (by linarith))]; linarith
  have hBpfin : ν B_pos < ⊤ := lt_of_le_of_lt (measure_mono hBp_sub) hBfin
  have hBnfin : ν B_neg < ⊤ := lt_of_le_of_lt (measure_mono hBn_sub) hBfin
  have hB_union : B = B_pos ∪ B_neg := by
    ext x; simp only [B, B_pos, B_neg, Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  have hB_disj : Disjoint B_pos B_neg := by
    rw [Set.disjoint_left]; intro x h1 h2; change r < x at h1; change x < -r at h2; linarith
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, ⟨N₂⟩⟩ := Kyprianou.poissonRandomMeasureExists ν
  letI : MeasurableSpace Ω₂ := mΩ₂
  letI : IsProbabilityMeasure P₂ := hP₂
  obtain ⟨hXl_levy, hXl_char⟩ := Kyprianou.finiteRegionPoissonIntegralCh02V3 P₂ ν N₂ B hBm hBfin
  let X_large : ℝ≥0 → Ω₂ → ℝ := fun s ω₂ => ∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B, z.2 ∂(N₂.N ω₂)
  have hXl_meas : ∀ s : ℝ≥0, Measurable (X_large s) := fun s =>
    Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P₂ ν N₂ _ (measurableSet_Ioc.prod hBm)
  let cnt : ℝ≥0 → Ω₂ → ℝ≥0∞ := fun s ω₂ => N₂.N ω₂ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B)
  have hcnt_meas : ∀ s : ℝ≥0, Measurable (cnt s) := fun s =>
    N₂.measurable_eval (measurableSet_Ioc.prod hBm)
  have hcnt_mono : ∀ ω₂, Monotone (fun s => cnt s ω₂) := fun ω₂ s₁ s₂ hle =>
    measure_mono (Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hle)) Set.Subset.rfl)
  let E_large1 : Set Ω₂ := {ω₂ | (1 : ℝ≥0∞) ≤ cnt t ω₂}
  have hE1_meas : MeasurableSet E_large1 := hcnt_meas t measurableSet_Ici
  have hRef_fin : ∀ (u : ℝ≥0) (A : Set ℝ), ν A < ⊤ →
      LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A) ≠ ⊤ := fun u A hA => by
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) (u : ℝ) ⊆ Set.Ici 0 from fun _ hx => le_of_lt hx.1),
      Real.volume_Ioc, sub_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA.ne
  -- Compute `P₂ E_large1`
  have hcnt_t_nat : ∀ᵐ ω₂ ∂P₂, ∃ k : ℕ, cnt t ω₂ = (k : ℝ≥0∞) :=
    prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBm) (hRef_fin t B hBfin)
  have hP_E1 : P₂ E_large1 = ENNReal.ofReal (1 - Real.exp (-(t : ℝ) * (ν B).toReal)) := by
    have hae_eq : E_large1 =ᵐ[P₂] ({ω₂ | cnt t ω₂ = 0}ᶜ) := by
      filter_upwards [hcnt_t_nat] with ω₂ ⟨k, hk⟩
      change (ω₂ ∈ E_large1) = (ω₂ ∈ {ω₂ | cnt t ω₂ = 0}ᶜ)
      simp only [E_large1, Set.mem_ofPred_eq, Set.mem_compl_iff, hk]
      cases k with
      | zero => simp
      | succ k => simp
    have hmeas0 : MeasurableSet {ω₂ | cnt t ω₂ = 0} := hcnt_meas t (measurableSet_singleton 0)
    have hstep1 : P₂ E_large1 = 1 - P₂ {ω₂ | cnt t ω₂ = 0} := by
      calc P₂ E_large1 = P₂ ({ω₂ | cnt t ω₂ = 0}ᶜ) := measure_congr hae_eq
        _ = P₂ Set.univ - P₂ {ω₂ | cnt t ω₂ = 0} := measure_compl hmeas0 (measure_ne_top _ _)
        _ = 1 - P₂ {ω₂ | cnt t ω₂ = 0} := by rw [measure_univ]
    rw [hstep1]
    have hP0 : P₂ {ω₂ | cnt t ω₂ = 0} = ENNReal.ofReal (Real.exp (-(t : ℝ) * (ν B).toReal)) := by
      have hpre : {ω₂ | cnt t ω₂ = 0} = cnt t ⁻¹' {0} := rfl
      rw [hpre, ← Measure.map_apply (hcnt_meas t) (measurableSet_singleton 0),
        N₂.poisson_law (measurableSet_Ioc.prod hBm) (hRef_fin t B hBfin)]
      have h0 := poissonMeasureENN_apply_nat
        (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toNNReal 0
      simp only [Nat.cast_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at h0
      rw [h0]
      congr 2
      have htr : ((LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toNNReal : ℝ) =
          (t : ℝ) * (ν B).toReal := by
        change (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal = _
        unfold LevyStochCalc.Poisson.referenceIntensity
        rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
          Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) (t : ℝ) ⊆ Set.Ici 0 from fun _ hx => le_of_lt hx.1),
          Real.volume_Ioc, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]
      rw [htr]; ring
    rw [hP0, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  -- Define measurable first-jump time `τ`
  open Classical in
  let τ : Ω₂ → ℝ≥0 := fun ω₂ =>
    if ω₂ ∈ E_large1 then sInf {s : ℝ≥0 | s ≤ t ∧ (1 : ℝ≥0∞) ≤ cnt s ω₂} else 0
  have hτ_le_t : ∀ ω₂, τ ω₂ ≤ t := fun ω₂ => by
    dsimp only [τ]
    split_ifs with h1
    · exact csInf_le ⟨0, fun _ _ => zero_le'⟩ ⟨le_rfl, h1⟩
    · exact zero_le'
  have hτ_meas : Measurable τ := by
    refine measurable_of_Iic fun a => ?_
    by_cases hta : t ≤ a
    · have huniv : τ ⁻¹' Set.Iic a = Set.univ := by
        ext ω₂; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (hτ_le_t ω₂).trans hta
      rw [huniv]; exact MeasurableSet.univ
    · have heq : τ ⁻¹' Set.Iic a =
          E_large1ᶜ ∪ (E_large1 ∩ ⋂ n : ℕ, {ω₂ | (1 : ℝ≥0∞) ≤ cnt (min t (a + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))) ω₂}) := by
        ext ω₂
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_compl_iff,
          Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
        by_cases h1 : ω₂ ∈ E_large1
        · simp only [τ, h1, ↓reduceIte, not_true_eq_false, false_or, true_and]
          let S : Set ℝ≥0 := {s : ℝ≥0 | s ≤ t ∧ (1 : ℝ≥0∞) ≤ cnt s ω₂}
          have hSne : S.Nonempty := ⟨t, le_rfl, h1⟩
          have hSbdd : BddBelow S := ⟨0, fun _ _ => zero_le'⟩
          constructor
          · intro hle n
            have hlt : sInf S < a + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by
              have hpos : (0 : ℝ≥0) < (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by positivity
              exact lt_of_le_of_lt hle (lt_add_of_pos_right a hpos)
            obtain ⟨s, hs, hslt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
            exact hs.2.trans (hcnt_mono ω₂ (le_min hs.1 hslt.le))
          · intro hall
            have hle_n : ∀ n : ℕ, ((sInf S : ℝ≥0) : ℝ) ≤ (a : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := fun n => by
              have hmem : min t (a + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) ∈ S :=
                ⟨min_le_left _ _, hall n⟩
              have h1' : sInf S ≤ a + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) :=
                (csInf_le hSbdd hmem).trans (min_le_right _ _)
              have h2' : ((sInf S : ℝ≥0) : ℝ) ≤ ((a + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) :=
                NNReal.coe_le_coe.mpr h1'
              simpa using h2'
            have htend : Tendsto (fun n : ℕ => (a : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds (a : ℝ)) := by
              simpa using (tendsto_const_nhds (x := (a : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
            rw [← NNReal.coe_le_coe]
            exact ge_of_tendsto' htend hle_n
        · simp [τ, h1]
      rw [heq]
      exact hE1_meas.compl.union (hE1_meas.inter (MeasurableSet.iInter fun n =>
        hcnt_meas _ measurableSet_Ici))
  -- Right-continuity of `s ↦ N₂.N ω₂ (Ioc 0 s ×ˢ A)` when finite at `t`
  have hrc_N : ∀ (ω₂ : Ω₂) (A : Set ℝ), MeasurableSet A → ∀ (s : ℝ≥0), s ≤ t →
      N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) < ⊤ →
      ∀ (u : ℕ → ℝ≥0), Antitone u → (∀ n, s ≤ u n) → (∀ n, u n ≤ t) → Tendsto u atTop (nhds s) →
      Tendsto (fun n => N₂.N ω₂ (Set.Ioc (0 : ℝ) (u n : ℝ) ×ˢ A)) atTop
        (nhds (N₂.N ω₂ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A))) := by
    intro ω₂ A hAm s _ hfin_t u hu_anti hu_ge hu_le hu_tend
    let Sets : ℕ → Set (ℝ × ℝ) := fun n => Set.Ioc (0 : ℝ) (u n : ℝ) ×ˢ A
    have hSets_anti : Antitone Sets := fun i j hij =>
      Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hu_anti hij)) Set.Subset.rfl
    have hSets_inter : (⋂ n : ℕ, Sets n) = Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A := by
      ext ⟨x, y⟩
      simp only [Sets, Set.mem_iInter, Set.mem_prod, Set.mem_Ioc]
      constructor
      · intro h
        refine ⟨⟨(h 0).1.1, ge_of_tendsto' (NNReal.continuous_coe.continuousAt.tendsto.comp hu_tend)
          fun n => (h n).1.2⟩, (h 0).2⟩
      · rintro ⟨⟨hx0, hxs⟩, hy⟩ n
        exact ⟨⟨hx0, hxs.trans (by exact_mod_cast hu_ge n)⟩, hy⟩
    rw [← hSets_inter]
    exact tendsto_measure_iInter_atTop (fun _ => (measurableSet_Ioc.prod hAm).nullMeasurableSet)
      hSets_anti ⟨0, (lt_of_le_of_lt (measure_mono
        (Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hu_le 0)) Set.Subset.rfl)) hfin_t).ne⟩
  -- For any `ω₂ ∈ E_large1` with `cnt t ω₂ < ⊤`, we have `1 ≤ cnt (τ ω₂) ω₂` and `0 < τ ω₂`
  have hcnt_τ_ge1 : ∀ ω₂, ω₂ ∈ E_large1 → cnt t ω₂ < ⊤ → (1 : ℝ≥0∞) ≤ cnt (τ ω₂) ω₂ := by
    intro ω₂ h1 hfin_t
    let u : ℕ → ℝ≥0 := fun n => min t (τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))
    have hu_anti : Antitone u := fun i j hij => by
      dsimp only [u]; gcongr
    have hu_ge : ∀ n, τ ω₂ ≤ u n := fun n => le_min (hτ_le_t ω₂) le_self_add
    have hu_le : ∀ n, u n ≤ t := fun n => min_le_left _ _
    have hu_tend : Tendsto u atTop (nhds (τ ω₂)) := by
      rw [← NNReal.tendsto_coe]
      have hadd : Tendsto (fun n : ℕ => (τ ω₂ : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds (τ ω₂ : ℝ)) := by
        simpa using (tendsto_const_nhds (x := (τ ω₂ : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
      have hmin : Tendsto (fun n : ℕ => min (t : ℝ) ((τ ω₂ : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)))
          atTop (nhds (min (t : ℝ) (τ ω₂ : ℝ))) := tendsto_const_nhds.min hadd
      rw [min_eq_right (show (τ ω₂ : ℝ) ≤ (t : ℝ) by exact_mod_cast hτ_le_t ω₂)] at hmin
      simpa [u] using hmin
    have hcnt_u_ge1 : ∀ n : ℕ, (1 : ℝ≥0∞) ≤ cnt (u n) ω₂ := fun n => by
      let S : Set ℝ≥0 := {s : ℝ≥0 | s ≤ t ∧ (1 : ℝ≥0∞) ≤ cnt s ω₂}
      have hSne : S.Nonempty := ⟨t, le_rfl, h1⟩
      have hSbdd : BddBelow S := ⟨0, fun _ _ => zero_le'⟩
      have hτ_eq : τ ω₂ = sInf S := by simp [τ, h1, S]
      have hlt : sInf S < τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by
        rw [← hτ_eq]; exact lt_add_of_pos_right _ (by positivity)
      obtain ⟨s, hs, hslt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      exact hs.2.trans (hcnt_mono ω₂ (le_min hs.1 hslt.le))
    have htend := hrc_N ω₂ B hBm (τ ω₂) (hτ_le_t ω₂) hfin_t u hu_anti hu_ge hu_le hu_tend
    exact ge_of_tendsto' htend hcnt_u_ge1
  -- All rational-time counts in `B`, `B_pos`, `B_neg` are natural-valued a.s.
  have hrat_nat : ∀ᵐ ω₂ ∂P₂, ∀ q : ℚ≥0,
      (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B) = (k : ℝ≥0∞)) ∧
      (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B_pos) = (k : ℝ≥0∞)) ∧
      (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B_neg) = (k : ℝ≥0∞)) :=
    ae_all_iff.mpr fun q =>
      (prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBm) (hRef_fin (q : ℝ≥0) B hBfin)).and
        ((prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBpm) (hRef_fin (q : ℝ≥0) B_pos hBpfin)).and
          (prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBnm) (hRef_fin (q : ℝ≥0) B_neg hBnfin)))
  have ht_nat_pn : ∀ᵐ ω₂ ∂P₂,
      (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B_pos) = (k : ℝ≥0∞)) ∧
      (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B_neg) = (k : ℝ≥0∞)) :=
    (prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBpm) (hRef_fin t B_pos hBpfin)).and
      (prm_nat_valued_ae N₂ (measurableSet_Ioc.prod hBnm) (hRef_fin t B_neg hBnfin))
  -- For every fixed `x : ℝ≥0`, `P₂ {ω₂ | ω₂ ∈ E_large1 ∧ τ ω₂ = x} = 0`
  have hτ_atomless : ∀ x : ℝ≥0, P₂ {ω₂ | ω₂ ∈ E_large1 ∧ τ ω₂ = x} = 0 := by
    intro x
    have hsing_zero : ∀ᵐ ω₂ ∂P₂, N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0 := by
      have hm : MeasurableSet ({(x : ℝ)} ×ˢ B) := (measurableSet_singleton _).prod hBm
      have hint0 : LevyStochCalc.Poisson.referenceIntensity ν ({(x : ℝ)} ×ˢ B) = 0 := by
        unfold LevyStochCalc.Poisson.referenceIntensity
        rw [Measure.prod_prod, Measure.restrict_apply (measurableSet_singleton _)]
        have hvol0 : volume ({(x : ℝ)} ∩ Set.Ici (0 : ℝ)) = 0 :=
          le_antisymm ((measure_mono Set.inter_subset_left).trans (le_of_eq Real.volume_singleton)) zero_le'
        rw [hvol0, zero_mul]
      have hP0 : P₂ {ω₂ | N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0} = 1 := by
        have hpre : {ω₂ | N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0} =
            (fun ω₂ => N₂.N ω₂ ({(x : ℝ)} ×ˢ B)) ⁻¹' {0} := rfl
        rw [hpre, ← Measure.map_apply (N₂.measurable_eval hm) (measurableSet_singleton 0),
          N₂.poisson_law hm (by rw [hint0]; exact ENNReal.zero_ne_top)]
        simpa [hint0] using poissonMeasureENN_apply_nat 0 0
      rw [ae_iff]
      have hmeas0 : MeasurableSet {ω₂ | N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0} :=
        N₂.measurable_eval hm (measurableSet_singleton 0)
      have hcompl : {ω₂ | ¬ N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0} =
          {ω₂ | N₂.N ω₂ ({(x : ℝ)} ×ˢ B) = 0}ᶜ := rfl
      rw [hcompl, measure_compl hmeas0 (measure_ne_top _ _), measure_univ, hP0, tsub_self]
    have hae_not : ∀ᵐ ω₂ ∂P₂, ¬ (ω₂ ∈ E_large1 ∧ τ ω₂ = x) := by
      filter_upwards [hcnt_t_nat, hrat_nat, hsing_zero] with ω₂ ⟨kt, hkt⟩ hrat hsing
      rintro ⟨h1, hτx⟩
      have hfin_t : cnt t ω₂ < ⊤ := by rw [hkt]; exact ENNReal.natCast_lt_top kt
      have hge1 : (1 : ℝ≥0∞) ≤ cnt x ω₂ := hτx ▸ hcnt_τ_ge1 ω₂ h1 hfin_t
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with rfl | hx_pos
      · have h0 : cnt 0 ω₂ = 0 := by simp [cnt]
        rw [h0] at hge1; exact absurd hge1 (by norm_num)
      · -- For every `u < x`, `cnt u ω₂ = 0`
        have hlt_zero : ∀ u : ℝ≥0, u < x → cnt u ω₂ = 0 := by
          intro u hux
          obtain ⟨q_rat, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < (x : ℝ) by exact_mod_cast hux)
          let q : ℚ≥0 := ⟨q_rat, by
            have : (0 : ℝ) ≤ (q_rat : ℝ) := le_trans u.coe_nonneg hq1.le
            exact_mod_cast this⟩
          have huq : u ≤ (q : ℝ≥0) := by change (u : ℝ) ≤ (q_rat : ℝ); exact hq1.le
          have hqx : (q : ℝ≥0) < x := by change (q_rat : ℝ) < (x : ℝ); exact hq2
          have hq_not_ge1 : ¬ ((1 : ℝ≥0∞) ≤ cnt (q : ℝ≥0) ω₂) := by
            intro hge
            have hqt : (q : ℝ≥0) ≤ t := hqx.le.trans (hτx ▸ hτ_le_t ω₂)
            have hle_τ : τ ω₂ ≤ (q : ℝ≥0) := by
              simp only [τ, h1, ↓reduceIte]
              exact csInf_le ⟨0, fun _ _ => zero_le'⟩ ⟨hqt, hge⟩
            exact not_lt_of_ge (hτx ▸ hle_τ) hqx
          obtain ⟨kq, hkq⟩ := (hrat q).1
          have hkq0 : kq = 0 := by
            by_contra hne
            have hge : (1 : ℝ≥0∞) ≤ (kq : ℝ≥0∞) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
            exact hq_not_ge1 (by change (1 : ℝ≥0∞) ≤ N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B); rw [hkq]; exact hge)
          exact le_antisymm ((hcnt_mono ω₂ huq).trans (by
            change N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B) ≤ 0
            rw [hkq, hkq0]; simp)) zero_le'
        -- Express `Ioc 0 x ×ˢ B = ({x} ×ˢ B) ∪ ⋃ n, (Ioc 0 u_n ×ˢ B)` with `u_n < x`
        let un : ℕ → ℝ≥0 := fun n => ⟨max 0 ((x : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)), le_max_left _ _⟩
        have hun_lt : ∀ n : ℕ, un n < x := fun n => by
          change max 0 ((x : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) < (x : ℝ)
          have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx_pos
          exact max_lt hx' (sub_lt_self _ (by positivity))
        have hsub : Set.Ioc (0 : ℝ) (x : ℝ) ×ˢ B ⊆
            ({(x : ℝ)} ×ˢ B) ∪ ⋃ n : ℕ, (Set.Ioc (0 : ℝ) (un n : ℝ) ×ˢ B) := by
          intro ⟨a, b⟩ ⟨⟨ha0, hax⟩, hb⟩
          rcases eq_or_lt_of_le hax with rfl | hlt
          · exact Or.inl ⟨rfl, hb⟩
          · refine Or.inr (Set.mem_iUnion.mpr ?_)
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
            refine ⟨n, ⟨ha0, ?_⟩, hb⟩
            change a ≤ max 0 ((x : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))
            have hn' : 1 / ((n + 1 : ℕ) : ℝ) < (x : ℝ) - a := by push_cast; exact hn
            exact le_trans (by linarith) (le_max_right _ _)
        have hzero_union : N₂.N ω₂ (⋃ n : ℕ, (Set.Ioc (0 : ℝ) (un n : ℝ) ×ˢ B)) = 0 :=
          measure_iUnion_null fun n => hlt_zero (un n) (hun_lt n)
        have hcnt_x0 : cnt x ω₂ = 0 := by
          refine le_antisymm ?_ zero_le'
          calc cnt x ω₂
              ≤ N₂.N ω₂ (({(x : ℝ)} ×ˢ B) ∪ ⋃ n : ℕ, (Set.Ioc (0 : ℝ) (un n : ℝ) ×ˢ B)) :=
                measure_mono hsub
            _ ≤ N₂.N ω₂ ({(x : ℝ)} ×ˢ B) + N₂.N ω₂ (⋃ n : ℕ, (Set.Ioc (0 : ℝ) (un n : ℝ) ×ˢ B)) :=
                measure_union_le _ _
            _ = 0 := by rw [hsing, hzero_union, add_zero]
        rw [hcnt_x0] at hge1; exact absurd hge1 (by norm_num)
    simpa [ae_iff] using hae_not
  -- On `E_large1ᶜ`, `X_large s ω₂ = 0` for all `s ≤ t`
  have hnotE1_zero : ∀ᵐ ω₂ ∂P₂, ω₂ ∉ E_large1 → ∀ s ≤ t, X_large s ω₂ = 0 := by
    filter_upwards [hcnt_t_nat] with ω₂ ⟨kt, hkt⟩ hnot s hst
    have hkt0 : kt = 0 := by
      by_contra hne
      have hge : (1 : ℝ≥0∞) ≤ (kt : ℝ≥0∞) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      exact hnot (by change (1 : ℝ≥0∞) ≤ cnt t ω₂; rw [hkt]; exact hge)
    have hcnt_s0 : cnt s ω₂ = 0 :=
      le_antisymm ((hcnt_mono ω₂ hst).trans (by dsimp only; rw [hkt, hkt0]; simp)) zero_le'
    change ∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B, z.2 ∂(N₂.N ω₂) = 0
    have hres0 : (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B) = 0 :=
      Measure.restrict_eq_zero.mpr hcnt_s0
    rw [hres0]; simp
  -- Almost surely there exists `M : ℕ` such that `N₂.N ω₂ (Ioc 0 t ×ˢ {x | M < |x|}) = 0`
  have hbdd_mark : ∀ᵐ ω₂ ∂P₂, ∃ M : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | (M : ℝ) < |x|}) = 0 := by
    let Tail : ℕ → Set ℝ := fun M => {x : ℝ | (M : ℝ) < |x|}
    have hTailm : ∀ M, MeasurableSet (Tail M) := fun M => continuous_abs.measurable measurableSet_Ioi
    obtain ⟨M₀, hM₀⟩ := exists_nat_gt r
    have hTail_fin : ∀ M ≥ M₀, ν (Tail M) < ⊤ := fun M hM =>
      lt_of_le_of_lt (measure_mono fun x hx => lt_trans (lt_of_lt_of_le hM₀ (by exact_mod_cast hM)) hx) hBfin
    have hTail_tend : Tendsto (fun M : ℕ => ν (Tail (M + M₀))) atTop (nhds 0) := by
      have hanti : Antitone (fun M : ℕ => Tail (M + M₀)) := fun i j hij x hx =>
        lt_of_le_of_lt (show ((i + M₀ : ℕ) : ℝ) ≤ ((j + M₀ : ℕ) : ℝ) by
          exact_mod_cast Nat.add_le_add_right hij M₀) hx
      have hinter : (⋂ M : ℕ, Tail (M + M₀)) = ∅ := by
        ext x; simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, Tail, Set.mem_ofPred_eq]
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        exact ⟨n, not_lt_of_ge (by push_cast; linarith)⟩
      simpa [hinter, Function.comp_def] using tendsto_measure_iInter_atTop
        (fun M => (hTailm (M + M₀)).nullMeasurableSet) hanti ⟨0, by simpa using (hTail_fin M₀ le_rfl).ne⟩
    let Ev : ℕ → Set Ω₂ := fun M => {ω₂ | N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) ≠ 0}
    have hEv_le : ∀ M : ℕ, P₂ (Ev M) ≤ ENNReal.ofReal ((t : ℝ) * (ν (Tail (M + M₀))).toReal) := fun M => by
      have hm : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) :=
        measurableSet_Ioc.prod (hTailm (M + M₀))
      have hfin := hRef_fin t (Tail (M + M₀)) (hTail_fin (M + M₀) (Nat.le_add_left M₀ M))
      have hP0 : P₂ {ω₂ | N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) = 0} =
          ENNReal.ofReal (Real.exp (-(t : ℝ) * (ν (Tail (M + M₀))).toReal)) := by
        have hpre : {ω₂ | N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) = 0} =
            (fun ω₂ => N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀))) ⁻¹' {0} := rfl
        rw [hpre, ← Measure.map_apply (N₂.measurable_eval hm) (measurableSet_singleton 0),
          N₂.poisson_law hm hfin]
        have h0 := poissonMeasureENN_apply_nat
          (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀))).toNNReal 0
        simp only [Nat.cast_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at h0
        rw [h0]
        congr 2
        have htr : ((LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀))).toNNReal : ℝ) =
            (t : ℝ) * (ν (Tail (M + M₀))).toReal := by
          change (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀))).toReal = _
          unfold LevyStochCalc.Poisson.referenceIntensity
          rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
            Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) (t : ℝ) ⊆ Set.Ici 0 from fun _ hx => le_of_lt hx.1),
            Real.volume_Ioc, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]
        rw [htr]; ring
      have hmeas0 : MeasurableSet {ω₂ | N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) = 0} :=
        N₂.measurable_eval hm (measurableSet_singleton 0)
      have hcompl : Ev M = {ω₂ | N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail (M + M₀)) = 0}ᶜ := rfl
      rw [hcompl, measure_compl hmeas0 (measure_ne_top _ _),
        measure_univ, hP0, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Real.add_one_le_exp (-(t : ℝ) * (ν (Tail (M + M₀))).toReal)
      linarith
    have hEv_tend : Tendsto (fun M : ℕ => ENNReal.ofReal ((t : ℝ) * (ν (Tail (M + M₀))).toReal))
        atTop (nhds 0) := by
      have htr : Tendsto (fun M : ℕ => (ν (Tail (M + M₀))).toReal) atTop (nhds 0) := by
        have hc := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hTail_tend
        simpa [Function.comp_def, ENNReal.toReal_zero] using hc
      have hmul : Tendsto (fun M : ℕ => (t : ℝ) * (ν (Tail (M + M₀))).toReal) atTop (nhds 0) := by
        simpa using htr.const_mul (t : ℝ)
      have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
      simpa [Function.comp_def, ENNReal.ofReal_zero] using hc
    have hinter0 : P₂ (⋂ M : ℕ, Ev M) = 0 :=
      le_antisymm (ge_of_tendsto' hEv_tend fun M =>
        (measure_mono (Set.iInter_subset Ev M)).trans (hEv_le M)) zero_le'
    rw [ae_iff]
    have hsub : {ω₂ | ¬ ∃ M : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Tail M) = 0} ⊆ ⋂ M : ℕ, Ev M := by
      intro ω₂ hω
      simp only [Set.mem_ofPred_eq, not_exists] at hω
      exact Set.mem_iInter.mpr fun M => hω (M + M₀)
    exact le_antisymm ((measure_mono hsub).trans (le_of_eq hinter0)) zero_le'
  -- Main a.e. jump statement on `E_large1`
  have hE1_jump : ∀ᵐ ω₂ ∂P₂, ω₂ ∈ E_large1 →
      0 < τ ω₂ ∧ τ ω₂ ≤ t ∧ (∀ u < τ ω₂, X_large u ω₂ = 0) ∧ r < |X_large (τ ω₂) ω₂| := by
    filter_upwards [hcnt_t_nat, hrat_nat, ht_nat_pn, prm_no_double_jump_ae N₂ hBm hBfin ht,
      hbdd_mark] with ω₂ ⟨kt, hkt⟩ hrat ⟨⟨kp, hkp⟩, ⟨kn, hkn⟩⟩ ⟨m, hm⟩ ⟨M, hM⟩ h1
    have hfin_t : cnt t ω₂ < ⊤ := by rw [hkt]; exact ENNReal.natCast_lt_top kt
    have hfin_tp : N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B_pos) < ⊤ := by
      rw [hkp]; exact ENNReal.natCast_lt_top kp
    have hfin_tn : N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B_neg) < ⊤ := by
      rw [hkn]; exact ENNReal.natCast_lt_top kn
    have hge1 : (1 : ℝ≥0∞) ≤ cnt (τ ω₂) ω₂ := hcnt_τ_ge1 ω₂ h1 hfin_t
    have hτ_pos : 0 < τ ω₂ := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ τ ω₂) with h0 | hpos
      · have : cnt (τ ω₂) ω₂ = 0 := by rw [← h0]; simp [cnt]
        rw [this] at hge1; exact absurd hge1 (by norm_num)
      · exact hpos
    have hlt_cnt0 : ∀ u : ℝ≥0, u < τ ω₂ → cnt u ω₂ = 0 := by
      intro u hu
      obtain ⟨q_rat, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < (τ ω₂ : ℝ) by exact_mod_cast hu)
      let q : ℚ≥0 := ⟨q_rat, by
        have : (0 : ℝ) ≤ (q_rat : ℝ) := le_trans u.coe_nonneg hq1.le
        exact_mod_cast this⟩
      have huq : u ≤ (q : ℝ≥0) := by change (u : ℝ) ≤ (q_rat : ℝ); exact hq1.le
      have hqτ : (q : ℝ≥0) < τ ω₂ := by change (q_rat : ℝ) < (τ ω₂ : ℝ); exact hq2
      have hq_not_ge1 : ¬ ((1 : ℝ≥0∞) ≤ cnt (q : ℝ≥0) ω₂) := by
        intro hge
        have hle : τ ω₂ ≤ (q : ℝ≥0) := by
          simp only [τ, h1, ↓reduceIte]
          exact csInf_le ⟨0, fun _ _ => zero_le'⟩ ⟨hqτ.le.trans (hτ_le_t ω₂), hge⟩
        exact not_lt_of_ge hle hqτ
      obtain ⟨kq, hkq⟩ := (hrat q).1
      have hkq0 : kq = 0 := by
        by_contra hne
        have hge : (1 : ℝ≥0∞) ≤ (kq : ℝ≥0∞) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
        exact hq_not_ge1 (by change (1 : ℝ≥0∞) ≤ N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B); rw [hkq]; exact hge)
      exact le_antisymm ((hcnt_mono ω₂ huq).trans (by
        change N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ B) ≤ 0
        rw [hkq, hkq0]; simp)) zero_le'
    have hlt_Xl0 : ∀ u < τ ω₂, X_large u ω₂ = 0 := fun u hu => by
      change ∫ z in Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B, z.2 ∂(N₂.N ω₂) = 0
      have hres0 : (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B) = 0 :=
        Measure.restrict_eq_zero.mpr (hlt_cnt0 u hu)
      rw [hres0]; simp
    -- Show `cnt (τ ω₂) ω₂ = 1` using `hm`
    have hcnt_τ_eq1 : cnt (τ ω₂) ω₂ = 1 := by
      refine le_antisymm ?_ hge1
      have hτposR : (0 : ℝ) < (τ ω₂ : ℝ) := by exact_mod_cast hτ_pos
      have htposR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      let δ : ℝ := min ((τ ω₂ : ℝ) / 2) ((t : ℝ) / (2 : ℝ) ^ m / 2)
      have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
      let u : ℝ≥0 := ⟨(τ ω₂ : ℝ) - δ, by linarith [min_le_left ((τ ω₂ : ℝ) / 2) ((t : ℝ) / (2 : ℝ) ^ m / 2)]⟩
      have hu_lt : u < τ ω₂ := by change (τ ω₂ : ℝ) - δ < (τ ω₂ : ℝ); linarith
      have hu_close : (τ ω₂ : ℝ) - (u : ℝ) < (t : ℝ) / (2 : ℝ) ^ m := by
        change (τ ω₂ : ℝ) - ((τ ω₂ : ℝ) - δ) < (t : ℝ) / (2 : ℝ) ^ m
        have h1' : δ ≤ (t : ℝ) / (2 : ℝ) ^ m / 2 := min_le_right _ _
        have h2' : (0 : ℝ) < (t : ℝ) / (2 : ℝ) ^ m := by positivity
        linarith
      obtain ⟨k, hk⟩ := Ioc_subset_overlapping_dyadic ht hu_lt (hτ_le_t ω₂) m hu_close
      have hsub : Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B ⊆
          (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B) ∪ (Set.Ioc (u : ℝ) (τ ω₂ : ℝ) ×ˢ B) := by
        intro ⟨x, y⟩ ⟨⟨hx0, hxτ⟩, hy⟩
        by_cases hxu : x ≤ (u : ℝ)
        · exact Or.inl ⟨⟨hx0, hxu⟩, hy⟩
        · exact Or.inr ⟨⟨lt_of_not_ge hxu, hxτ⟩, hy⟩
      calc cnt (τ ω₂) ω₂
          ≤ N₂.N ω₂ ((Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B) ∪ (Set.Ioc (u : ℝ) (τ ω₂ : ℝ) ×ˢ B)) :=
            measure_mono hsub
        _ ≤ cnt u ω₂ + N₂.N ω₂ (Set.Ioc (u : ℝ) (τ ω₂ : ℝ) ×ˢ B) := measure_union_le _ _
        _ = N₂.N ω₂ (Set.Ioc (u : ℝ) (τ ω₂ : ℝ) ×ˢ B) := by rw [hlt_cnt0 u hu_lt, zero_add]
        _ ≤ N₂.N ω₂ (Set.Ioc ((k.1 : ℝ) * (t : ℝ) / (2 : ℝ) ^ m)
              (((k.1 + 2 : ℕ) : ℝ) * (t : ℝ) / (2 : ℝ) ^ m) ×ˢ B) :=
            measure_mono (Set.prod_mono hk Set.Subset.rfl)
        _ ≤ 1 := hm k
    -- Show `N₂.N ω₂ (Ioc 0 (τ ω₂) ×ˢ B_pos)` and `B_neg` are natural-valued and sum to `1`
    have hnat_at_τ : ∀ (A : Set ℝ), MeasurableSet A →
        N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) < ⊤ →
        (∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) = (k : ℝ≥0∞)) →
        (∀ q : ℚ≥0, ∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) ((q : ℝ≥0) : ℝ) ×ˢ A) = (k : ℝ≥0∞)) →
        ∃ k : ℕ, N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A) = (k : ℝ≥0∞) := by
      intro A hAm hfinA htA hratA
      rcases eq_or_lt_of_le (hτ_le_t ω₂) with hτt | hτt
      · rw [hτt]; exact htA
      · -- Pick a strictly decreasing sequence of rationals `q_n` in `(τ ω₂, t]` converging to `τ ω₂`
        have hex_q : ∀ n : ℕ, ∃ q : ℚ≥0,
            τ ω₂ ≤ (q : ℝ≥0) ∧ (q : ℝ≥0) ≤ min t (τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) := by
          intro n
          have hlt : (τ ω₂ : ℝ) < (min t (τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) : ℝ) := by
            have h1' : τ ω₂ < t := hτt
            have h2' : τ ω₂ < τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) :=
              lt_add_of_pos_right _ (by positivity)
            exact_mod_cast lt_min h1' h2'
          obtain ⟨q_rat, hq1, hq2⟩ := exists_rat_btwn hlt
          let q : ℚ≥0 := ⟨q_rat, by
            have : (0 : ℝ) ≤ (q_rat : ℝ) := le_trans (τ ω₂).coe_nonneg hq1.le
            exact_mod_cast this⟩
          exact ⟨q, by change (τ ω₂ : ℝ) ≤ (q_rat : ℝ); exact hq1.le,
            by change (q_rat : ℝ) ≤ _; exact hq2.le⟩
        choose qseq hq_ge hq_le using hex_q
        -- Make monotone decreasing via `r n = inf_{i ≤ n} qseq i`
        have hne_range : ∀ n : ℕ, (Finset.range (n + 1)).Nonempty :=
          fun n => ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        let rseq : ℕ → ℚ≥0 := fun n =>
          (Finset.range (n + 1)).inf' (hne_range n) qseq
        have hr_anti : Antitone rseq := fun i j hij =>
          Finset.inf'_mono qseq (Finset.range_mono (Nat.add_le_add_right hij 1)) (hne_range i)
        have hr_le_q : ∀ n, rseq n ≤ qseq n := fun n =>
          Finset.inf'_le qseq (Finset.mem_range.mpr (Nat.lt_succ_self n))
        have hr_ge : ∀ n : ℕ, τ ω₂ ≤ (rseq n : ℝ≥0) := fun n => by
          obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' (hne_range n) qseq
          change τ ω₂ ≤ (((Finset.range (n + 1)).inf' (hne_range n) qseq : ℚ≥0) : ℝ≥0)
          rw [hk]
          exact hq_ge k
        have hr_le_t : ∀ n, (rseq n : ℝ≥0) ≤ t := fun n =>
          (show (rseq n : ℝ≥0) ≤ (qseq n : ℝ≥0) by exact_mod_cast hr_le_q n).trans
            ((hq_le n).trans (min_le_left _ _))
        have hr_tend : Tendsto (fun n => (rseq n : ℝ≥0)) atTop (nhds (τ ω₂)) := by
          rw [← NNReal.tendsto_coe]
          have hhi : Tendsto (fun n : ℕ => (τ ω₂ : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds (τ ω₂ : ℝ)) := by
            simpa using (tendsto_const_nhds (x := (τ ω₂ : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi
            (fun n => by exact_mod_cast hr_ge n) (fun n => ?_)
          have h1' : (rseq n : ℝ≥0) ≤ (qseq n : ℝ≥0) := by exact_mod_cast hr_le_q n
          have h2' : (qseq n : ℝ≥0) ≤ τ ω₂ + (1 : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) :=
            (hq_le n).trans (min_le_right _ _)
          exact_mod_cast h1'.trans h2'
        have htend := hrc_N ω₂ A hAm (τ ω₂) (hτ_le_t ω₂) hfinA
          (fun n => (rseq n : ℝ≥0)) (fun i j hij => by dsimp only; exact_mod_cast hr_anti hij) hr_ge hr_le_t hr_tend
        choose kseq hkseq using fun n => hratA (rseq n)
        have hk_anti : Antitone kseq := fun i j hij => by
          have h1' : N₂.N ω₂ (Set.Ioc (0 : ℝ) ((rseq j : ℝ≥0) : ℝ) ×ˢ A) ≤
              N₂.N ω₂ (Set.Ioc (0 : ℝ) ((rseq i : ℝ≥0) : ℝ) ×ˢ A) :=
            measure_mono (Set.prod_mono
              (Set.Ioc_subset_Ioc_right (by exact_mod_cast hr_anti hij)) Set.Subset.rfl)
          rw [hkseq j, hkseq i] at h1'
          exact_mod_cast h1'
        -- An antitone `ℕ`-valued sequence is eventually constant
        have hmin_ex : ∃ n₀ : ℕ, ∀ n ≥ n₀, kseq n = kseq n₀ := by
          have hne : (Set.range kseq).Nonempty := ⟨kseq 0, 0, rfl⟩
          obtain ⟨n₀, hn₀⟩ := Nat.sInf_mem hne
          refine ⟨n₀, fun n hn => le_antisymm (hk_anti hn) ?_⟩
          rw [hn₀]; exact Nat.sInf_le ⟨n, rfl⟩
        obtain ⟨n₀, hn₀⟩ := hmin_ex
        refine ⟨kseq n₀, ?_⟩
        have hev : ∀ᶠ n in atTop, N₂.N ω₂ (Set.Ioc (0 : ℝ) ((rseq n : ℝ≥0) : ℝ) ×ˢ A) = (kseq n₀ : ℝ≥0∞) :=
          eventually_atTop.mpr ⟨n₀, fun n hn => by rw [hkseq n, hn₀ n hn]⟩
        exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
    obtain ⟨kpτ, hkpτ⟩ := hnat_at_τ B_pos hBpm hfin_tp ⟨kp, hkp⟩ (fun q => (hrat q).2.1)
    obtain ⟨knτ, hknτ⟩ := hnat_at_τ B_neg hBnm hfin_tn ⟨kn, hkn⟩ (fun q => (hrat q).2.2)
    have hsplit_τ : Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B =
        (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos) ∪ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg) := by
      rw [hB_union, Set.prod_union]
    have hdisj_τ : Disjoint (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos) (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg) :=
      Set.disjoint_left.mpr fun _ h1 h2 => Set.disjoint_left.mp hB_disj h1.2 h2.2
    have hsum1 : kpτ + knτ = 1 := by
      have h1' : cnt (τ ω₂) ω₂ =
          N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos) + N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg) := by
        dsimp only [cnt]; rw [hsplit_τ, measure_union hdisj_τ (measurableSet_Ioc.prod hBnm)]
      rw [hcnt_τ_eq1, hkpτ, hknτ] at h1'
      exact_mod_cast h1'.symm
    -- Integrability of `z.2` on `Ioc 0 (τ ω₂) ×ˢ B` via `hM`
    have hM_sub : N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ {x : ℝ | (M : ℝ) < |x|}) = 0 :=
      le_antisymm ((measure_mono (Set.prod_mono
        (Set.Ioc_subset_Ioc_right (by exact_mod_cast hτ_le_t ω₂)) Set.Subset.rfl)).trans (le_of_eq hM)) zero_le'
    have hint_B : ∀ (A : Set ℝ), A ⊆ B → MeasurableSet A →
        IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A) (N₂.N ω₂) := fun A hAB hAm => by
      have hfinA : N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A) < ⊤ :=
        lt_of_le_of_lt (measure_mono (Set.prod_mono Set.Subset.rfl hAB)) (by rw [show N₂.N ω₂ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B) = 1 from hcnt_τ_eq1]; exact ENNReal.one_lt_top)
      haveI : IsFiniteMeasure ((N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinA⟩
      refine Integrable.of_bound measurable_snd.aestronglyMeasurable (M : ℝ) ?_
      have hae_leM : ∀ᵐ z ∂((N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A)), |z.2| ≤ (M : ℝ) := by
        rw [ae_iff]
        have hsub' : {z : ℝ × ℝ | ¬ |z.2| ≤ (M : ℝ)} ∩ (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ A) ⊆
            Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ {x : ℝ | (M : ℝ) < |x|} := by
          intro z ⟨hz1, hz2⟩
          exact ⟨hz2.1, lt_of_not_ge hz1⟩
        rw [Measure.restrict_apply' (measurableSet_Ioc.prod hAm)]
        exact le_antisymm ((measure_mono hsub').trans (le_of_eq hM_sub)) zero_le'
      filter_upwards [hae_leM] with z hz
      simpa [Real.norm_eq_abs] using hz
    have hgt_r : r < |X_large (τ ω₂) ω₂| := by
      have hXl_split : X_large (τ ω₂) ω₂ =
          (∫ z in Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos, z.2 ∂(N₂.N ω₂)) +
          (∫ z in Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg, z.2 ∂(N₂.N ω₂)) := by
        change ∫ z in Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B, z.2 ∂(N₂.N ω₂) = _
        rw [hsplit_τ, setIntegral_union hdisj_τ (measurableSet_Ioc.prod hBnm)
          (hint_B B_pos hBp_sub hBpm) (hint_B B_neg hBn_sub hBnm)]
      have hcases : (kpτ = 1 ∧ knτ = 0) ∨ (kpτ = 0 ∧ knτ = 1) := by omega
      rcases hcases with ⟨hp1, hn0⟩ | ⟨hp0, hn1⟩
      · have hneg0 : ∫ z in Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg, z.2 ∂(N₂.N ω₂) = 0 := by
          have hres0 : (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg) = 0 :=
            Measure.restrict_eq_zero.mpr (by rw [hknτ, hn0]; simp)
          rw [hres0]; simp
        rw [hXl_split, hneg0, add_zero]
        let μp : Measure (ℝ × ℝ) := (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos)
        have hμp_univ : μp Set.univ = 1 := by
          dsimp only [μp]; rw [Measure.restrict_apply_univ, hkpτ, hp1]; simp
        haveI : IsFiniteMeasure μp := ⟨by rw [hμp_univ]; exact ENNReal.one_lt_top⟩
        have hpos_int : 0 < ∫ z, (z.2 - r) ∂μp := by
          rw [integral_pos_iff_support_of_nonneg_ae]
          · have hsupp : Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos ⊆ Function.support (fun z : ℝ × ℝ => z.2 - r) := by
              intro z hz; exact sub_ne_zero.mpr (ne_of_gt hz.2)
            have h1' : μp (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos) = 1 := by
              dsimp only [μp]; rw [Measure.restrict_apply (measurableSet_Ioc.prod hBpm),
                Set.inter_self, hkpτ, hp1]; simp
            exact lt_of_lt_of_le (by norm_num) (h1' ▸ measure_mono hsupp)
          · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hBpm)] with z hz
            exact sub_nonneg.mpr hz.2.le
          · exact (hint_B B_pos hBp_sub hBpm).sub (integrable_const r)
        have hsub_eq : ∫ z, (z.2 - r) ∂μp = (∫ z, z.2 ∂μp) - ∫ _z, r ∂μp :=
          integral_sub (hint_B B_pos hBp_sub hBpm) (integrable_const r)
        rw [hsub_eq, integral_const, Measure.real_def, hμp_univ, ENNReal.toReal_one, one_smul] at hpos_int
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      · have hpos0 : ∫ z in Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos, z.2 ∂(N₂.N ω₂) = 0 := by
          have hres0 : (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_pos) = 0 :=
            Measure.restrict_eq_zero.mpr (by rw [hkpτ, hp0]; simp)
          rw [hres0]; simp
        rw [hXl_split, hpos0, zero_add]
        let μn : Measure (ℝ × ℝ) := (N₂.N ω₂).restrict (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg)
        have hμn_univ : μn Set.univ = 1 := by
          dsimp only [μn]; rw [Measure.restrict_apply_univ, hknτ, hn1]; simp
        haveI : IsFiniteMeasure μn := ⟨by rw [hμn_univ]; exact ENNReal.one_lt_top⟩
        have hpos_int : 0 < ∫ z, (-z.2 - r) ∂μn := by
          rw [integral_pos_iff_support_of_nonneg_ae]
          · have hsupp : Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg ⊆ Function.support (fun z : ℝ × ℝ => -z.2 - r) := by
              intro z hz; change -z.2 - r ≠ 0; have hz2 : z.2 < -r := hz.2; linarith
            have h1' : μn (Set.Ioc (0 : ℝ) (τ ω₂ : ℝ) ×ˢ B_neg) = 1 := by
              dsimp only [μn]; rw [Measure.restrict_apply (measurableSet_Ioc.prod hBnm),
                Set.inter_self, hknτ, hn1]; simp
            exact lt_of_lt_of_le (by norm_num) (h1' ▸ measure_mono hsupp)
          · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hBnm)] with z hz
            change 0 ≤ -z.2 - r; have hz2 : z.2 < -r := hz.2; linarith
          · exact (hint_B B_neg hBn_sub hBnm).neg.sub (integrable_const r)
        have hsub_eq : ∫ z, (-z.2 - r) ∂μn = (∫ z, (-z.2) ∂μn) - ∫ _z, r ∂μn :=
          integral_sub (hint_B B_neg hBn_sub hBnm).neg (integrable_const r)
        rw [hsub_eq, integral_neg, integral_const, Measure.real_def, hμn_univ, ENNReal.toReal_one, one_smul] at hpos_int
        exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
    exact ⟨hτ_pos, hτ_le_t ω₂, hlt_Xl0, hgt_r⟩
  exact ⟨Ω₂, mΩ₂, P₂, hP₂, X_large, E_large1, τ, hXl_levy, hXl_meas, hXl_char,
    hE1_meas, hP_E1, hτ_meas, hτ_atomless, hnotE1_zero, hE1_jump⟩

private lemma ae_comp_of_map_eq
    {Ω_prod Ω : Type} [MeasurableSpace Ω_prod] [MeasurableSpace Ω]
    {P_prod : Measure Ω_prod} {P : Measure Ω} {π : Ω_prod → Ω}
    (hπ : Measurable π) (hmap : P_prod.map π = P)
    {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω_prod ∂P_prod, p (π ω_prod) := by
  rw [ae_iff] at hp ⊢
  obtain ⟨S, hsub, hSm, hS0⟩ := exists_measurable_superset_of_null hp
  have hsub' : {ω_prod | ¬ p (π ω_prod)} ⊆ π ⁻¹' S := fun ω_prod hω_prod => hsub hω_prod
  refine measure_mono_null hsub' ?_
  rw [← Measure.map_apply hπ hSm, hmap, hS0]

private lemma lift_levy_process
    {Ω_prod Ω : Type} [MeasurableSpace Ω_prod] [MeasurableSpace Ω]
    (P_prod : Measure Ω_prod) [IsProbabilityMeasure P_prod]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (π : Ω_prod → Ω) (hπ : Measurable π) (hmap : P_prod.map π = P)
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hX_meas : ∀ s : ℝ≥0, Measurable (X s)) :
    ProbabilityTheory.IsLevyProcess (fun s ω_prod => X s (π ω_prod)) P_prod ∧
    (∀ s : ℝ≥0, Measurable (fun ω_prod => X s (π ω_prod))) ∧
    (∀ s : ℝ≥0, P_prod.map (fun ω_prod => X s (π ω_prod)) = P.map (X s)) := by
  have hmeas' : ∀ s : ℝ≥0, Measurable (fun ω_prod => X s (π ω_prod)) := fun s => (hX_meas s).comp hπ
  have hmap' : ∀ s : ℝ≥0, P_prod.map (fun ω_prod => X s (π ω_prod)) = P.map (X s) := fun s => by
    rw [show (fun ω_prod => X s (π ω_prod)) = X s ∘ π from rfl, ← Measure.map_map (hX_meas s) hπ, hmap]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hmeas', hmap'⟩
  · funext ω_prod; exact congrFun hX.start_zero (π ω_prod)
  · intro n ts hts
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hpre : ∀ i : Fin n,
        ProbabilityTheory.increment (fun s ω_prod => X s (π ω_prod)) (ts i.castSucc) (ts i.succ) ⁻¹' sets i =
        π ⁻¹' (ProbabilityTheory.increment X (ts i.castSucc) (ts i.succ) ⁻¹' sets i) := fun _ => rfl
    have hmeas_inc : ∀ i ∈ S,
        MeasurableSet (ProbabilityTheory.increment X (ts i.castSucc) (ts i.succ) ⁻¹' sets i) :=
      fun i hi => ((hX_meas _).sub (hX_meas _)) (hsets i hi)
    have hinter : (⋂ i ∈ S, ProbabilityTheory.increment (fun s ω_prod => X s (π ω_prod))
          (ts i.castSucc) (ts i.succ) ⁻¹' sets i) =
        π ⁻¹' (⋂ i ∈ S, ProbabilityTheory.increment X (ts i.castSucc) (ts i.succ) ⁻¹' sets i) := by
      simp only [hpre, Set.preimage_iInter]
    rw [hinter, ← Measure.map_apply hπ (Finset.measurableSet_biInter S hmeas_inc), hmap]
    have hprod : ∏ i ∈ S, P_prod (ProbabilityTheory.increment (fun s ω_prod => X s (π ω_prod))
          (ts i.castSucc) (ts i.succ) ⁻¹' sets i) =
        ∏ i ∈ S, P (ProbabilityTheory.increment X (ts i.castSucc) (ts i.succ) ⁻¹' sets i) :=
      Finset.prod_congr rfl fun i hi => by
        rw [hpre i, ← Measure.map_apply hπ (hmeas_inc i hi), hmap]
    rw [hprod]
    exact (iIndepFun_iff_measure_inter_preimage_eq_mul.mp (hX.indep_increments n ts hts)) S hsets
  · intro s h
    have hm1 : Measurable (ProbabilityTheory.increment X s (s + h)) := (hX_meas (s + h)).sub (hX_meas s)
    have hm2 : Measurable (ProbabilityTheory.increment X 0 h) := (hX_meas h).sub (hX_meas 0)
    refine ⟨(hm1.comp hπ).aemeasurable, (hm2.comp hπ).aemeasurable, ?_⟩
    have h1 : P_prod.map (ProbabilityTheory.increment (fun u ω_prod => X u (π ω_prod)) s (s + h)) =
        P.map (ProbabilityTheory.increment X s (s + h)) := by
      change P_prod.map (ProbabilityTheory.increment X s (s + h) ∘ π) = _
      rw [← Measure.map_map hm1 hπ, hmap]
    have h2 : P_prod.map (ProbabilityTheory.increment (fun u ω_prod => X u (π ω_prod)) 0 h) =
        P.map (ProbabilityTheory.increment X 0 h) := by
      change P_prod.map (ProbabilityTheory.increment X 0 h ∘ π) = _
      rw [← Measure.map_map hm2 hπ, hmap]
    rw [h1, h2]
    exact (hX.stationary_increments s h).map_eq
  · exact ae_comp_of_map_eq hπ hmap hX.cadlag_ae

private lemma prod_three_indep_components
    {Ω₀ Ω₁ Ω₂ : Type} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X_gauss : ℝ≥0 → Ω₀ → ℝ) (hXg : ProbabilityTheory.IsLevyProcess X_gauss P₀)
    (hXg_meas : ∀ s : ℝ≥0, Measurable (X_gauss s))
    (X_small : ℝ≥0 → Ω₁ → ℝ) (hXs : ProbabilityTheory.IsLevyProcess X_small P₁)
    (hXs_meas : ∀ s : ℝ≥0, Measurable (X_small s))
    (X_large : ℝ≥0 → Ω₂ → ℝ) (hXl : ProbabilityTheory.IsLevyProcess X_large P₂)
    (hXl_meas : ∀ s : ℝ≥0, Measurable (X_large s)) :
    let P_prod : Measure (Ω₀ × (Ω₁ × Ω₂)) := P₀.prod (P₁.prod P₂)
    let Xg_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_gauss s ω.1
    let Xl_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_large s ω.2.2
    let Xs_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_small s ω.2.1
    ProbabilityTheory.IsLevyProcess Xg_lift P_prod ∧
    ProbabilityTheory.IsLevyProcess Xl_lift P_prod ∧
    ProbabilityTheory.IsLevyProcess Xs_lift P_prod ∧
    (∀ s : ℝ≥0, P_prod.map (Xg_lift s) = P₀.map (X_gauss s)) ∧
    (∀ s : ℝ≥0, P_prod.map (Xl_lift s) = P₂.map (X_large s)) ∧
    (∀ s : ℝ≥0, P_prod.map (Xs_lift s) = P₁.map (X_small s)) ∧
    Kyprianou.IndependentLevyItoComponents P_prod Xg_lift Xl_lift Xs_lift := by
  let P_prod : Measure (Ω₀ × (Ω₁ × Ω₂)) := P₀.prod (P₁.prod P₂)
  let Xg_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_gauss s ω.1
  let Xl_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_large s ω.2.2
  let Xs_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_small s ω.2.1
  have hmap0 : P_prod.map Prod.fst = P₀ := by
    dsimp only [P_prod]; rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap12 : P_prod.map Prod.snd = P₁.prod P₂ := by
    dsimp only [P_prod]; rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmap1 : P_prod.map (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) = P₁ := by
    rw [show (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd, hmap12, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hmap2 : P_prod.map (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) = P₂ := by
    rw [show (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd measurable_snd, hmap12, Measure.map_snd_prod,
      measure_univ, one_smul]
  obtain ⟨hXg', _, hXg_map⟩ := lift_levy_process P_prod P₀ Prod.fst measurable_fst hmap0 X_gauss hXg hXg_meas
  obtain ⟨hXl', _, hXl_map⟩ := lift_levy_process P_prod P₂ (fun ω => ω.2.2)
    (measurable_snd.comp measurable_snd) hmap2 X_large hXl hXl_meas
  obtain ⟨hXs', _, hXs_map⟩ := lift_levy_process P_prod P₁ (fun ω => ω.2.1)
    (measurable_fst.comp measurable_snd) hmap1 X_small hXs hXs_meas
  have hind : Kyprianou.IndependentLevyItoComponents P_prod Xg_lift Xl_lift Xs_lift := by
    unfold Kyprianou.IndependentLevyItoComponents
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    let fg : Ω₀ → (ℝ≥0 → ℝ) := fun ω₀ t => X_gauss t ω₀
    let fl : Ω₂ → (ℝ≥0 → ℝ) := fun ω₂ t => X_large t ω₂
    let fs : Ω₁ → (ℝ≥0 → ℝ) := fun ω₁ t => X_small t ω₁
    have hfg_m : Measurable fg := measurable_pi_lambda _ hXg_meas
    have hfl_m : Measurable fl := measurable_pi_lambda _ hXl_meas
    have hfs_m : Measurable fs := measurable_pi_lambda _ hXs_meas
    let A₀ : Set Ω₀ := if (0 : Fin 3) ∈ S then fg ⁻¹' sets 0 else Set.univ
    let A₂ : Set Ω₂ := if (1 : Fin 3) ∈ S then fl ⁻¹' sets 1 else Set.univ
    let A₁ : Set Ω₁ := if (2 : Fin 3) ∈ S then fs ⁻¹' sets 2 else Set.univ
    have hA₀m : MeasurableSet A₀ := by
      dsimp only [A₀]; split_ifs with h
      · exact hfg_m (hsets 0 h)
      · exact MeasurableSet.univ
    have hA₂m : MeasurableSet A₂ := by
      dsimp only [A₂]; split_ifs with h
      · exact hfl_m (hsets 1 h)
      · exact MeasurableSet.univ
    have hA₁m : MeasurableSet A₁ := by
      dsimp only [A₁]; split_ifs with h
      · exact hfs_m (hsets 2 h)
      · exact MeasurableSet.univ
    let F : Fin 3 → Ω₀ × (Ω₁ × Ω₂) → (ℝ≥0 → ℝ) :=
      fun i ω t => if i = 0 then Xg_lift t ω else if i = 1 then Xl_lift t ω else Xs_lift t ω
    have hinter : (⋂ i ∈ S, F i ⁻¹' sets i) = A₀ ×ˢ (A₁ ×ˢ A₂) := by
      ext ⟨ω₀, ω₁, ω₂⟩
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_prod, A₀, A₁, A₂]
      constructor
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · split_ifs with h0
          · exact h 0 h0
          · trivial
        · split_ifs with h2
          · exact h 2 h2
          · trivial
        · split_ifs with h1
          · exact h 1 h1
          · trivial
      · rintro ⟨h0, h2, h1⟩ i hi
        fin_cases i
        · have hi0 : (0 : Fin 3) ∈ S := hi
          rw [if_pos hi0] at h0; exact h0
        · have hi1 : (1 : Fin 3) ∈ S := hi
          rw [if_pos hi1] at h1; exact h1
        · have hi2 : (2 : Fin 3) ∈ S := hi
          rw [if_pos hi2] at h2; exact h2
    have hmeas_lhs : P_prod (⋂ i ∈ S, F i ⁻¹' sets i) = P₀ A₀ * (P₁ A₁ * P₂ A₂) := by
      rw [hinter]
      dsimp only [P_prod]
      rw [Measure.prod_prod, Measure.prod_prod]
    let m : Fin 3 → ℝ≥0∞ := fun i => if i = 0 then P₀ A₀ else if i = 1 then P₂ A₂ else P₁ A₁
    have hterm : ∀ i ∈ S, P_prod (F i ⁻¹' sets i) = m i := by
      intro i hi
      fin_cases i
      · change P_prod (F 0 ⁻¹' sets 0) = m 0
        have hi0 : (0 : Fin 3) ∈ S := hi
        have hpre : F 0 ⁻¹' sets 0 = Prod.fst ⁻¹' A₀ := by
          ext ω; simp [F, fg, Xg_lift, A₀, hi0]
        rw [hpre, ← Measure.map_apply measurable_fst hA₀m, hmap0]; simp [m]
      · change P_prod (F 1 ⁻¹' sets 1) = m 1
        have hi1 : (1 : Fin 3) ∈ S := hi
        have hpre : F 1 ⁻¹' sets 1 = (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) ⁻¹' A₂ := by
          ext ω; simp [F, fl, Xl_lift, A₂, hi1]
        have hπ₂ : Measurable (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) := measurable_snd.comp measurable_snd
        rw [hpre, ← Measure.map_apply hπ₂ hA₂m, hmap2]; simp [m]
      · change P_prod (F 2 ⁻¹' sets 2) = m 2
        have hi2 : (2 : Fin 3) ∈ S := hi
        have hpre : F 2 ⁻¹' sets 2 = (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) ⁻¹' A₁ := by
          ext ω; simp [F, fs, Xs_lift, A₁, hi2]
        have hπ₁ : Measurable (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) := measurable_fst.comp measurable_snd
        rw [hpre, ← Measure.map_apply hπ₁ hA₁m, hmap1]; simp [m]
    have hnot : ∀ i : Fin 3, i ∉ S → m i = 1 := by
      intro i hi
      fin_cases i
      · have hi0 : (0 : Fin 3) ∉ S := hi; simp [m, A₀, hi0, measure_univ]
      · have hi1 : (1 : Fin 3) ∉ S := hi; simp [m, A₂, hi1, measure_univ]
      · have hi2 : (2 : Fin 3) ∉ S := hi; simp [m, A₁, hi2, measure_univ]
    have hprod_eq : ∏ i ∈ S, P_prod (F i ⁻¹' sets i) = ∏ i : Fin 3, m i := by
      rw [Finset.prod_congr rfl hterm]
      exact Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => hnot i hi)
    rw [hmeas_lhs, hprod_eq, Fin.prod_univ_three]
    dsimp only [m]
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
    ring
  exact ⟨hXg', hXl', hXs', hXg_map, hXl_map, hXs_map, hind⟩

private lemma ae_continuousAt_independent_time
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X_small : ℝ≥0 → Ω₁ → ℝ)
    (hXs_cadlag : ∀ᵐ ω₁ ∂P₁, ProbabilityTheory.IsCadlag (fun s : ℝ≥0 => X_small s ω₁))
    (hXs_meas : ∀ s : ℝ≥0, Measurable (X_small s))
    (hXs_cnt : ∀ᵐ ω₁ ∂P₁, {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => X_small u ω₁) s}.Countable)
    (E_large1 : Set Ω₂) (hE1_meas : MeasurableSet E_large1)
    (τ : Ω₂ → ℝ≥0) (hτ_meas : Measurable τ)
    (hτ_atomless : ∀ x : ℝ≥0, P₂ {ω₂ | ω₂ ∈ E_large1 ∧ τ ω₂ = x} = 0)
    (hτ_pos : ∀ᵐ ω₂ ∂P₂, ω₂ ∈ E_large1 → 0 < τ ω₂) :
    ∀ᵐ p ∂(P₁.prod P₂), p.2 ∈ E_large1 → ContinuousAt (fun s : ℝ≥0 => X_small s p.1) (τ p.2) := by
  let Bad : Set (Ω₁ × Ω₂) :=
    {p | p.2 ∈ E_large1 ∧ 0 < τ p.2 ∧
      ∃ k : ℕ, ∀ m : ℕ, ∃ (q₁ q₂ : ℚ≥0),
        (τ p.2 : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) < (q₁ : ℝ) ∧ (q₁ : ℝ) < (τ p.2 : ℝ) ∧
        (τ p.2 : ℝ) ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) < (τ p.2 : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) ∧
        1 / ((k + 1 : ℕ) : ℝ) < |X_small (q₂ : ℝ≥0) p.1 - X_small (q₁ : ℝ≥0) p.1|}
  have hBad_meas : MeasurableSet Bad := by
    have hrew : Bad =
        (Prod.snd ⁻¹' E_large1) ∩
        (Prod.snd ⁻¹' (τ ⁻¹' Set.Ioi 0)) ∩
        ⋃ (k : ℕ), ⋂ (m : ℕ), ⋃ (q₁ : ℚ≥0), ⋃ (q₂ : ℚ≥0),
          ({p : Ω₁ × Ω₂ | (τ p.2 : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) < (q₁ : ℝ)} ∩
           {p : Ω₁ × Ω₂ | (q₁ : ℝ) < (τ p.2 : ℝ)} ∩
           {p : Ω₁ × Ω₂ | (τ p.2 : ℝ) ≤ (q₂ : ℝ)} ∩
           {p : Ω₁ × Ω₂ | (q₂ : ℝ) < (τ p.2 : ℝ) + 1 / ((m + 1 : ℕ) : ℝ)} ∩
           {p : Ω₁ × Ω₂ | 1 / ((k + 1 : ℕ) : ℝ) <
             |X_small (q₂ : ℝ≥0) p.1 - X_small (q₁ : ℝ≥0) p.1|}) := by
      ext p
      simp only [Bad, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
        Set.mem_iUnion, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2, k, hk⟩
        refine ⟨⟨h1, h2⟩, k, fun m => ?_⟩
        obtain ⟨q₁, q₂, a1, a2, a3, a4, a5⟩ := hk m
        exact ⟨q₁, q₂, ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩⟩
      · rintro ⟨⟨h1, h2⟩, k, hk⟩
        refine ⟨h1, h2, k, fun m => ?_⟩
        obtain ⟨q₁, q₂, ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩⟩ := hk m
        exact ⟨q₁, q₂, a1, a2, a3, a4, a5⟩
    rw [hrew]
    have hτR : Measurable (fun p : Ω₁ × Ω₂ => (τ p.2 : ℝ)) :=
      NNReal.continuous_coe.measurable.comp (hτ_meas.comp measurable_snd)
    refine ((measurable_snd hE1_meas).inter (measurable_snd (hτ_meas measurableSet_Ioi))).inter ?_
    refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun m =>
      MeasurableSet.iUnion fun q₁ => MeasurableSet.iUnion fun q₂ => ?_
    refine ((((measurableSet_lt (hτR.sub measurable_const) measurable_const).inter
      (measurableSet_lt measurable_const hτR)).inter
      (measurableSet_le hτR measurable_const)).inter
      (measurableSet_lt measurable_const (hτR.add measurable_const))).inter ?_
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        (((hXs_meas (q₂ : ℝ≥0)).comp measurable_fst).sub ((hXs_meas (q₁ : ℝ≥0)).comp measurable_fst)))
  -- For any `p = (ω₁, ω₂) ∈ Bad`, `X_small · ω₁` is NOT continuous at `τ ω₂`
  have hBad_discont : ∀ ω₁ ω₂, (ω₁, ω₂) ∈ Bad →
      ω₂ ∈ E_large1 ∧ ¬ ContinuousAt (fun s : ℝ≥0 => X_small s ω₁) (τ ω₂) := by
    intro ω₁ ω₂ ⟨hE, _, k, hkm⟩
    refine ⟨hE, fun hcont => ?_⟩
    have hε : (0 : ℝ) < 1 / (2 * ((k + 1 : ℕ) : ℝ)) := by positivity
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont _ hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨q₁, q₂, hq1_lo, hq1_hi, hq2_lo, hq2_hi, hjump⟩ := hkm m
    push_cast at hq1_lo hq2_hi
    have hq1_eq : ((q₁ : ℝ≥0) : ℝ) = (q₁ : ℝ) := by norm_cast
    have hq2_eq : ((q₂ : ℝ≥0) : ℝ) = (q₂ : ℝ) := by norm_cast
    have hd1 : dist (q₁ : ℝ≥0) (τ ω₂) < δ := by
      rw [NNReal.dist_eq, hq1_eq, abs_lt]
      constructor <;> linarith
    have hd2 : dist (q₂ : ℝ≥0) (τ ω₂) < δ := by
      rw [NNReal.dist_eq, hq2_eq, abs_lt]
      constructor <;> linarith
    have hf1 : |X_small (q₁ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| < 1 / (2 * ((k + 1 : ℕ) : ℝ)) := by
      simpa [Real.dist_eq] using hball hd1
    have hf2 : |X_small (q₂ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| < 1 / (2 * ((k + 1 : ℕ) : ℝ)) := by
      simpa [Real.dist_eq] using hball hd2
    have htri : |X_small (q₂ : ℝ≥0) ω₁ - X_small (q₁ : ℝ≥0) ω₁| ≤
        |X_small (q₂ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| +
        |X_small (q₁ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| := by
      rw [abs_sub_comm (X_small (q₁ : ℝ≥0) ω₁)]
      exact abs_sub_le _ _ _
    have hhalf : 1 / (2 * ((k + 1 : ℕ) : ℝ)) + 1 / (2 * ((k + 1 : ℕ) : ℝ)) =
        1 / ((k + 1 : ℕ) : ℝ) := by ring
    linarith
  -- Compute `(P₁.prod P₂) Bad = 0` by Tonelli
  have hBad_zero : (P₁.prod P₂) Bad = 0 := by
    rw [Measure.prod_apply hBad_meas]
    have hae0 : ∀ᵐ ω₁ ∂P₁, P₂ (Prod.mk ω₁ ⁻¹' Bad) = 0 := by
      filter_upwards [hXs_cnt] with ω₁ hcnt
      have hsub : Prod.mk ω₁ ⁻¹' Bad ⊆
          ⋃ x ∈ {s : ℝ≥0 | ¬ ContinuousAt (fun u : ℝ≥0 => X_small u ω₁) s},
            {ω₂ | ω₂ ∈ E_large1 ∧ τ ω₂ = x} := by
        intro ω₂ hω₂
        obtain ⟨hE, hdisc⟩ := hBad_discont ω₁ ω₂ hω₂
        exact Set.mem_biUnion hdisc ⟨hE, rfl⟩
      exact measure_mono_null hsub ((measure_biUnion_null_iff hcnt).mpr fun x _ => hτ_atomless x)
    rw [lintegral_congr_ae hae0, lintegral_zero]
  -- Conversely, for càdlàg `X_small · ω₁` and `0 < τ ω₂`, discontinuity implies `∈ Bad`
  have hnotBad : ∀ᵐ p ∂(P₁.prod P₂), p ∉ Bad := by
    rw [ae_iff]; simpa using hBad_zero
  have hcadlag_prod : ∀ᵐ p ∂(P₁.prod P₂), ProbabilityTheory.IsCadlag (fun s : ℝ≥0 => X_small s p.1) :=
    ae_comp_of_map_eq measurable_fst
      (by rw [Measure.map_fst_prod, measure_univ, one_smul]) hXs_cadlag
  have hpos_prod : ∀ᵐ p ∂(P₁.prod P₂), p.2 ∈ E_large1 → 0 < τ p.2 :=
    ae_comp_of_map_eq measurable_snd
      (by rw [Measure.map_snd_prod, measure_univ, one_smul]) hτ_pos
  filter_upwards [hnotBad, hcadlag_prod, hpos_prod] with ⟨ω₁, ω₂⟩ hnb hcad hpos hE
  by_contra hdisc
  apply hnb
  have hτ0 : 0 < τ ω₂ := hpos hE
  refine ⟨hE, hτ0, ?_⟩
  have hrc : Tendsto (fun u : ℝ≥0 => X_small u ω₁) (nhdsWithin (τ ω₂) (Set.Ici (τ ω₂)))
      (nhds (X_small (τ ω₂) ω₁)) := (hcad (τ ω₂)).1
  obtain ⟨l, hll⟩ := (hcad (τ ω₂)).2
  have hne : X_small (τ ω₂) ω₁ ≠ l := by
    intro heq
    apply hdisc
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have h1 := (Metric.tendsto_nhds.mp hrc ε hε)
    have h2 := (Metric.tendsto_nhds.mp (heq ▸ hll) ε hε)
    rw [eventually_nhdsWithin_iff] at h1 h2
    filter_upwards [h1, h2] with u hu1 hu2
    rcases lt_or_ge u (τ ω₂) with hlt | hge
    · exact hu2 hlt
    · exact hu1 hge
  have hgap : 0 < |X_small (τ ω₂) ω₁ - l| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < |X_small (τ ω₂) ω₁ - l| / 2 by positivity)
  refine ⟨k, fun m => ?_⟩
  let ε : ℝ := (|X_small (τ ω₂) ω₁ - l| - 1 / ((k + 1 : ℕ) : ℝ)) / 2
  have hε : 0 < ε := by dsimp only [ε]; push_cast; linarith
  have h1 := eventually_nhdsWithin_iff.mp (Metric.tendsto_nhds.mp hll ε hε)
  have h2 := eventually_nhdsWithin_iff.mp (Metric.tendsto_nhds.mp hrc ε hε)
  rw [Metric.eventually_nhds_iff] at h1 h2
  obtain ⟨δ₁, hδ₁, h1'⟩ := h1
  obtain ⟨δ₂, hδ₂, h2'⟩ := h2
  have hτR_pos : (0 : ℝ) < (τ ω₂ : ℝ) := by exact_mod_cast hτ0
  have hm_pos : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
  let lo : ℝ := max 0 ((τ ω₂ : ℝ) - min δ₁ (1 / ((m + 1 : ℕ) : ℝ)))
  have hlo_lt : lo < (τ ω₂ : ℝ) := by
    dsimp only [lo]
    exact max_lt hτR_pos (sub_lt_self _ (lt_min hδ₁ hm_pos))
  obtain ⟨q₁_rat, hq1_lo, hq1_hi⟩ := exists_rat_btwn hlo_lt
  let q₁ : ℚ≥0 := ⟨q₁_rat, by
    have : (0 : ℝ) ≤ (q₁_rat : ℝ) := le_trans (le_max_left _ _) hq1_lo.le
    exact_mod_cast this⟩
  let hi : ℝ := (τ ω₂ : ℝ) + min δ₂ (1 / ((m + 1 : ℕ) : ℝ))
  have hhi_gt : (τ ω₂ : ℝ) < hi := lt_add_of_pos_right _ (lt_min hδ₂ hm_pos)
  obtain ⟨q₂_rat, hq2_lo, hq2_hi⟩ := exists_rat_btwn hhi_gt
  let q₂ : ℚ≥0 := ⟨q₂_rat, by
    have : (0 : ℝ) ≤ (q₂_rat : ℝ) := le_trans (τ ω₂).coe_nonneg hq2_lo.le
    exact_mod_cast this⟩
  have hq1R : (q₁ : ℝ) = (q₁_rat : ℝ) := rfl
  have hq2R : (q₂ : ℝ) = (q₂_rat : ℝ) := rfl
  have hq1_coe : ((q₁ : ℝ≥0) : ℝ) = (q₁ : ℝ) := by norm_cast
  have hq2_coe : ((q₂ : ℝ≥0) : ℝ) = (q₂ : ℝ) := by norm_cast
  have hq1_gt_m : (τ ω₂ : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) < (q₁ : ℝ) := by
    rw [hq1R]
    have h1'' : (τ ω₂ : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) ≤ (τ ω₂ : ℝ) - min δ₁ (1 / ((m + 1 : ℕ) : ℝ)) :=
      sub_le_sub_left (min_le_right _ _) _
    exact lt_of_le_of_lt (h1''.trans (le_max_right _ _)) hq1_lo
  have hq1_lt : (q₁ : ℝ) < (τ ω₂ : ℝ) := by rw [hq1R]; exact hq1_hi
  have hq2_ge : (τ ω₂ : ℝ) ≤ (q₂ : ℝ) := by rw [hq2R]; exact hq2_lo.le
  have hq2_lt_m : (q₂ : ℝ) < (τ ω₂ : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) := by
    rw [hq2R]
    exact lt_of_lt_of_le hq2_hi (add_le_add le_rfl (min_le_right _ _))
  have hd1 : dist (q₁ : ℝ≥0) (τ ω₂) < δ₁ := by
    rw [NNReal.dist_eq, hq1_coe, abs_lt]
    have h1'' : (τ ω₂ : ℝ) - δ₁ ≤ lo :=
      (sub_le_sub_left (min_le_left _ _) _).trans (le_max_right _ _)
    have hq1_d : (τ ω₂ : ℝ) - δ₁ < (q₁ : ℝ) := by rw [hq1R]; exact lt_of_le_of_lt h1'' hq1_lo
    constructor <;> linarith
  have hd2 : dist (q₂ : ℝ≥0) (τ ω₂) < δ₂ := by
    rw [NNReal.dist_eq, hq2_coe, abs_lt]
    have hq2_d : (q₂ : ℝ) < (τ ω₂ : ℝ) + δ₂ := by
      rw [hq2R]; exact lt_of_lt_of_le hq2_hi (add_le_add le_rfl (min_le_left _ _))
    constructor <;> linarith
  have hf1 : |X_small (q₁ : ℝ≥0) ω₁ - l| < ε := by
    simpa [Real.dist_eq] using h1' hd1 (by exact_mod_cast hq1_lt)
  have hf2 : |X_small (q₂ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| < ε := by
    simpa [Real.dist_eq] using h2' hd2 (by exact_mod_cast hq2_ge)
  have htri : |X_small (τ ω₂) ω₁ - l| ≤
      |X_small (q₂ : ℝ≥0) ω₁ - X_small (τ ω₂) ω₁| +
      |X_small (q₂ : ℝ≥0) ω₁ - X_small (q₁ : ℝ≥0) ω₁| +
      |X_small (q₁ : ℝ≥0) ω₁ - l| := by
    have hstep1 := abs_sub_le (X_small (τ ω₂) ω₁) (X_small (q₂ : ℝ≥0) ω₁) l
    have hstep2 := abs_sub_le (X_small (q₂ : ℝ≥0) ω₁) (X_small (q₁ : ℝ≥0) ω₁) l
    rw [abs_sub_comm (X_small (τ ω₂) ω₁) (X_small (q₂ : ℝ≥0) ω₁)] at hstep1
    linarith
  exact ⟨q₁, q₂, hq1_gt_m, hq1_lt, hq2_ge, hq2_lt_m, by dsimp only [ε] at hf1 hf2; linarith⟩

private lemma part1_jump_prob
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (t : ℝ≥0) (threshold : ℝ) (hthresh : 0 < threshold) :
    P (jumpEvent X t threshold) =
      ENNReal.ofReal (1 - Real.exp (-(t : ℝ) * (ν {x : ℝ | threshold < |x|}).toReal)) := by
  by_cases ht0 : t = 0
  · subst ht0
    have hempty : jumpEvent X 0 threshold = ∅ := by
      ext ω; simp only [jumpEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨s, hs0, hsle, _⟩
      exact not_lt_of_ge hsle hs0
    rw [hempty, measure_empty]
    simp
  have ht : 0 < t := pos_iff_ne_zero.mpr ht0
  -- Define the drift adjustment sets `A₁ = {1 ≤ |x| ≤ threshold}` and `A₂ = {threshold < |x| < 1}`
  let B_small : Set ℝ := {x : ℝ | |x| ≤ threshold}
  let B_large : Set ℝ := {x : ℝ | threshold < |x|}
  let A₁ : Set ℝ := {x : ℝ | 1 ≤ |x| ∧ |x| ≤ threshold}
  let A₂ : Set ℝ := {x : ℝ | threshold < |x| ∧ |x| < 1}
  have hBsm : MeasurableSet B_small := continuous_abs.measurable measurableSet_Iic
  have hBlm : MeasurableSet B_large := continuous_abs.measurable measurableSet_Ioi
  have hA₁m : MeasurableSet A₁ :=
    (continuous_abs.measurable measurableSet_Ici).inter hBsm
  have hA₂m : MeasurableSet A₂ :=
    hBlm.inter (continuous_abs.measurable measurableSet_Iio)
  have hν_ge1_fin : ν {x : ℝ | 1 ≤ |x|} < ⊤ :=
    lt_of_le_of_lt (measure_mono fun x (hx : 1 ≤ |x|) => show (1 / 2 : ℝ) < |x| by linarith)
      (levyMeasure_abs_gt_lt_top hν (by norm_num : (0 : ℝ) < 1 / 2))
  have hν_Bl_fin : ν B_large < ⊤ := levyMeasure_abs_gt_lt_top hν hthresh
  have hν_A₁_fin : ν A₁ < ⊤ :=
    lt_of_le_of_lt (measure_mono fun _ hx => hx.1) hν_ge1_fin
  have hν_A₂_fin : ν A₂ < ⊤ :=
    lt_of_le_of_lt (measure_mono fun _ hx => hx.1) hν_Bl_fin
  have hint_A₁ : IntegrableOn (fun x : ℝ => x) A₁ ν := by
    haveI : IsFiniteMeasure (ν.restrict A₁) := ⟨by rw [Measure.restrict_apply_univ]; exact hν_A₁_fin⟩
    refine (integrable_const threshold).mono' measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA₁m] with x hx
    simpa [Real.norm_eq_abs] using hx.2
  have hint_A₂ : IntegrableOn (fun x : ℝ => x) A₂ ν := by
    haveI : IsFiniteMeasure (ν.restrict A₂) := ⟨by rw [Measure.restrict_apply_univ]; exact hν_A₂_fin⟩
    refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA₂m] with x hx
    simpa [Real.norm_eq_abs] using hx.2.le
  let c_drift : ℝ := -a + (∫ x in A₁, x ∂ν) - (∫ x in A₂, x ∂ν)
  -- Construct the three independent Lévy-Itô components
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, X_gauss, hXg_levy, hXg_meas, hXg_cont, hXg_char⟩ :=
    brownian_levy_component σ c_drift
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, X_small, hXs_levy, hXs_meas, hXs_cnt, hXs_jump_le, hXs_char⟩ :=
    smallJump_levy_component ν hν threshold hthresh t ht
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, X_large, E_large1, τ, hXl_levy, hXl_meas, hXl_char,
      hE1_meas, hP_E1, hτ_meas, hτ_atomless, hnotE1_zero, hE1_jump⟩ :=
    largeJump_levy_component ν hν threshold hthresh t ht
  letI : MeasurableSpace Ω₀ := mΩ₀
  letI : IsProbabilityMeasure P₀ := hP₀
  letI : MeasurableSpace Ω₁ := mΩ₁
  letI : IsProbabilityMeasure P₁ := hP₁
  letI : MeasurableSpace Ω₂ := mΩ₂
  letI : IsProbabilityMeasure P₂ := hP₂
  -- Combine on `Ω_prod = Ω₀ × (Ω₁ × Ω₂)` with `P_prod = P₀.prod (P₁.prod P₂)`
  let P_prod : Measure (Ω₀ × (Ω₁ × Ω₂)) := P₀.prod (P₁.prod P₂)
  let Xg_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_gauss s ω.1
  let Xl_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_large s ω.2.2
  let Xs_lift : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => X_small s ω.2.1
  obtain ⟨hXg', hXl', hXs', hXg_map, hXl_map, hXs_map, hind⟩ :=
    prod_three_indep_components P₀ P₁ P₂ X_gauss hXg_levy hXg_meas
      X_small hXs_levy hXs_meas X_large hXl_levy hXl_meas
  let X_prod : ℝ≥0 → Ω₀ × (Ω₁ × Ω₂) → ℝ := fun s ω => Xg_lift s ω + Xl_lift s ω + Xs_lift s ω
  obtain ⟨hX_prod_levy, hX_prod_char_prod⟩ :=
    Kyprianou.sumOfIndependentLevyProcesses P_prod Xg_lift Xl_lift Xs_lift hXg' hXl' hXs' hind
  -- Verify `charFun (P_prod.map (X_prod s)) ξ = charFun (P.map (X s)) ξ`
  have hX_prod_marginals : ∀ s : ℝ≥0, P.map (X s) = P_prod.map (X_prod s) := by
    intro s
    have hX_meas : AEMeasurable (X s) P := levyProcess_aemeasurable hX s
    have hX_prod_meas : Measurable (X_prod s) :=
      (((hXg_meas s).comp measurable_fst).add ((hXl_meas s).comp (measurable_snd.comp measurable_snd))).add
        ((hXs_meas s).comp (measurable_fst.comp measurable_snd))
    haveI : IsProbabilityMeasure (P.map (X s)) := Measure.isProbabilityMeasure_map hX_meas
    haveI : IsProbabilityMeasure (P_prod.map (X_prod s)) := Measure.isProbabilityMeasure_map hX_prod_meas.aemeasurable
    apply Measure.ext_of_charFun
    funext ξ
    rw [hchar s ξ, hX_prod_char_prod s ξ, hXg_map s, hXl_map s, hXs_map s,
      hXg_char s ξ, hXl_char s ξ, hXs_char s ξ, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [← mul_add, ← mul_add]
    congr 1
    -- Match the Lévy-Khintchine exponents
    let g : ℝ → ℂ := ProbabilityTheory.levyCompensatedIntegrand ξ
    have hg_meas : Measurable g := by
      dsimp only [g, ProbabilityTheory.levyCompensatedIntegrand]
      have h1 : Measurable (fun x : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1) :=
        (Complex.continuous_exp.measurable.comp
          (((Complex.continuous_ofReal.measurable.mul measurable_const).mul measurable_const))).sub
          measurable_const
      have h2 : Measurable (fun x : ℝ => (x : ℂ) * (ξ : ℂ) * Complex.I * if |x| < 1 then (1 : ℂ) else 0) :=
        ((Complex.continuous_ofReal.measurable.mul measurable_const).mul measurable_const).mul
          (Measurable.ite (continuous_abs.measurable measurableSet_Iio) measurable_const measurable_const)
      exact h1.sub h2
    -- Integrability of `g` on `ℝ` w.r.t. `ν`
    have hg_int : Integrable g ν := by
      have hpt : ∀ x : ℝ, ‖g x‖ ≤ max 2 (ξ ^ 2 / 2) * min 1 (x ^ 2) := fun x => by
        dsimp only [g, ProbabilityTheory.levyCompensatedIntegrand]
        by_cases hx1 : |x| < 1
        · rw [if_pos hx1, mul_one]
          have hq : ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1 - (x : ℂ) * (ξ : ℂ) * Complex.I‖ ≤
              (ξ * x) ^ 2 / 2 := by
            have h1 := norm_exp_I_mul_sub_one_sub_le (x * ξ)
            have heq1 : ((x * ξ : ℝ) : ℂ) * Complex.I = (x : ℂ) * (ξ : ℂ) * Complex.I := by
              push_cast; ring
            have heq2 : (x * ξ) ^ 2 / 2 = (ξ * x) ^ 2 / 2 := by ring
            simpa [heq1, heq2] using h1
          have hmin : min 1 (x ^ 2) = x ^ 2 := by
            rw [min_eq_right]; nlinarith [abs_lt.mp hx1]
          rw [hmin]
          calc ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1 - (x : ℂ) * (ξ : ℂ) * Complex.I‖
              ≤ (ξ * x) ^ 2 / 2 := hq
            _ = (ξ ^ 2 / 2) * x ^ 2 := by ring
            _ ≤ max 2 (ξ ^ 2 / 2) * x ^ 2 :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x)
        · rw [if_neg hx1, mul_zero, sub_zero]
          have hle2 : ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1‖ ≤ 2 := by
            calc ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1‖
                ≤ ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 1 + 1 := by
                  have : (x : ℂ) * (ξ : ℂ) * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by
                    push_cast; ring
                  rw [this, Complex.norm_exp_ofReal_mul_I, norm_one]
              _ = 2 := by norm_num
          have hxge : 1 ≤ |x| := not_lt.mp hx1
          have hmin : min 1 (x ^ 2) = 1 := by
            rw [min_eq_left]
            have : (1 : ℝ) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) hxge 2
            simpa [sq_abs] using this
          rw [hmin]
          exact hle2.trans (by linarith [le_max_left (2 : ℝ) (ξ ^ 2 / 2)])
      have hmin_int : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
        refine ⟨(measurable_const.min (measurable_id.pow_const 2)).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal]
        · exact hν.2
        · exact ae_of_all _ fun x => le_min (by norm_num) (sq_nonneg x)
      exact (hmin_int.const_mul (max 2 (ξ ^ 2 / 2))).mono' hg_meas.aestronglyMeasurable
        (ae_of_all _ hpt)
    -- Relate small-jump integral to `∫ x in B_small, g x ∂ν`
    have hsmall_rel :
        (∫ x in B_small,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 -
            Complex.I * (((ξ * x : ℝ) : ℂ))) ∂ν) =
        (∫ x in B_small, g x ∂ν) - Complex.I * (ξ : ℂ) * ((∫ x in A₁, x ∂ν : ℝ) : ℂ) := by
      have hpt : ∀ x ∈ B_small,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 -
            Complex.I * (((ξ * x : ℝ) : ℂ))) =
          g x - A₁.indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ)) x := by
        intro x hx
        dsimp only [g, ProbabilityTheory.levyCompensatedIntegrand]
        have hexp : Complex.I * (((ξ * x : ℝ) : ℂ)) = (x : ℂ) * (ξ : ℂ) * Complex.I := by
          push_cast; ring
        rw [hexp]
        by_cases h1 : |x| < 1
        · have hxA₁ : x ∉ A₁ := fun h => not_le_of_gt h1 h.1
          rw [if_pos h1, Set.indicator_of_notMem hxA₁]; ring
        · have hxA₁ : x ∈ A₁ := ⟨not_lt.mp h1, hx⟩
          rw [if_neg h1, Set.indicator_of_mem hxA₁]; push_cast; ring
      rw [setIntegral_congr_fun hBsm hpt]
      have hind_int : IntegrableOn (A₁.indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ))) B_small ν := by
        have hsub : A₁ ⊆ B_small := fun _ hx => hx.2
        rw [IntegrableOn, integrable_indicator_iff hA₁m, IntegrableOn, Measure.restrict_restrict hA₁m,
          Set.inter_eq_left.mpr hsub]
        exact (Complex.ofRealCLM.integrable_comp hint_A₁).const_mul (Complex.I * (ξ : ℂ))
      rw [integral_sub hg_int.integrableOn hind_int]
      congr 1
      have hsub : A₁ ⊆ B_small := fun _ hx => hx.2
      rw [setIntegral_indicator hA₁m, Set.inter_eq_right.mpr hsub, integral_const_mul]
      congr 1
      exact Complex.ofRealCLM.integral_comp_comm hint_A₁
    -- Relate large-jump integral to `∫ x in B_large, g x ∂ν`
    have hlarge_rel :
        (∫ x in B_large,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) =
        (∫ x in B_large, g x ∂ν) + Complex.I * (ξ : ℂ) * ((∫ x in A₂, x ∂ν : ℝ) : ℂ) := by
      have hpt : ∀ x ∈ B_large,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) =
          g x + A₂.indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ)) x := by
        intro x hx
        dsimp only [g, ProbabilityTheory.levyCompensatedIntegrand]
        have hexp : Complex.I * (((ξ * x : ℝ) : ℂ)) = (x : ℂ) * (ξ : ℂ) * Complex.I := by
          push_cast; ring
        rw [hexp]
        by_cases h1 : |x| < 1
        · have hxA₂ : x ∈ A₂ := ⟨hx, h1⟩
          rw [if_pos h1, Set.indicator_of_mem hxA₂]; push_cast; ring
        · have hxA₂ : x ∉ A₂ := fun h => h1 h.2
          rw [if_neg h1, Set.indicator_of_notMem hxA₂]; ring
      rw [setIntegral_congr_fun hBlm hpt]
      have hind_int : IntegrableOn (A₂.indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ))) B_large ν := by
        have hsub : A₂ ⊆ B_large := fun _ hx => hx.1
        rw [IntegrableOn, integrable_indicator_iff hA₂m, IntegrableOn, Measure.restrict_restrict hA₂m,
          Set.inter_eq_left.mpr hsub]
        exact (Complex.ofRealCLM.integrable_comp hint_A₂).const_mul (Complex.I * (ξ : ℂ))
      rw [integral_add hg_int.integrableOn hind_int]
      congr 1
      have hsub : A₂ ⊆ B_large := fun _ hx => hx.1
      rw [setIntegral_indicator hA₂m, Set.inter_eq_right.mpr hsub, integral_const_mul]
      congr 1
      exact Complex.ofRealCLM.integral_comp_comm hint_A₂
    -- Combine `B_large ∪ B_small = Set.univ`
    have hsplit_g : (∫ x in B_large, g x ∂ν) + (∫ x in B_small, g x ∂ν) = ∫ x, g x ∂ν := by
      have hdisj : Disjoint B_large B_small := by
        rw [Set.disjoint_left]; intro x h1 h2
        change threshold < |x| at h1; change |x| ≤ threshold at h2; linarith
      have hunion : B_large ∪ B_small = Set.univ := by
        ext x; simp only [B_large, B_small, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact lt_or_ge threshold |x|
      rw [← setIntegral_union hdisj hBsm hg_int.integrableOn hg_int.integrableOn,
        hunion, setIntegral_univ]
    rw [hsmall_rel, hlarge_rel]
    unfold Kyprianou.Ch01.levyTripleExponent
    dsimp only [c_drift]
    have hsum : (∫ x in B_large, g x ∂ν) + (∫ x in B_small, g x ∂ν) =
        ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν := hsplit_g
    push_cast
    linear_combination -hsum
  -- Transfer jump-event probability from `X` to `X_prod`
  rw [levyProcess_jumpEvent_measure_eq hX hX_prod_levy hX_prod_marginals t hthresh]
  -- Pull back a.e. path properties to `P_prod`
  have hmap0 : P_prod.map Prod.fst = P₀ := by
    dsimp only [P_prod]; rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap12 : P_prod.map Prod.snd = P₁.prod P₂ := by
    dsimp only [P_prod]; rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmap1 : P_prod.map (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) = P₁ := by
    rw [show (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd, hmap12, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hmap2 : P_prod.map (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) = P₂ := by
    rw [show (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd measurable_snd, hmap12, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hτ_pos_ae : ∀ᵐ ω₂ ∂P₂, ω₂ ∈ E_large1 → 0 < τ ω₂ := by
    filter_upwards [hE1_jump] with ω₂ hω₂ hE; exact (hω₂ hE).1
  have hcont_at_τ_12 : ∀ᵐ p ∂(P₁.prod P₂),
      p.2 ∈ E_large1 → ContinuousAt (fun s : ℝ≥0 => X_small s p.1) (τ p.2) :=
    ae_continuousAt_independent_time P₁ P₂ X_small hXs_levy.cadlag_ae hXs_meas hXs_cnt
      E_large1 hE1_meas τ hτ_meas hτ_atomless hτ_pos_ae
  have h0_ae : ∀ᵐ ω ∂P_prod, Continuous (fun s : ℝ≥0 => X_gauss s ω.1) :=
    ae_comp_of_map_eq measurable_fst hmap0 hXg_cont
  have h1_jump_ae : ∀ᵐ ω ∂P_prod, ∀ s : ℝ≥0, 0 < s → s ≤ t → ∀ l : ℝ,
      Tendsto (fun u => X_small u ω.2.1) (nhdsWithin s (Set.Iio s)) (nhds l) →
      |X_small s ω.2.1 - l| ≤ threshold :=
    ae_comp_of_map_eq (measurable_fst.comp measurable_snd) hmap1 hXs_jump_le
  have h12_cont_ae : ∀ᵐ ω ∂P_prod,
      ω.2.2 ∈ E_large1 → ContinuousAt (fun s : ℝ≥0 => X_small s ω.2.1) (τ ω.2.2) :=
    ae_comp_of_map_eq measurable_snd hmap12 hcont_at_τ_12
  have h2_zero_ae : ∀ᵐ ω ∂P_prod, ω.2.2 ∉ E_large1 → ∀ s ≤ t, X_large s ω.2.2 = 0 :=
    ae_comp_of_map_eq (measurable_snd.comp measurable_snd) hmap2 hnotE1_zero
  have h2_jump_ae : ∀ᵐ ω ∂P_prod, ω.2.2 ∈ E_large1 →
      0 < τ ω.2.2 ∧ τ ω.2.2 ≤ t ∧ (∀ u < τ ω.2.2, X_large u ω.2.2 = 0) ∧
      threshold < |X_large (τ ω.2.2) ω.2.2| :=
    ae_comp_of_map_eq (measurable_snd.comp measurable_snd) hmap2 hE1_jump
  -- Prove `jumpEvent X_prod t threshold =ᵐ[P_prod] {ω | ω.2.2 ∈ E_large1}`
  have hae_jump : jumpEvent X_prod t threshold =ᵐ[P_prod] {ω : Ω₀ × (Ω₁ × Ω₂) | ω.2.2 ∈ E_large1} := by
    filter_upwards [h0_ae, h1_jump_ae, h12_cont_ae, h2_zero_ae, h2_jump_ae] with
      ω h0 h1j h12c h2z h2j
    change (ω ∈ jumpEvent X_prod t threshold) = (ω.2.2 ∈ E_large1)
    rw [eq_iff_iff]
    constructor
    · rintro ⟨s, hs0, hst, l, hlim, hgt⟩
      by_contra hnotE
      have hXl_zero_le : ∀ u ≤ t, X_large u ω.2.2 = 0 := h2z hnotE
      have hXs_lim : Tendsto (fun u : ℝ≥0 => X_small u ω.2.1)
          (nhdsWithin s (Set.Iio s)) (nhds (l - X_gauss s ω.1)) := by
        have hg_lim : Tendsto (fun u : ℝ≥0 => X_gauss u ω.1)
            (nhdsWithin s (Set.Iio s)) (nhds (X_gauss s ω.1)) :=
          (h0.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have hsub_lim := hlim.sub hg_lim
        refine hsub_lim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u (hu : u < s)
        dsimp only [X_prod, Xg_lift, Xl_lift, Xs_lift]
        rw [hXl_zero_le u (le_trans hu.le hst)]
        ring
      have hle := h1j s hs0 hst (l - X_gauss s ω.1) hXs_lim
      have heq : X_prod s ω - l = X_small s ω.2.1 - (l - X_gauss s ω.1) := by
        dsimp only [X_prod, Xg_lift, Xl_lift, Xs_lift]
        rw [hXl_zero_le s hst]
        ring
      rw [heq] at hgt
      linarith
    · intro hE
      obtain ⟨hτ0, hτt, hXl_lt, hXl_gt⟩ := h2j hE
      have hXs_cont_τ : ContinuousAt (fun s : ℝ≥0 => X_small s ω.2.1) (τ ω.2.2) := h12c hE
      refine ⟨τ ω.2.2, hτ0, hτt, X_gauss (τ ω.2.2) ω.1 + 0 + X_small (τ ω.2.2) ω.2.1, ?_, ?_⟩
      · have hg_lim : Tendsto (fun u : ℝ≥0 => X_gauss u ω.1)
            (nhdsWithin (τ ω.2.2) (Set.Iio (τ ω.2.2))) (nhds (X_gauss (τ ω.2.2) ω.1)) :=
          (h0.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have hl_lim : Tendsto (fun u : ℝ≥0 => X_large u ω.2.2)
            (nhdsWithin (τ ω.2.2) (Set.Iio (τ ω.2.2))) (nhds 0) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [self_mem_nhdsWithin] with u (hu : u < τ ω.2.2)
            exact (hXl_lt u hu).symm)
        have hs_lim : Tendsto (fun u : ℝ≥0 => X_small u ω.2.1)
            (nhdsWithin (τ ω.2.2) (Set.Iio (τ ω.2.2))) (nhds (X_small (τ ω.2.2) ω.2.1)) :=
          hXs_cont_τ.tendsto.mono_left nhdsWithin_le_nhds
        exact (hg_lim.add hl_lim).add hs_lim
      · have heq : X_prod (τ ω.2.2) ω - (X_gauss (τ ω.2.2) ω.1 + 0 + X_small (τ ω.2.2) ω.2.1) =
            X_large (τ ω.2.2) ω.2.2 := by
          dsimp only [X_prod, Xg_lift, Xl_lift, Xs_lift]; ring
        rw [heq]; exact hXl_gt
  rw [measure_congr hae_jump]
  have hpre : {ω : Ω₀ × (Ω₁ × Ω₂) | ω.2.2 ∈ E_large1} =
      (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) ⁻¹' E_large1 := rfl
  have hπ₂ : Measurable (fun ω : Ω₀ × (Ω₁ × Ω₂) => ω.2.2) := measurable_snd.comp measurable_snd
  rw [hpre, ← Measure.map_apply hπ₂ hE1_meas, hmap2, hP_E1]

/-! ### Section 4: Part (2) (`Continuous ↔ ν = 0`) from Part (1) -/

private lemma part2_continuous_iff_nu_zero
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ)) :
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔ ν = 0 := by
  constructor
  · intro hcont
    have hzero_k : ∀ k : ℕ, ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|} = 0 := by
      intro k
      have hkpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hsub : jumpEvent X 1 (1 / ((k : ℝ) + 1)) ⊆ {ω | ¬ Continuous (fun t : ℝ≥0 => X t ω)} := by
        rintro ω ⟨s, hs0, _, l, hl, hj⟩ hcw
        have hlim : Tendsto (fun u => X u ω) (nhdsWithin s (Set.Iio s)) (nhds (X s ω)) :=
          hcw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have hnebot : (nhdsWithin s (Set.Iio s)).NeBot := by
          rw [nhdsWithin_neBot]
          intro U hU
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
          have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
          let u : ℝ≥0 := ⟨(s : ℝ) - min ((s : ℝ) / 2) (ε / 2), by
            have := min_le_left ((s : ℝ) / 2) (ε / 2); linarith⟩
          refine ⟨u, hball ?_, ?_⟩
          · rw [Metric.mem_ball, NNReal.dist_eq]
            have hmin_pos : 0 < min ((s : ℝ) / 2) (ε / 2) := lt_min (by linarith) (by linarith)
            have hmin_le : min ((s : ℝ) / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
            have hsub' : (u : ℝ) - (s : ℝ) = -min ((s : ℝ) / 2) (ε / 2) := by
              change ((s : ℝ) - min ((s : ℝ) / 2) (ε / 2)) - (s : ℝ) = _; ring
            rw [hsub', abs_neg, abs_of_pos hmin_pos]; linarith
          · have hmin_pos : 0 < min ((s : ℝ) / 2) (ε / 2) := lt_min (by linarith) (by linarith)
            change (u : ℝ) < (s : ℝ)
            change (s : ℝ) - min ((s : ℝ) / 2) (ε / 2) < (s : ℝ)
            linarith
        have heq : l = X s ω := tendsto_nhds_unique hl hlim
        rw [heq, sub_self, abs_zero] at hj
        linarith
      have hP0 : P (jumpEvent X 1 (1 / ((k : ℝ) + 1))) = 0 :=
        measure_mono_null hsub (ae_iff.mp hcont)
      have hp1 := part1_jump_prob a σ ν hν P X hX hchar 1 (1 / ((k : ℝ) + 1)) hkpos
      rw [hP0] at hp1
      have hle0 : 1 - Real.exp (-(1 : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal) ≤ 0 :=
        ENNReal.ofReal_eq_zero.mp (by simpa using hp1.symm)
      have hexp : 1 ≤ Real.exp (-(ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal) := by
        simpa using (sub_nonpos.mp hle0)
      have hneg : 0 ≤ -(ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal := by
        rwa [Real.one_le_exp_iff] at hexp
      have htr0 : (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal = 0 :=
        le_antisymm (by linarith) ENNReal.toReal_nonneg
      exact (ENNReal.toReal_eq_zero_iff _).mp htr0 |>.resolve_right
        (levyMeasure_abs_gt_lt_top hν hkpos).ne
    have hcompl : ν ({0}ᶜ : Set ℝ) = 0 := by
      have hunion : ({0}ᶜ : Set ℝ) = ⋃ k : ℕ, {x : ℝ | 1 / ((k : ℝ) + 1) < |x|} := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · intro hx
          have hpos : 0 < |x| := abs_pos.mpr hx
          obtain ⟨k, hk⟩ := exists_nat_gt (1 / |x|)
          refine ⟨k, ?_⟩
          have h1 : 1 / |x| < (k : ℝ) + 1 := by linarith
          rw [div_lt_iff₀ hpos] at h1
          rw [div_lt_iff₀ (by positivity)]
          linarith
        · rintro ⟨k, hk⟩ h0
          rw [h0, abs_zero] at hk
          linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]
      rw [hunion]
      exact measure_iUnion_null hzero_k
    exact Measure.measure_univ_eq_zero.mp (by
      have huniv : (Set.univ : Set ℝ) = {0} ∪ ({0}ᶜ : Set ℝ) := by simp
      rw [huniv]
      exact le_antisymm ((measure_union_le _ _).trans (by simp [hν.1, hcompl])) zero_le')
  · intro hν0
    have hnojump : ∀ m k : ℕ, ∀ᵐ ω ∂P, ω ∉ jumpEvent X (m : ℝ≥0) (1 / ((k : ℝ) + 1)) := by
      intro m k
      have hkpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hp1 := part1_jump_prob a σ ν hν P X hX hchar (m : ℝ≥0) (1 / ((k : ℝ) + 1)) hkpos
      simp only [hν0, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, mul_zero,
        Real.exp_zero, sub_self, ENNReal.ofReal_zero] at hp1
      rw [ae_iff]
      simpa using hp1
    have hall : ∀ᵐ ω ∂P, ∀ m k : ℕ, ω ∉ jumpEvent X (m : ℝ≥0) (1 / ((k : ℝ) + 1)) :=
      ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => hnojump m k
    filter_upwards [hX.cadlag_ae, hall] with ω hcad hnj
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs0 : s = 0
    · subst hs0
      have hrc := (hcad 0).1
      have hici : Set.Ici (0 : ℝ≥0) = Set.univ := Set.ext fun _ => ⟨fun _ => trivial, fun _ => Set.mem_Ici.mpr zero_le⟩
      rwa [hici, continuousWithinAt_univ] at hrc
    · have hspos : 0 < s := pos_iff_ne_zero.mpr hs0
      obtain ⟨l, hl⟩ := (hcad s).2
      have hle_zero : |X s ω - l| = 0 := by
        by_contra hne
        have hpos : 0 < |X s ω - l| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / |X s ω - l|)
        have hklt : 1 / ((k : ℝ) + 1) < |X s ω - l| := by
          have h1 : 1 / |X s ω - l| < (k : ℝ) + 1 := by linarith
          rw [div_lt_iff₀ hpos] at h1
          rw [div_lt_iff₀ (by positivity)]
          linarith
        let m : ℕ := ⌈(s : ℝ)⌉₊
        have hsm : s ≤ (m : ℝ≥0) := by exact_mod_cast Nat.le_ceil (s : ℝ)
        exact hnj m k ⟨s, hspos, hsm, l, hl, hklt⟩
      have hl_eq : l = X s ω := (sub_eq_zero.mp (abs_eq_zero.mp hle_zero)).symm
      rw [hl_eq] at hl
      have hleft : ContinuousWithinAt (fun u => X u ω) (Set.Iio s) s := hl
      have hright : ContinuousWithinAt (fun u => X u ω) (Set.Ici s) s := (hcad s).1
      have hunion : ContinuousWithinAt (fun u => X u ω) (Set.Iio s ∪ Set.Ici s) s :=
        hleft.union hright
      have htot : Set.Iio s ∪ Set.Ici s = Set.univ := by
        ext u; simp [lt_or_ge]
      rwa [htot, continuousWithinAt_univ] at hunion

/-! ### Section 5: Part (4) (`ν univ = ⊤ → dense discontinuities`) from Part (1) -/

private lemma part4_dense_jumps
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (hinf : ν Set.univ = ⊤) :
    ∀ᵐ ω ∂P,
      closure {t : ℝ≥0 | ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} = Set.univ := by
  have hsup_top : Tendsto (fun k : ℕ => (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)
      atTop atTop := by
    have hmono : Monotone (fun k : ℕ => {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}) := by
      intro i j hij x hx
      have hle : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hij 1
      exact lt_of_le_of_lt hle hx
    have hunion : (⋃ k : ℕ, {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}) = ({0}ᶜ : Set ℝ) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, hk⟩ h0
        rw [h0, abs_zero] at hk; linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]
      · intro hx
        have hpos : 0 < |x| := abs_pos.mpr hx
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / |x|)
        refine ⟨k, ?_⟩
        have h1 : 1 / |x| < (k : ℝ) + 1 := by linarith
        rw [div_lt_iff₀ hpos] at h1
        rw [div_lt_iff₀ (by positivity)]
        linarith
    have hcompl_top : ν ({0}ᶜ : Set ℝ) = ⊤ := by
      have huniv : (Set.univ : Set ℝ) = {0} ∪ ({0}ᶜ : Set ℝ) := by simp
      have hle := measure_union_le (μ := ν) {0} ({0}ᶜ : Set ℝ)
      rw [← huniv, hinf, hν.1, zero_add] at hle
      exact top_unique hle
    have htend : Tendsto (fun k : ℕ => ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}) atTop (nhds ⊤) := by
      have := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν) hmono
      rwa [hunion, hcompl_top] at this
    rw [Filter.tendsto_atTop]
    intro M
    have hgt : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal M < ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|} :=
      htend.eventually (Ioi_mem_nhds ENNReal.ofReal_lt_top)
    filter_upwards [hgt] with k hk
    have hfin := levyMeasure_abs_gt_lt_top hν (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
    by_cases hM : 0 ≤ M
    · have h1 := ENNReal.toReal_strict_mono hfin.ne hk
      rw [ENNReal.toReal_ofReal hM] at h1
      exact h1.le
    · linarith [ENNReal.toReal_nonneg (a := ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|})]
  -- For any rational interval `(q₁, q₂)` with `0 ≤ q₁ < q₂`, a.s. there is a discontinuity in `(q₁, q₂)`
  have hinterval : ∀ (q₁ q₂ : ℚ), 0 ≤ q₁ → q₁ < q₂ →
      ∀ᵐ ω ∂P, ∃ s : ℝ≥0, (q₁ : ℝ) < (s : ℝ) ∧ (s : ℝ) < (q₂ : ℝ) ∧
        ¬ ContinuousAt (fun u : ℝ≥0 => X u ω) s := by
    intro q₁ q₂ hq₁ hq₁₂
    let a₁ : ℝ≥0 := ⟨(q₁ : ℝ), by exact_mod_cast hq₁⟩
    let δ : ℝ≥0 := ⟨((q₂ : ℝ) - (q₁ : ℝ)) / 2, by
      have : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₁₂
      linarith⟩
    have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
      have : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₁₂
      change 0 < ((q₂ : ℝ) - (q₁ : ℝ)) / 2; linarith
    let Y : ℝ≥0 → Ω → ℝ := fun u ω => X (a₁ + u) ω - X a₁ ω
    obtain ⟨hY, hYchar⟩ := levyProcess_shift hX a₁
    have hYchar' : ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (Y t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ) := fun t ξ => by
      rw [hYchar t ξ, hchar t ξ]
    let Good : Set Ω := {ω | ∃ s : ℝ≥0, (q₁ : ℝ) < (s : ℝ) ∧ (s : ℝ) < (q₂ : ℝ) ∧
      ¬ ContinuousAt (fun u : ℝ≥0 => X u ω) s}
    have hsub_k : ∀ k : ℕ, jumpEvent Y δ (1 / ((k : ℝ) + 1)) ⊆ Good := by
      intro k ω ⟨u, hu0, huδ, l, hl, hj⟩
      refine ⟨a₁ + u, ?_, ?_, ?_⟩
      · have : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
        change (q₁ : ℝ) < (a₁ : ℝ) + (u : ℝ)
        have : (a₁ : ℝ) = (q₁ : ℝ) := rfl
        linarith
      · have hule : (u : ℝ) ≤ (δ : ℝ) := by exact_mod_cast huδ
        have : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₁₂
        change (a₁ : ℝ) + (u : ℝ) < (q₂ : ℝ)
        have ha₁r : (a₁ : ℝ) = (q₁ : ℝ) := rfl
        have hδr : (δ : ℝ) = ((q₂ : ℝ) - (q₁ : ℝ)) / 2 := rfl
        linarith
      · intro hcont
        have hYcont : ContinuousAt (fun v : ℝ≥0 => Y v ω) u :=
          (hcont.comp (continuous_const.add continuous_id).continuousAt).sub continuousAt_const
        have hlim : Tendsto (fun v => Y v ω) (nhdsWithin u (Set.Iio u)) (nhds (Y u ω)) :=
          hYcont.tendsto.mono_left nhdsWithin_le_nhds
        have hnebot : (nhdsWithin u (Set.Iio u)).NeBot := by
          rw [nhdsWithin_neBot]
          intro U hU
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
          have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
          let v : ℝ≥0 := ⟨(u : ℝ) - min ((u : ℝ) / 2) (ε / 2), by
            have := min_le_left ((u : ℝ) / 2) (ε / 2); linarith⟩
          refine ⟨v, hball ?_, ?_⟩
          · rw [Metric.mem_ball, NNReal.dist_eq]
            have hmin_pos : 0 < min ((u : ℝ) / 2) (ε / 2) := lt_min (by linarith) (by linarith)
            have hmin_le : min ((u : ℝ) / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
            have hsub' : (v : ℝ) - (u : ℝ) = -min ((u : ℝ) / 2) (ε / 2) := by
              change ((u : ℝ) - min ((u : ℝ) / 2) (ε / 2)) - (u : ℝ) = _; ring
            rw [hsub', abs_neg, abs_of_pos hmin_pos]; linarith
          · have hmin_pos : 0 < min ((u : ℝ) / 2) (ε / 2) := lt_min (by linarith) (by linarith)
            change (v : ℝ) < (u : ℝ)
            change (u : ℝ) - min ((u : ℝ) / 2) (ε / 2) < (u : ℝ)
            linarith
        have heq : l = Y u ω := tendsto_nhds_unique hl hlim
        rw [heq, sub_self, abs_zero] at hj
        linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]
    have hcompl_le : ∀ k : ℕ,
        P Goodᶜ ≤ ENNReal.ofReal (Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)) := by
      intro k
      have hkpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hnm := jumpEvent_nullMeasurableSet hY δ hkpos
      have hp1 := part1_jump_prob a σ ν hν P Y hY hYchar' δ (1 / ((k : ℝ) + 1)) hkpos
      have hcompl_eq : P (jumpEvent Y δ (1 / ((k : ℝ) + 1)))ᶜ =
          1 - P (jumpEvent Y δ (1 / ((k : ℝ) + 1))) := by
        rw [measure_compl₀ hnm (measure_ne_top P _), measure_univ]
      have hsub_compl : Goodᶜ ⊆ (jumpEvent Y δ (1 / ((k : ℝ) + 1)))ᶜ :=
        Set.compl_subset_compl.mpr (hsub_k k)
      calc P Goodᶜ ≤ P (jumpEvent Y δ (1 / ((k : ℝ) + 1)))ᶜ := measure_mono hsub_compl
        _ = 1 - ENNReal.ofReal (1 - Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)) := by
            rw [hcompl_eq, hp1]
        _ = ENNReal.ofReal (Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)) := by
            have hexp_le : Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have : 0 ≤ (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal := ENNReal.toReal_nonneg
              nlinarith
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
            congr 1; ring
    have htend0 : Tendsto (fun k : ℕ =>
        ENNReal.ofReal (Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun k : ℕ => -(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)
          atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hsup_top
      have h2 : Tendsto (fun k : ℕ =>
          Real.exp (-(δ : ℝ) * (ν {x : ℝ | 1 / ((k : ℝ) + 1) < |x|}).toReal)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h1
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h2
    have hP0 : P Goodᶜ = 0 :=
      le_antisymm (ge_of_tendsto htend0 (Eventually.of_forall hcompl_le)) zero_le'
    rw [ae_iff]
    exact hP0
  have hall : ∀ᵐ ω ∂P, ∀ (q₁ q₂ : ℚ), 0 ≤ q₁ → q₁ < q₂ →
      ∃ s : ℝ≥0, (q₁ : ℝ) < (s : ℝ) ∧ (s : ℝ) < (q₂ : ℝ) ∧
        ¬ ContinuousAt (fun u : ℝ≥0 => X u ω) s := by
    rw [ae_all_iff]; intro q₁
    rw [ae_all_iff]; intro q₂
    by_cases h : 0 ≤ q₁ ∧ q₁ < q₂
    · filter_upwards [hinterval q₁ q₂ h.1 h.2] with ω hω _ _
      exact hω
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [hall] with ω hω
  apply Set.eq_univ_of_forall
  intro t
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q₁, hq₁_gt, hq₁_lt⟩ := exists_rat_btwn (show (t : ℝ) < (t : ℝ) + ε / 2 by linarith)
  obtain ⟨q₂, hq₂_gt, hq₂_lt⟩ := exists_rat_btwn (show (q₁ : ℝ) < (t : ℝ) + ε by linarith)
  have hq₁_nn : 0 ≤ q₁ := by
    have : (0 : ℝ) ≤ (q₁ : ℝ) := le_trans t.coe_nonneg hq₁_gt.le
    exact_mod_cast this
  have hq₁₂ : q₁ < q₂ := by exact_mod_cast hq₂_gt
  obtain ⟨s, hs1, hs2, hdisc⟩ := hω q₁ q₂ hq₁_nn hq₁₂
  refine ⟨s, hdisc, ?_⟩
  rw [NNReal.dist_eq, abs_of_neg (by linarith : (t : ℝ) - (s : ℝ) < 0)]
  linarith

/-! ### Section 6: Part (3)(→) (`piecewiseLinear → σ = 0 ∧ ν univ < ⊤`) -/

private def piecewiseLinear (f : ℝ≥0 → ℝ) : Prop :=
  ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
    Tendsto T atTop atTop ∧
    ∀ n : ℕ, ∃ (slope intercept : ℝ),
      ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
        f t = slope * (t : ℝ) + intercept

private lemma piecewiseLinear_closure_ne_univ {f : ℝ≥0 → ℝ} (hf : piecewiseLinear f) :
    closure {t : ℝ≥0 | ¬ ContinuousAt f t} ≠ Set.univ := by
  obtain ⟨T, hT0, hTmono, _, hTlin⟩ := hf
  obtain ⟨slope, intercept, hlin⟩ := hTlin 0
  have hT1_pos : (0 : ℝ≥0) < T 1 := hT0 ▸ hTmono zero_lt_one
  let m : ℝ≥0 := T 1 / 2
  have hm_pos : 0 < m := by
    change (0 : ℝ) < (T 1 : ℝ) / 2
    have : (0 : ℝ) < (T 1 : ℝ) := by exact_mod_cast hT1_pos
    linarith
  have hm_lt : m < T 1 := by
    change (T 1 : ℝ) / 2 < (T 1 : ℝ)
    have : (0 : ℝ) < (T 1 : ℝ) := by exact_mod_cast hT1_pos
    linarith
  have hdisj : Set.Ioo (0 : ℝ≥0) (T 1) ∩ {t : ℝ≥0 | ¬ ContinuousAt f t} = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    rintro ⟨ht0, ht1⟩
    have hev : f =ᶠ[nhds t] fun u : ℝ≥0 => slope * (u : ℝ) + intercept := by
      have hmem : Set.Ioo (0 : ℝ≥0) (T 1) ∈ nhds t := Ioo_mem_nhds ht0 ht1
      filter_upwards [hmem] with u hu
      exact hlin u (hT0 ▸ hu.1.le) hu.2
    have hcont : ContinuousAt (fun u : ℝ≥0 => slope * (u : ℝ) + intercept) t :=
      ((continuous_const.mul NNReal.continuous_coe).add continuous_const).continuousAt
    exact hcont.congr hev.symm
  intro heq
  have hm_cl : m ∈ closure {t : ℝ≥0 | ¬ ContinuousAt f t} := by rw [heq]; trivial
  have hne := mem_closure_iff.mp hm_cl (Set.Ioo (0 : ℝ≥0) (T 1)) isOpen_Ioo ⟨hm_pos, hm_lt⟩
  rw [hdisj] at hne
  exact Set.not_nonempty_empty hne

/-- If `‖charFun μ ξ‖ ≤ exp(-c * ξ^2)` with `c > 0`, then `μ {0} = 0`. -/
private lemma measure_singleton_zero_eq_zero_of_charFun_gaussian_decay
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ ξ : ℝ, ‖charFun μ ξ‖ ≤ Real.exp (-c * ξ ^ 2)) :
    μ {0} = 0 := by
  -- For every `R > 0`, compute `(1 / (2 R)) * ∫ ξ in Icc (-R) R, charFun μ ξ`
  have hinner_eval : ∀ (R : ℝ) (hR : 0 < R) (x : ℝ),
      ‖((1 : ℂ) / (2 * (R : ℂ))) * ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ ≤ 1 ∧
      (x = 0 → ((1 : ℂ) / (2 * (R : ℂ))) * ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) = 1) ∧
      (x ≠ 0 → ‖((1 : ℂ) / (2 * (R : ℂ))) * ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ ≤
        1 / (R * |x|)) := by
    intro R hR x
    have hcont : Continuous (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)
    have hnorm_one : ∀ ξ : ℝ, ‖Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := fun ξ => by
      have hcast : (ξ : ℂ) * (x : ℂ) * Complex.I = ((ξ * x : ℝ) : ℂ) * Complex.I := by push_cast; rfl
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    have hle1 : ‖((1 : ℂ) / (2 * (R : ℂ))) * ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
      have hint_le : ‖∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ ≤ 2 * R := by
        calc ‖∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖
            ≤ ∫ ξ in Set.Icc (-R) R, ‖Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ _ in Set.Icc (-R) R, (1 : ℝ) := by simp_rw [hnorm_one]
          _ = (volume (Set.Icc (-R) R)).toReal := by
              rw [setIntegral_const, Measure.real, smul_eq_mul, mul_one]
          _ = 2 * R := by
              rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
      have h2R : (0 : ℝ) < 2 * R := by linarith
      calc 1 / (2 * R) * ‖∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)‖
          ≤ 1 / (2 * R) * (2 * R) := mul_le_mul_of_nonneg_left hint_le (by positivity)
        _ = 1 := by field_simp
    refine ⟨hle1, ?_, ?_⟩
    · intro hx0
      subst hx0
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        setIntegral_const, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R - -R), Complex.real_smul, mul_one]
      have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
      have hsub : ((R - -R : ℝ) : ℂ) = 2 * (R : ℂ) := by push_cast; ring
      rw [hsub]
      field_simp [hRne]
    · intro hxne
      have hIcc_eq : ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) =
          ∫ ξ in (-R)..R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) := by
        rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
          MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [hIcc_eq]
      let F : ℝ → ℂ := fun ξ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) / ((x : ℂ) * Complex.I)
      have hxI : (x : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hxne) Complex.I_ne_zero
      have hFderiv : ∀ ξ ∈ Set.uIcc (-R) R,
          HasDerivAt F (Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) ξ := fun ξ _ => by
        have hlin : HasDerivAt (fun r : ℝ => (r : ℂ) * (x : ℂ) * Complex.I) ((x : ℂ) * Complex.I) ξ := by
          have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 ξ := Complex.ofRealCLM.hasDerivAt
          simpa [mul_assoc] using (h1.mul_const ((x : ℂ) * Complex.I))
        have hd := hlin.cexp.div_const ((x : ℂ) * Complex.I)
        have heq : Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) * ((x : ℂ) * Complex.I) /
            ((x : ℂ) * Complex.I) = Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) :=
          mul_div_cancel_right₀ _ hxI
        rwa [heq] at hd
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv (hcont.intervalIntegrable (-R) R)]
      have hnum : ‖F R - F (-R)‖ ≤ 2 / |x| := by
        dsimp only [F]
        rw [← sub_div, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one]
        refine div_le_div_of_nonneg_right ?_ (abs_nonneg x)
        calc ‖Complex.exp ((R : ℂ) * (x : ℂ) * Complex.I) -
              Complex.exp (((-R : ℝ) : ℂ) * (x : ℂ) * Complex.I)‖
            ≤ ‖Complex.exp ((R : ℂ) * (x : ℂ) * Complex.I)‖ +
              ‖Complex.exp (((-R : ℝ) : ℂ) * (x : ℂ) * Complex.I)‖ := norm_sub_le _ _
          _ = 2 := by rw [hnorm_one R, hnorm_one (-R)]; norm_num
      rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
      have h1 : 1 / (2 * R) * ‖F R - F (-R)‖ ≤ 1 / (2 * R) * (2 / |x|) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      have h2 : 1 / (2 * R) * (2 / |x|) = 1 / (R * |x|) := by
        have hxpos : |x| ≠ 0 := abs_ne_zero.mpr hxne
        field_simp [hR.ne', hxpos]
      linarith
  -- Fubini on `Icc (-R) R × ℝ`
  have hfubini : ∀ (R : ℝ) (hR : 0 < R),
      ((1 : ℂ) / (2 * (R : ℂ))) * ∫ ξ in Set.Icc (-R) R, charFun μ ξ =
      ∫ x, (((1 : ℂ) / (2 * (R : ℂ))) *
        ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) ∂μ := by
    intro R hR
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-R) R)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hjoint_cont : Continuous (fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) * (p.2 : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        (((Complex.continuous_ofReal.comp continuous_fst).mul
          (Complex.continuous_ofReal.comp continuous_snd)).mul continuous_const)
    have hjoint_int : Integrable (Function.uncurry fun ξ x : ℝ =>
        Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
        ((volume.restrict (Set.Icc (-R) R)).prod μ) :=
      Integrable.of_bound hjoint_cont.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
        have hcast : (p.1 : ℂ) * (p.2 : ℂ) * Complex.I = ((p.1 * p.2 : ℝ) : ℂ) * Complex.I := by
          push_cast; rfl
        change ‖Complex.exp ((p.1 : ℂ) * (p.2 : ℂ) * Complex.I)‖ ≤ 1
        rw [hcast, Complex.norm_exp_ofReal_mul_I])
    have hswap := MeasureTheory.integral_integral_swap hjoint_int
    have hchar_eq : (∫ ξ in Set.Icc (-R) R, charFun μ ξ) =
        ∫ ξ in Set.Icc (-R) R, ∫ x, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
      refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
      exact charFun_apply_real ξ
    rw [hchar_eq, hswap, ← integral_const_mul]
  -- Dominated convergence on the RHS as `R = n + 1 → ∞`
  have hrhs_tend : Tendsto (fun n : ℕ =>
      ∫ x, (((1 : ℂ) / (2 * (((n : ℝ) + 1 : ℝ) : ℂ))) *
        ∫ ξ in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
          Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) ∂μ)
      atTop (nhds (∫ x, ({0} : Set ℝ).indicator (fun _ => (1 : ℂ)) x ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
      (integrable_const 1) ?_ ?_
    · intro n
      let R : ℝ := (n : ℝ) + 1
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-R) R)) :=
        ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
      have hmeas_inner : StronglyMeasurable (fun x : ℝ =>
          ∫ ξ in Set.Icc (-R) R, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) := by
        have hcont : Continuous (fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) * (p.2 : ℂ) * Complex.I)) :=
          Complex.continuous_exp.comp
            (((Complex.continuous_ofReal.comp continuous_fst).mul
              (Complex.continuous_ofReal.comp continuous_snd)).mul continuous_const)
        exact hcont.stronglyMeasurable.integral_prod_left
      exact (stronglyMeasurable_const.mul hmeas_inner).aestronglyMeasurable
    · intro n
      exact Eventually.of_forall fun x => (hinner_eval ((n : ℝ) + 1) (by positivity) x).1
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x = 0
      · subst hx
        simp only [Set.mem_singleton_iff, Set.indicator_of_mem]
        have heq : ∀ n : ℕ, ((1 : ℂ) / (2 * (((n : ℝ) + 1 : ℝ) : ℂ))) *
            ∫ ξ in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
              Complex.exp ((ξ : ℂ) * ((0 : ℝ) : ℂ) * Complex.I) = 1 :=
          fun n => (hinner_eval ((n : ℝ) + 1) (by positivity) 0).2.1 rfl
        simp_rw [heq]; exact tendsto_const_nhds
      · simp only [Set.mem_singleton_iff, hx, not_false_eq_true, Set.indicator_of_notMem]
        refine squeeze_zero_norm (fun n =>
          (hinner_eval ((n : ℝ) + 1) (by positivity) x).2.2 hx) ?_
        have hpos : 0 < |x| := abs_pos.mpr hx
        have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
          simpa [one_div, Function.comp_def] using
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hmul : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * (1 / |x|)) atTop (nhds 0) := by
          simpa using hinv.mul_const (1 / |x|)
        refine hmul.congr fun n => ?_
        field_simp
  -- LHS tends to `0` by Gaussian integrability
  have hlhs_tend : Tendsto (fun n : ℕ =>
      ((1 : ℂ) / (2 * (((n : ℝ) + 1 : ℝ) : ℂ))) *
        ∫ ξ in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), charFun μ ξ)
      atTop (nhds 0) := by
    have hgauss_int : Integrable (fun ξ : ℝ => Real.exp (-c * ξ ^ 2)) volume :=
      integrable_exp_neg_mul_sq hc
    let M : ℝ := ∫ ξ : ℝ, Real.exp (-c * ξ ^ 2)
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / (2 * ((n : ℝ) + 1)) * M) (fun n => ?_) ?_
    · let R : ℝ := (n : ℝ) + 1
      have hR : 0 < R := by positivity
      rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
      have hint_le : ‖∫ ξ in Set.Icc (-R) R, charFun μ ξ‖ ≤ M := by
        calc ‖∫ ξ in Set.Icc (-R) R, charFun μ ξ‖
            ≤ ∫ ξ in Set.Icc (-R) R, ‖charFun μ ξ‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ ξ in Set.Icc (-R) R, Real.exp (-c * ξ ^ 2) := by
              refine setIntegral_mono_on ?_ hgauss_int.integrableOn measurableSet_Icc fun ξ _ => hdecay ξ
              have hcont : Continuous (fun ξ : ℝ => ‖charFun μ ξ‖) :=
                continuous_norm.comp (continuous_charFun)
              exact hcont.continuousOn.integrableOn_Icc
          _ ≤ ∫ ξ : ℝ, Real.exp (-c * ξ ^ 2) :=
              setIntegral_le_integral hgauss_int (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_left hint_le (by positivity)
    · have hinv : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (nhds 0) := by
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
          simpa [one_div, Function.comp_def] using
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1.const_mul (1 / 2 : ℝ)
      simpa using hinv.mul_const M
  have heq_seq : (fun n : ℕ =>
      ((1 : ℂ) / (2 * (((n : ℝ) + 1 : ℝ) : ℂ))) *
        ∫ ξ in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), charFun μ ξ) =
      fun n : ℕ => ∫ x, (((1 : ℂ) / (2 * (((n : ℝ) + 1 : ℝ) : ℂ))) *
        ∫ ξ in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
          Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) ∂μ :=
    funext fun n => hfubini ((n : ℝ) + 1) (by positivity)
  rw [heq_seq] at hlhs_tend
  have hzero_c : ∫ x, ({0} : Set ℝ).indicator (fun _ => (1 : ℂ)) x ∂μ = 0 :=
    tendsto_nhds_unique hrhs_tend hlhs_tend
  rw [integral_indicator_const _ (measurableSet_singleton (0 : ℝ)), Measure.real,
    Complex.real_smul, mul_one] at hzero_c
  have htr0 : (μ {0}).toReal = 0 := Complex.ofReal_eq_zero.mp hzero_c
  exact (ENNReal.toReal_eq_zero_iff _).mp htr0 |>.resolve_right (measure_ne_top μ {0})

private lemma part3_fwd_sigma_zero
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (hpl : ∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) :
    σ = 0 := by
  by_contra hσne
  have hσpos : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hσne
  -- Show for every `h > 0`, `P {ω | X h ω - X 0 ω = X (2 * h) ω - X h ω} = 0`
  have hzero_h : ∀ h : ℝ≥0, 0 < h →
      P {ω | ProbabilityTheory.increment X 0 h ω = ProbabilityTheory.increment X h (h + h) ω} = 0 := by
    intro h hh
    let I₁ : Ω → ℝ := ProbabilityTheory.increment X 0 h
    let I₂ : Ω → ℝ := ProbabilityTheory.increment X h (h + h)
    have hI₁_eq : I₁ = X h := by funext ω; simp [I₁, ProbabilityTheory.increment, hX.start_zero]
    have hI₁_aem : AEMeasurable I₁ P := by rw [hI₁_eq]; exact levyProcess_aemeasurable hX h
    have hI₂_aem : AEMeasurable I₂ P :=
      (levyProcess_aemeasurable hX (h + h)).sub (levyProcess_aemeasurable hX h)
    have hI₂_law : P.map I₂ = P.map (X h) := by
      have hid := (hX.stationary_increments h h).map_eq
      rwa [show ProbabilityTheory.increment X 0 h = X h from hI₁_eq] at hid
    -- `I₁` and `I₂` are independent from `hX.indep_increments` on `![0, h, h + h]`
    let ts : Fin 3 → ℝ≥0 := ![0, h, h + h]
    have hts_mono : Monotone ts := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [ts] at hij ⊢
    have hind_all := hX.indep_increments 2 ts hts_mono
    have hind12 : IndepFun I₁ I₂ P := by
      have hpair := hind_all.indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
      simpa [I₁, I₂, ts] using hpair
    have hind_neg : IndepFun I₁ (-I₂) P := hind12.comp measurable_id measurable_neg
    have hdiff_eq : (fun ω => I₁ ω - I₂ ω) = I₁ + (-I₂) := by funext ω; simp [sub_eq_add_neg]
    have hchar_diff : ∀ ξ : ℝ,
        ‖charFun (P.map (fun ω => I₁ ω - I₂ ω)) ξ‖ ≤ Real.exp (-(h : ℝ) * (σ : ℝ) ^ 2 * ξ ^ 2) := by
      intro ξ
      rw [hdiff_eq]
      have hmul := congrFun (hind_neg.charFun_map_add_eq_mul hI₁_aem hI₂_aem.neg) ξ
      simp only [Pi.mul_apply] at hmul
      rw [hmul, norm_mul]
      have hneg_char : charFun (P.map (-I₂)) ξ = charFun (P.map (X h)) (-ξ) := by
        have hcomp : (-I₂) = (fun x : ℝ => -x) ∘ I₂ := rfl
        rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable measurable_neg.aemeasurable hI₂_aem,
          hI₂_law, charFun_apply_real, charFun_apply_real]
        have hcont_exp : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
          Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
            continuous_const)
        rw [integral_map measurable_neg.aemeasurable hcont_exp.aestronglyMeasurable]
        congr 1; funext x; congr 1; push_cast; ring
      rw [hI₁_eq, hneg_char, hchar h ξ, hchar h (-ξ), Complex.norm_exp, Complex.norm_exp]
      have hre1 := levyTripleExponent_re_le a σ ν hν ξ
      have hre2 := levyTripleExponent_re_le a σ ν hν (-ξ)
      have hmul1 : (((h : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ).re ≤
          -((h : ℝ) * ((σ : ℝ) ^ 2 * ξ ^ 2 / 2)) := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have := mul_le_mul_of_nonneg_left hre1 h.coe_nonneg
        linarith
      have hmul2 : (((h : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ (-ξ)).re ≤
          -((h : ℝ) * ((σ : ℝ) ^ 2 * ξ ^ 2 / 2)) := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have := mul_le_mul_of_nonneg_left hre2 h.coe_nonneg
        have hsq : (-ξ) ^ 2 = ξ ^ 2 := neg_sq ξ
        rw [hsq] at this
        linarith
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hdiff_aem : AEMeasurable (fun ω => I₁ ω - I₂ ω) P := hI₁_aem.sub hI₂_aem
    haveI : IsProbabilityMeasure (P.map (fun ω => I₁ ω - I₂ ω)) :=
      Measure.isProbabilityMeasure_map hdiff_aem
    have hc_pos : 0 < (h : ℝ) * (σ : ℝ) ^ 2 := by
      have hh' : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
      positivity
    have hmap0 : (P.map (fun ω => I₁ ω - I₂ ω)) {0} = 0 :=
      measure_singleton_zero_eq_zero_of_charFun_gaussian_decay hc_pos fun ξ => by
        simpa [mul_assoc, neg_mul] using hchar_diff ξ
    rw [Measure.map_apply_of_aemeasurable hdiff_aem (measurableSet_singleton (0 : ℝ))] at hmap0
    have hset : (fun ω => I₁ ω - I₂ ω) ⁻¹' {0} = {ω | I₁ ω = I₂ ω} := by
      ext ω; simp [sub_eq_zero]
    rwa [hset] at hmap0
  -- Every `piecewiseLinear` path with `X 0 ω = 0` satisfies `I₁ = I₂` for `h = 1 / (2 * (n + 1))`
  let E : ℕ → Set Ω := fun n =>
    let h : ℝ≥0 := 1 / (2 * ((n : ℝ≥0) + 1))
    {ω | ProbabilityTheory.increment X 0 h ω = ProbabilityTheory.increment X h (h + h) ω}
  have hsub : {ω | piecewiseLinear (fun t => X t ω)} ⊆ ⋃ n : ℕ, E n := by
    intro ω ⟨T, hT0, hTmono, _, hTlin⟩
    obtain ⟨slope, intercept, hlin⟩ := hTlin 0
    have hT1_pos : (0 : ℝ) < (T 1 : ℝ) := by
      have : (0 : ℝ≥0) < T 1 := hT0 ▸ hTmono zero_lt_one
      exact_mod_cast this
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (T 1 : ℝ))
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    let h : ℝ≥0 := 1 / (2 * ((n : ℝ≥0) + 1))
    have h2h_lt : h + h < T 1 := by
      change (1 : ℝ) / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) < (T 1 : ℝ)
      have h1 : 1 / (T 1 : ℝ) < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hT1_pos] at h1
      have h2 : (1 : ℝ) / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        have : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp; ring
      rw [h2, div_lt_iff₀ (by positivity)]
      linarith
    have hh_lt : h < T 1 := lt_of_le_of_lt le_self_add h2h_lt
    have h0_lt : (0 : ℝ≥0) < T 1 := hT0 ▸ hTmono zero_lt_one
    have hf0 : X 0 ω = slope * (0 : ℝ≥0) + intercept := hlin 0 (hT0 ▸ le_rfl) h0_lt
    have hfh : X h ω = slope * (h : ℝ) + intercept := hlin h (hT0 ▸ zero_le') hh_lt
    have hf2h : X (h + h) ω = slope * ((h + h : ℝ≥0) : ℝ) + intercept := hlin (h + h) (hT0 ▸ zero_le') h2h_lt
    change X h ω - X 0 ω = X (h + h) ω - X h ω
    rw [hf0, hfh, hf2h]
    push_cast; ring
  have hnull : P (⋃ n : ℕ, E n) = 0 :=
    measure_iUnion_null fun n => hzero_h (1 / (2 * ((n : ℝ≥0) + 1))) (by positivity)
  have hP0 : P {ω | piecewiseLinear (fun t => X t ω)} = 0 :=
    measure_mono_null hsub hnull
  have hP1 : P {ω | piecewiseLinear (fun t => X t ω)} = 1 := by
    have hc : P {ω | piecewiseLinear (fun t => X t ω)}ᶜ = 0 := ae_iff.mp hpl
    have h1 := measure_union_le (μ := P) {ω | piecewiseLinear (fun t => X t ω)}
      {ω | piecewiseLinear (fun t => X t ω)}ᶜ
    rw [Set.union_compl_self, measure_univ, hc, add_zero] at h1
    exact le_antisymm (prob_le_one) h1
  rw [hP0] at hP1
  exact zero_ne_one hP1

private lemma part3_fwd
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (hpl : ∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) :
    σ = 0 ∧ ν Set.univ < ⊤ := by
  refine ⟨part3_fwd_sigma_zero a σ ν hν P X hX hchar hpl, ?_⟩
  by_contra hnotlt
  have htop : ν Set.univ = ⊤ := top_unique (le_of_not_gt hnotlt)
  have hdense := part4_dense_jumps a σ ν hν P X hX hchar htop
  have hboth : ∀ᵐ ω ∂P, False := by
    filter_upwards [hpl, hdense] with ω h1 h2
    exact piecewiseLinear_closure_ne_univ h1 h2
  have h0 : P Set.univ = 0 := by
    simpa [ae_iff] using hboth
  rw [measure_univ] at h0
  exact one_ne_zero h0

/-! ### Section 7: Part (3)(←) (`σ = 0 ∧ ν univ < ⊤ → piecewiseLinear`) -/

private lemma one_sub_exp_neg_le {x : ℝ} (hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

private lemma poissonMeasureENN_apply_zero (μ : ℝ≥0) :
    LevyStochCalc.Poisson.poissonMeasureENN μ {0} = ENNReal.ofReal (Real.exp (-(μ : ℝ))) := by
  unfold LevyStochCalc.Poisson.poissonMeasureENN
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (0 : ℝ≥0∞))]
  have hpre : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {0} = {0} := by
    ext n; simp
  rw [hpre, ProbabilityTheory.poissonMeasure, Measure.sum_apply _ (measurableSet_singleton 0)]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    have hnot : n ∉ ({0} : Set ℕ) := by simpa using hn
    simp [Measure.dirac_apply' _ (measurableSet_singleton 0), Set.indicator_of_notMem hnot]

/-- Dyadic grid constancy predicate for a path `f` on `[a, b]`. -/
private def ConstDyad (f : ℝ≥0 → ℝ) (a b : ℝ≥0) : Prop :=
  ∀ (r : ℕ) (k : Fin (2 ^ r)),
    f (a + ((k.1 + 1 : ℕ) : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r)) =
      f (a + (k.1 : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r))

private lemma constDyad_eq_left {f : ℝ≥0 → ℝ} {a b : ℝ≥0} (h : ConstDyad f a b)
    (r : ℕ) (k : ℕ) (hk : k ≤ 2 ^ r) :
    f (a + (k : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r)) = f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : k < 2 ^ r := Nat.lt_of_succ_le hk
    have hstep := h r ⟨k, hlt⟩
    simpa [ih (Nat.le_of_lt hlt)] using hstep

private lemma constDyad_endpoints {f : ℝ≥0 → ℝ} {a b : ℝ≥0} (hab : a ≤ b)
    (h : ConstDyad f a b) : f b = f a := by
  have h0 := h 0 ⟨0, by norm_num⟩
  simpa [add_tsub_cancel_of_le hab] using h0

private lemma constDyad_Icc_const {f : ℝ≥0 → ℝ} (hrc : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    {a b : ℝ≥0} (hab : a ≤ b) (h : ConstDyad f a b) :
    ∀ u ∈ Set.Icc a b, f u = f a := by
  intro u hu
  rcases eq_or_lt_of_le hu.2 with rfl | hub
  · exact constDyad_endpoints hab h
  · have hpos : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
      have ha : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.1
      have hb : (u : ℝ) < (b : ℝ) := by exact_mod_cast hub
      linarith
    -- Approximate `u ∈ [a, b)` from the right by dyadic grid points in `[a, b]`
    let k : ℕ → ℕ := fun r => ⌊(((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r⌋₊ + 1
    have hk_le : ∀ r : ℕ, k r ≤ 2 ^ r := fun r => by
      have hfrac : ((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) < 1 := by
        rw [div_lt_one hpos]
        have : (u : ℝ) < (b : ℝ) := by exact_mod_cast hub
        linarith
      have hmul : (((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r < ((2 ^ r : ℕ) : ℝ) := by
        push_cast
        linarith [mul_lt_mul_of_pos_right hfrac (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)]
      have hfl : ⌊(((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r⌋₊ < 2 ^ r :=
        (Nat.floor_lt (by
          have : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.1
          exact mul_nonneg (div_nonneg (by linarith) hpos.le) (by positivity))).mpr hmul
      dsimp only [k]; omega
    let q : ℕ → ℝ≥0 := fun r => a + (k r : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r)
    have hq_ge : ∀ r : ℕ, u ≤ q r := fun r => by
      have h2r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
      have hfl : (((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r < (k r : ℝ) := by
        dsimp only [k]; push_cast
        exact Nat.lt_floor_add_one _
      change (u : ℝ) ≤ (a : ℝ) + (k r : ℝ) * ((b - a : ℝ≥0) : ℝ) / (2 : ℝ) ^ r
      rw [NNReal.coe_sub hab]
      have h1 : (u : ℝ) - (a : ℝ) < (k r : ℝ) * ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r := by
        rw [lt_div_iff₀ h2r]
        have := mul_lt_mul_of_pos_right hfl hpos
        field_simp [hpos.ne'] at this
        linarith
      linarith
    have hq_le : ∀ r : ℕ, (q r : ℝ) ≤ (u : ℝ) + ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r := fun r => by
      have h2r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
      have hnn : 0 ≤ (((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r := by
        have : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.1
        exact mul_nonneg (div_nonneg (by linarith) hpos.le) (by positivity)
      have hfl : (k r : ℝ) ≤ (((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r + 1 := by
        dsimp only [k]; push_cast; linarith [Nat.floor_le hnn]
      change (a : ℝ) + (k r : ℝ) * ((b - a : ℝ≥0) : ℝ) / (2 : ℝ) ^ r ≤ _
      rw [NNReal.coe_sub hab]
      have h1 : (k r : ℝ) * ((b : ℝ) - (a : ℝ)) ≤
          (((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) * (2 : ℝ) ^ r + 1) * ((b : ℝ) - (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hfl hpos.le
      have h2 : ((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 : ℝ) ^ r + 1) * ((b : ℝ) - (a : ℝ)) =
          ((u : ℝ) - (a : ℝ)) * (2 : ℝ) ^ r + ((b : ℝ) - (a : ℝ)) := by field_simp [hpos.ne']
      rw [h2] at h1
      have h3 : (k r : ℝ) * ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r ≤
          ((u : ℝ) - (a : ℝ)) + ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r := by
        rw [div_le_iff₀ h2r]
        have h4 : (((u : ℝ) - (a : ℝ)) + ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r) * (2 : ℝ) ^ r =
            ((u : ℝ) - (a : ℝ)) * (2 : ℝ) ^ r + ((b : ℝ) - (a : ℝ)) := by field_simp [h2r.ne']
        linarith
      linarith
    have hq_tend : Tendsto q atTop (nhds u) := by
      rw [← NNReal.tendsto_coe]
      have hgeom : Tendsto (fun r : ℕ => ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r) atTop (nhds 0) := by
        have h1 : Tendsto (fun r : ℕ => (1 / 2 : ℝ) ^ r) atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa [div_eq_mul_inv, one_div, inv_pow] using h1.const_mul ((b : ℝ) - (a : ℝ))
      have hhi : Tendsto (fun r : ℕ => (u : ℝ) + ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r) atTop (nhds (u : ℝ)) := by
        simpa using (tendsto_const_nhds (x := (u : ℝ))).add hgeom
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi
        (fun r => by exact_mod_cast hq_ge r) hq_le
    have hq_within : Tendsto q atTop (nhdsWithin u (Set.Ici u)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq_tend (Eventually.of_forall hq_ge)
    have hlim1 : Tendsto (fun r => f (q r)) atTop (nhds (f u)) := (hrc u).tendsto.comp hq_within
    have hconst : (fun r => f (q r)) = fun _ => f a := funext fun r => constDyad_eq_left h r (k r) (hk_le r)
    rw [hconst] at hlim1
    exact tendsto_nhds_unique hlim1 tendsto_const_nhds

private lemma constDyad_join {f : ℝ≥0 → ℝ} {a b : ℝ≥0} (hab : a ≤ b) :
    let mid : ℝ≥0 := a + (b - a) / 2
    ConstDyad f a mid → ConstDyad f mid b → ConstDyad f a b := by
  intro mid h1 h2 r k
  cases r with
  | zero =>
    have hk0 : k.1 = 0 := by omega
    have hmid_le : mid ≤ b := by
      change (a : ℝ) + ((b - a : ℝ≥0) : ℝ) / 2 ≤ (b : ℝ)
      rw [NNReal.coe_sub hab]; linarith
    have ha_le : a ≤ mid := le_self_add
    have he1 := constDyad_endpoints ha_le h1
    have he2 := constDyad_endpoints hmid_le h2
    simp only [hk0, pow_zero, div_one, Nat.cast_zero, zero_mul, add_zero, zero_add,
      Nat.cast_one, one_mul, add_tsub_cancel_of_le hab]
    exact he2.trans he1
  | succ r =>
    have hsub_left : mid - a = (b - a) / 2 := add_tsub_cancel_left a ((b - a) / 2)
    have hsub_right : b - mid = (b - a) / 2 := by
      ext
      have hmid_le : mid ≤ b := by
        change (a : ℝ) + ((b - a : ℝ≥0) : ℝ) / 2 ≤ (b : ℝ)
        rw [NNReal.coe_sub hab]; linarith
      rw [NNReal.coe_sub hmid_le]
      change (b : ℝ) - ((a : ℝ) + ((b - a : ℝ≥0) : ℝ) / 2) = ((b - a : ℝ≥0) : ℝ) / 2
      rw [NNReal.coe_sub hab]; ring
    by_cases hlt : k.1 < 2 ^ r
    · have hstep := h1 r ⟨k.1, hlt⟩
      have harg : ∀ j : ℕ,
          a + (j : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ (r + 1)) =
            a + (j : ℝ≥0) * (mid - a) / ((2 : ℝ≥0) ^ r) := fun j => by
        rw [hsub_left, pow_succ]
        ext; push_cast; ring
      rw [harg (k.1 + 1), harg k.1]
      exact hstep
    · have hge : 2 ^ r ≤ k.1 := le_of_not_gt hlt
      have hk_sub : k.1 - 2 ^ r < 2 ^ r := by
        have hk2 : k.1 < 2 * 2 ^ r := by simpa [pow_succ'] using k.2
        omega
      have hstep := h2 r ⟨k.1 - 2 ^ r, hk_sub⟩
      have harg : ∀ j : ℕ, 2 ^ r ≤ j →
          a + (j : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ (r + 1)) =
            mid + ((j - 2 ^ r : ℕ) : ℝ≥0) * (b - mid) / ((2 : ℝ≥0) ^ r) := fun j hj => by
        rw [hsub_right, pow_succ]
        ext
        have hjcast : ((j - 2 ^ r : ℕ) : ℝ) = (j : ℝ) - (2 : ℝ) ^ r := by
          rw [Nat.cast_sub hj]; push_cast; rfl
        change (a : ℝ) + (j : ℝ) * ((b - a : ℝ≥0) : ℝ) / ((2 : ℝ) ^ r * 2) =
          (a : ℝ) + ((b - a : ℝ≥0) : ℝ) / 2 + ((j - 2 ^ r : ℕ) : ℝ) * (((b - a : ℝ≥0) : ℝ) / 2) / (2 : ℝ) ^ r
        rw [hjcast]
        have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
        field_simp [h2r]; ring
      have hsub_succ : k.1 + 1 - 2 ^ r = (k.1 - 2 ^ r) + 1 := by omega
      rw [harg (k.1 + 1) (by omega), harg k.1 hge, hsub_succ]
      exact hstep

open Classical in
/-- Deterministic lemma: if `f` is right-continuous and on `[a, b]` (`a < b`) the count of bad
dyadic subintervals is bounded by `1` at every dyadic refinement level, then `f` is constant on
`[a, τ)` and on `[τ, b]` for some `τ ∈ [a, b]`. -/
private lemma piecewiseConst_of_atMostOne_bad {f : ℝ≥0 → ℝ}
    (hrc : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    {a b : ℝ≥0} (hab : a < b)
    (hbad : ∀ r : ℕ,
      (Finset.univ.filter fun k : Fin (2 ^ r) =>
        ¬ ConstDyad f (a + (k.1 : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r))
            (a + ((k.1 + 1 : ℕ) : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r))).card ≤ 1) :
    ∃ τ ∈ Set.Icc a b,
      (∀ u ∈ Set.Ico a τ, f u = f a) ∧
      (∀ u ∈ Set.Ico τ b, f u = f b) := by
  let pt : ℕ → ℕ → ℝ≥0 := fun r k => a + (k : ℝ≥0) * (b - a) / ((2 : ℝ≥0) ^ r)
  have hpt_mono : ∀ r {i j : ℕ}, i ≤ j → pt r i ≤ pt r j := fun r i j hij => by
    dsimp only [pt]; gcongr
  have hpt_double : ∀ r k : ℕ, pt (r + 1) (2 * k) = pt r k := fun r k => by
    ext; dsimp only [pt]; push_cast [pow_succ]; ring
  have hpt_mid : ∀ r k : ℕ, pt (r + 1) (2 * k + 1) = pt r k + (pt r (k + 1) - pt r k) / 2 := fun r k => by
    ext
    have hle : pt r k ≤ pt r (k + 1) := hpt_mono r (Nat.le_succ k)
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hle, pt, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    push_cast [pow_succ]
    have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
    field_simp [h2r]; ring
  have hpt_end : ∀ r : ℕ, pt r (2 ^ r) = b := fun r => by
    ext; dsimp only [pt]
    have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
    rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hab.le]
    push_cast; field_simp [h2r]; ring
  by_cases hgood0 : ConstDyad f a b
  · refine ⟨b, ⟨hab.le, le_rfl⟩, fun u hu => constDyad_Icc_const hrc hab.le hgood0 u ⟨hu.1, hu.2.le⟩,
      fun u hu => absurd hu.2 (not_lt_of_ge hu.1)⟩
  · -- At every level `r`, there is a unique bad index `idx r < 2^r`
    have hex_bad : ∀ r : ℕ, ∃ k : Fin (2 ^ r), ¬ ConstDyad f (pt r k.1) (pt r (k.1 + 1)) := by
      intro r
      induction r with
      | zero =>
        refine ⟨⟨0, by norm_num⟩, ?_⟩
        simpa [pt, add_tsub_cancel_of_le hab.le] using hgood0
      | succ r ih =>
        obtain ⟨k, hk⟩ := ih
        have hle : pt r k.1 ≤ pt r (k.1 + 1) := hpt_mono r (Nat.le_succ k.1)
        by_contra hall
        push Not at hall
        have h1 : ConstDyad f (pt r k.1) (pt (r + 1) (2 * k.1 + 1)) := by
          rw [← hpt_double r k.1]
          exact hall ⟨2 * k.1, by rw [pow_succ']; omega⟩
        have h2 : ConstDyad f (pt (r + 1) (2 * k.1 + 1)) (pt r (k.1 + 1)) := by
          have heq : pt r (k.1 + 1) = pt (r + 1) (2 * k.1 + 1 + 1) := by
            rw [show 2 * k.1 + 1 + 1 = 2 * (k.1 + 1) by omega, hpt_double]
          rw [heq]
          exact hall ⟨2 * k.1 + 1, by rw [pow_succ']; omega⟩
        rw [hpt_mid r k.1] at h1 h2
        exact hk (constDyad_join hle h1 h2)
    choose idx hidx using hex_bad
    have huniq : ∀ (r : ℕ) (j : Fin (2 ^ r)), j ≠ idx r → ConstDyad f (pt r j.1) (pt r (j.1 + 1)) := by
      intro r j hne
      by_contra hnb
      let S := Finset.univ.filter fun k : Fin (2 ^ r) => ¬ ConstDyad f (pt r k.1) (pt r (k.1 + 1))
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnb⟩
      have hiS : idx r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ (idx r), hidx r⟩
      have hcard2 : 2 ≤ S.card := by
        have hsub : ({j, idx r} : Finset (Fin (2 ^ r))) ⊆ S := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have h2 : ({j, idx r} : Finset (Fin (2 ^ r))).card = 2 := Finset.card_pair hne
        have hle := Finset.card_le_card hsub
        omega
      exact absurd (hbad r) (not_le_of_gt (lt_of_lt_of_le (by norm_num) hcard2))
    -- Nestedness: `idx (r + 1)` is either `2 * idx r` or `2 * idx r + 1`
    have hchild : ∀ r : ℕ, (idx (r + 1)).1 = 2 * (idx r).1 ∨ (idx (r + 1)).1 = 2 * (idx r).1 + 1 := by
      intro r
      have hle : pt r (idx r).1 ≤ pt r ((idx r).1 + 1) := hpt_mono r (Nat.le_succ _)
      by_contra hneither
      push Not at hneither
      have h1 : ConstDyad f (pt r (idx r).1) (pt (r + 1) (2 * (idx r).1 + 1)) := by
        rw [← hpt_double r (idx r).1]
        exact huniq (r + 1) ⟨2 * (idx r).1, by rw [pow_succ']; omega⟩ (by intro heq; exact hneither.1 (by rw [← heq]))
      have h2 : ConstDyad f (pt (r + 1) (2 * (idx r).1 + 1)) (pt r ((idx r).1 + 1)) := by
        have heq : pt r ((idx r).1 + 1) = pt (r + 1) (2 * (idx r).1 + 1 + 1) := by
          rw [show 2 * (idx r).1 + 1 + 1 = 2 * ((idx r).1 + 1) by omega, hpt_double]
        rw [heq]
        exact huniq (r + 1) ⟨2 * (idx r).1 + 1, by rw [pow_succ']; omega⟩ (by intro heq; exact hneither.2 (by rw [← heq]))
      rw [hpt_mid r (idx r).1] at h1 h2
      exact hidx r (constDyad_join hle h1 h2)
    let L : ℕ → ℝ≥0 := fun r => pt r (idx r).1
    let R : ℕ → ℝ≥0 := fun r => pt r ((idx r).1 + 1)
    have hLR_le : ∀ r, L r ≤ R r := fun r => hpt_mono r (Nat.le_succ _)
    have hL_mono : Monotone L := monotone_nat_of_le_succ fun r => by
      dsimp only [L]
      rcases hchild r with h | h
      · rw [h, hpt_double]
      · rw [h, ← hpt_double r (idx r).1]; exact hpt_mono (r + 1) (Nat.le_succ _)
    have hR_anti : Antitone R := antitone_nat_of_succ_le fun r => by
      dsimp only [R]
      rcases hchild r with h | h
      · rw [h, show pt r ((idx r).1 + 1) = pt (r + 1) (2 * ((idx r).1 + 1)) from (hpt_double r _).symm]
        exact hpt_mono (r + 1) (by omega)
      · rw [h, show 2 * (idx r).1 + 1 + 1 = 2 * ((idx r).1 + 1) by omega, hpt_double]
    have hL_ge_a : ∀ r, a ≤ L r := fun r => by dsimp only [L, pt]; exact le_self_add
    have hR_le_b : ∀ r, R r ≤ b := fun r => by
      dsimp only [R]
      rw [← hpt_end r]
      exact hpt_mono r (Nat.succ_le_of_lt (idx r).2)
    have hL_const : ∀ r, ∀ u ∈ Set.Icc a (L r), f u = f a := by
      intro r
      induction r with
      | zero =>
        have h0 : (idx 0).1 = 0 := by omega
        intro u hu
        have hua : u = a := le_antisymm (by simpa [L, pt, h0] using hu.2) hu.1
        rw [hua]
      | succ r ih =>
        intro u hu
        rcases hchild r with h | h
        · have hLeq : L (r + 1) = L r := by dsimp only [L]; rw [h, hpt_double]
          exact ih u ⟨hu.1, hLeq ▸ hu.2⟩
        · have hLeq : L (r + 1) = pt (r + 1) (2 * (idx r).1 + 1) := by dsimp only [L]; rw [h]
          by_cases huL : u ≤ L r
          · exact ih u ⟨hu.1, huL⟩
          · have hgood_left : ConstDyad f (L r) (L (r + 1)) := by
              rw [hLeq]
              have hLr : L r = pt (r + 1) (2 * (idx r).1) := by dsimp only [L]; rw [hpt_double]
              rw [hLr]
              exact huniq (r + 1) ⟨2 * (idx r).1, by rw [pow_succ']; omega⟩
                (by
                  intro heq
                  have hval : (idx (r + 1)).1 = 2 * (idx r).1 := by rw [← heq]
                  omega)
            have h1 := constDyad_Icc_const hrc (hL_mono (Nat.le_succ r)) hgood_left u
              ⟨le_of_not_ge huL, hu.2⟩
            have h2 := ih (L r) ⟨hL_ge_a r, le_rfl⟩
            exact h1.trans h2
    have hR_const : ∀ r, ∀ u ∈ Set.Icc (R r) b, f u = f b := by
      intro r
      induction r with
      | zero =>
        have h0 : (idx 0).1 = 0 := by omega
        intro u hu
        have hub : u = b := le_antisymm hu.2 (by simpa [R, pt, h0, add_tsub_cancel_of_le hab.le] using hu.1)
        rw [hub]
      | succ r ih =>
        intro u hu
        rcases hchild r with h | h
        · have hReq : R (r + 1) = pt (r + 1) (2 * (idx r).1 + 1) := by dsimp only [R]; rw [h]
          by_cases huR : R r ≤ u
          · exact ih u ⟨huR, hu.2⟩
          · have hgood_right : ConstDyad f (R (r + 1)) (R r) := by
              rw [hReq]
              have hRr : R r = pt (r + 1) (2 * (idx r).1 + 1 + 1) := by
                dsimp only [R]; rw [show 2 * (idx r).1 + 1 + 1 = 2 * ((idx r).1 + 1) by omega, hpt_double]
              rw [hRr]
              exact huniq (r + 1) ⟨2 * (idx r).1 + 1, by rw [pow_succ']; omega⟩
                (by
                  intro heq
                  have hval : (idx (r + 1)).1 = 2 * (idx r).1 + 1 := by rw [← heq]
                  omega)
            have h1 := constDyad_Icc_const hrc (hR_anti (Nat.le_succ r)) hgood_right u
              ⟨hu.1, le_of_not_ge huR⟩
            have h2 := constDyad_endpoints (hR_anti (Nat.le_succ r)) hgood_right
            have h3 := ih (R r) ⟨le_rfl, hR_le_b r⟩
            exact h1.trans (h2.symm.trans h3)
        · have hReq : R (r + 1) = R r := by
            dsimp only [R]; rw [h, show 2 * (idx r).1 + 1 + 1 = 2 * ((idx r).1 + 1) by omega, hpt_double]
          exact ih u ⟨hReq ▸ hu.1, hu.2⟩
    let τ : ℝ≥0 := ⨆ r : ℕ, L r
    have hL_bdd : BddAbove (Set.range L) := ⟨b, by rintro _ ⟨r, rfl⟩; exact (hLR_le r).trans (hR_le_b r)⟩
    have hL_le_τ : ∀ r, L r ≤ τ := fun r => le_ciSup hL_bdd r
    have hτ_ge_a : a ≤ τ := (hL_ge_a 0).trans (hL_le_τ 0)
    have hτ_le_R : ∀ r, τ ≤ R r := fun r =>
      ciSup_le fun s => by
        rcases le_total s r with hsr | hrs
        · exact (hL_mono hsr).trans (hLR_le r)
        · exact (hLR_le s).trans (hR_anti hrs)
    have hτ_le_b : τ ≤ b := (hτ_le_R 0).trans (hR_le_b 0)
    have hgap : ∀ r, (R r : ℝ) - (L r : ℝ) = ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r := fun r => by
      dsimp only [L, R, pt]
      rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_div, NNReal.coe_div,
        NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_sub hab.le]
      push_cast; ring
    have hR_tend : Tendsto R atTop (nhds τ) := by
      rw [← NNReal.tendsto_coe]
      have hgeom : Tendsto (fun r : ℕ => ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r) atTop (nhds 0) := by
        have h1 : Tendsto (fun r : ℕ => (1 / 2 : ℝ) ^ r) atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa [div_eq_mul_inv, one_div, inv_pow] using h1.const_mul ((b : ℝ) - (a : ℝ))
      have hhi : Tendsto (fun r : ℕ => (τ : ℝ) + ((b : ℝ) - (a : ℝ)) / (2 : ℝ) ^ r) atTop (nhds (τ : ℝ)) := by
        simpa using (tendsto_const_nhds (x := (τ : ℝ))).add hgeom
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi
        (fun r => by exact_mod_cast hτ_le_R r) (fun r => ?_)
      have h1 : (L r : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hL_le_τ r
      linarith [hgap r]
    refine ⟨τ, ⟨hτ_ge_a, hτ_le_b⟩, ?_, ?_⟩
    · intro u hu
      obtain ⟨r, hur⟩ := (lt_ciSup_iff hL_bdd).mp hu.2
      exact hL_const r u ⟨hu.1, hur.le⟩
    · intro u hu
      rcases eq_or_lt_of_le hu.1 with hτu_eq | hτu
      · rw [← hτu_eq]
        have hR_within : Tendsto R atTop (nhdsWithin τ (Set.Ici τ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hR_tend (Eventually.of_forall hτ_le_R)
        have hlim : Tendsto (fun r => f (R r)) atTop (nhds (f τ)) := (hrc τ).tendsto.comp hR_within
        have hconst : (fun r => f (R r)) = fun _ => f b := funext fun r => hR_const r (R r) ⟨le_rfl, hR_le_b r⟩
        rw [hconst] at hlim
        exact tendsto_nhds_unique hlim tendsto_const_nhds
      · obtain ⟨r, hr⟩ := (hR_tend.eventually (gt_mem_nhds hτu)).exists
        exact hR_const r u ⟨hr.le, hu.2.le⟩

private lemma nnreal_grid_step_le (K k m : ℕ) :
    (K : ℝ≥0) + (k : ℝ≥0) / ((2 : ℝ≥0) ^ m) ≤
      (K : ℝ≥0) + ((k + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m) := by
  change (K : ℝ) + (k : ℝ) / (2 : ℝ) ^ m ≤ (K : ℝ) + ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m
  gcongr
  exact_mod_cast Nat.le_succ k

open Classical in
/-- Deterministic lemma: if `f` is right-continuous and on every unit interval `[K, K + 1]` the
bad dyadic count is bounded uniformly over all refinement levels, then `t ↦ f t + d * t` is
`piecewiseLinear`. -/
private lemma piecewiseLinear_of_bounded_unit_bad {f : ℝ≥0 → ℝ} (d : ℝ)
    (hrc : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    (hunit : ∀ K : ℕ, ∃ M : ℕ, ∀ m : ℕ,
      (Finset.univ.filter fun k : Fin (2 ^ m) =>
        ¬ ConstDyad f ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))).card ≤ M) :
    piecewiseLinear (fun t => f t + d * (t : ℝ)) := by
  -- On each `[K, K + 1)`, find a finite set `S K ⊆ [K, K + 1)` containing `K` such that `f` is
  -- constant between any two consecutive points of `S K ∪ {K + 1}`
  have hunit_fin : ∀ K : ℕ, ∃ S : Finset ℝ≥0,
      (K : ℝ≥0) ∈ S ∧
      (∀ x ∈ S, (K : ℝ≥0) ≤ x ∧ x < ((K + 1 : ℕ) : ℝ≥0)) ∧
      (∀ (u v : ℝ≥0), u ∈ insert ((K + 1 : ℕ) : ℝ≥0) S → v ∈ insert ((K + 1 : ℕ) : ℝ≥0) S →
        u < v → (∀ w ∈ S, ¬ (u < w ∧ w < v)) → ∀ t : ℝ≥0, u ≤ t → t < v → f t = f u) := by
    intro K
    obtain ⟨M, hM⟩ := hunit K
    let cnt : ℕ → ℕ := fun m =>
      (Finset.univ.filter fun k : Fin (2 ^ m) =>
        ¬ ConstDyad f ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))).card
    -- `cnt` is monotone and bounded by `M`, so it achieves its maximum at some `m₀`
    have hcnt_mono : Monotone cnt := monotone_nat_of_le_succ fun m => by
      dsimp only [cnt]
      let B₀ := Finset.univ.filter fun k : Fin (2 ^ m) =>
        ¬ ConstDyad f ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))
      let B₁ := Finset.univ.filter fun j : Fin (2 ^ (m + 1)) =>
        ¬ ConstDyad f ((K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)))
            ((K : ℝ≥0) + ((j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)))
      have hmap_ex : ∀ k ∈ B₀, ∃ j ∈ B₁, j.1 / 2 = k.1 := by
        intro k hk
        have hkbad := (Finset.mem_filter.mp hk).2
        let a : ℝ≥0 := (K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m)
        let b : ℝ≥0 := (K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m)
        have hab : a ≤ b := nnreal_grid_step_le K k.1 m
        have hmid_eq : a + (b - a) / 2 = (K : ℝ≥0) + ((2 * k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
          ext; rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hab]; dsimp only [a, b]
          push_cast [pow_succ]
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m]; ring
        have ha_eq : a = (K : ℝ≥0) + ((2 * k.1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
          ext; dsimp only [a]; push_cast [pow_succ]
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m]
        have hb_eq : b = (K : ℝ≥0) + ((2 * k.1 + 1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
          ext; dsimp only [b]; push_cast [pow_succ]
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m]; ring
        by_contra hnone
        push Not at hnone
        have hj0 : ConstDyad f a (a + (b - a) / 2) := by
          rw [hmid_eq, ha_eq]
          have hmem := hnone ⟨2 * k.1, by rw [pow_succ']; omega⟩
          by_contra hnb
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb⟩) (by dsimp only; omega)
        have hj1 : ConstDyad f (a + (b - a) / 2) b := by
          rw [hmid_eq, hb_eq]
          have hmem := hnone ⟨2 * k.1 + 1, by rw [pow_succ']; omega⟩
          by_contra hnb
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb⟩) (by dsimp only; omega)
        exact hkbad (constDyad_join hab hj0 hj1)
      have hsub : B₀ ⊆ B₁.image (fun j : Fin (2 ^ (m + 1)) =>
          (⟨j.1 / 2, by
            have hj2 : j.1 < 2 * 2 ^ m := by simpa [pow_succ'] using j.2
            omega⟩ : Fin (2 ^ m))) := by
        intro k hk
        obtain ⟨j, hj, hdiv⟩ := hmap_ex k hk
        exact Finset.mem_image.mpr ⟨j, hj, Fin.ext hdiv⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    -- Find `m₀` achieving the maximum of `cnt`
    have hmax_ex : ∃ m₀ : ℕ, ∀ m ≥ m₀, cnt m = cnt m₀ := by
      have hne : (Set.range cnt).Nonempty := ⟨cnt 0, 0, rfl⟩
      have hbdd : BddAbove (Set.range cnt) := ⟨M, by rintro _ ⟨m, rfl⟩; exact hM m⟩
      obtain ⟨m₀, hm₀⟩ := Nat.sSup_mem hne hbdd
      refine ⟨m₀, fun m hm => le_antisymm ?_ (hcnt_mono hm)⟩
      rw [hm₀]
      exact le_csSup hbdd ⟨m, rfl⟩
    obtain ⟨m₀, hm₀⟩ := hmax_ex
    -- For each `k : Fin (2^{m₀})`, the interval `[a_k, b_k]` has at most 1 bad subinterval at every refinement level `r`
    let grid : Fin (2 ^ m₀) → ℝ≥0 := fun k => (K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m₀)
    let gridR : Fin (2 ^ m₀) → ℝ≥0 := fun k => (K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m₀)
    have hsub_atMostOne : ∀ k : Fin (2 ^ m₀), ∀ r : ℕ,
        (Finset.univ.filter fun j : Fin (2 ^ r) =>
          ¬ ConstDyad f (grid k + (j.1 : ℝ≥0) * (gridR k - grid k) / ((2 : ℝ≥0) ^ r))
              (grid k + ((j.1 + 1 : ℕ) : ℝ≥0) * (gridR k - grid k) / ((2 : ℝ≥0) ^ r))).card ≤ 1 := by
      intro k r
      -- Embed `j : Fin (2^r)` into `Fin (2^(m₀ + r))` as `k * 2^r + j`
      let m := m₀ + r
      let B₀ := Finset.univ.filter fun i : Fin (2 ^ m₀) => ¬ ConstDyad f (grid i) (gridR i)
      let B_m := Finset.univ.filter fun i : Fin (2 ^ m) =>
        ¬ ConstDyad f ((K : ℝ≥0) + (i.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((i.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))
      let proj : Fin (2 ^ m) → Fin (2 ^ m₀) := fun i =>
        ⟨i.1 / 2 ^ r, by
          have hi : i.1 < 2 ^ m₀ * 2 ^ r := by simpa [m, pow_add] using i.2
          exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
      -- Every `i ∈ B₀` has at least one preimage in `B_m`
      have hsurj : ∀ i ∈ B₀, ∃ j ∈ B_m, proj j = i := by
        have hstep : ∀ s : ℕ, ∀ i : Fin (2 ^ m₀), ¬ ConstDyad f (grid i) (gridR i) →
            ∃ j : Fin (2 ^ (m₀ + s)),
              ¬ ConstDyad f ((K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + s)))
                  ((K : ℝ≥0) + ((j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + s))) ∧
              j.1 / 2 ^ s = i.1 := by
          intro s
          induction s with
          | zero =>
            intro i hi
            exact ⟨i, hi, by simp⟩
          | succ s ih =>
            intro i hi
            obtain ⟨j, hj, hdiv⟩ := ih i hi
            let a := (K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + s))
            let b := (K : ℝ≥0) + ((j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + s))
            have hab : a ≤ b := nnreal_grid_step_le K j.1 (m₀ + s)
            have hmid_eq : a + (b - a) / 2 =
                (K : ℝ≥0) + ((2 * j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + (s + 1))) := by
              ext; rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hab]; dsimp only [a, b]
              rw [show m₀ + (s + 1) = (m₀ + s) + 1 by omega]
              push_cast [pow_succ]
              have h2ms : (2 : ℝ) ^ (m₀ + s) ≠ 0 := by positivity
              field_simp [h2ms]; ring
            have ha_eq : a = (K : ℝ≥0) + ((2 * j.1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + (s + 1))) := by
              ext; dsimp only [a]; rw [show m₀ + (s + 1) = (m₀ + s) + 1 by omega]
              push_cast [pow_succ]
              have h2ms : (2 : ℝ) ^ (m₀ + s) ≠ 0 := by positivity
              field_simp [h2ms]
            have hb_eq : b = (K : ℝ≥0) + ((2 * j.1 + 1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m₀ + (s + 1))) := by
              ext; dsimp only [b]; rw [show m₀ + (s + 1) = (m₀ + s) + 1 by omega]
              push_cast [pow_succ]
              have h2ms : (2 : ℝ) ^ (m₀ + s) ≠ 0 := by positivity
              field_simp [h2ms]; ring
            by_cases hl : ¬ ConstDyad f a (a + (b - a) / 2)
            · refine ⟨⟨2 * j.1, by rw [show m₀ + (s + 1) = (m₀ + s) + 1 by omega, pow_succ']; omega⟩, ?_, ?_⟩
              · rwa [← hmid_eq, ← ha_eq]
              · dsimp only
                rw [pow_succ', ← Nat.div_div_eq_div_mul]
                simpa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] using hdiv
            · push Not at hl
              have hr : ¬ ConstDyad f (a + (b - a) / 2) b := fun hr' => hj (constDyad_join hab hl hr')
              refine ⟨⟨2 * j.1 + 1, by rw [show m₀ + (s + 1) = (m₀ + s) + 1 by omega, pow_succ']; omega⟩, ?_, ?_⟩
              · rwa [← hmid_eq, ← hb_eq]
              · dsimp only
                rw [pow_succ', ← Nat.div_div_eq_div_mul]
                have : (2 * j.1 + 1) / 2 = j.1 := by omega
                rwa [this]
        intro i hi
        obtain ⟨j, hj, hdiv⟩ := hstep r i (Finset.mem_filter.mp hi).2
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, Fin.ext hdiv⟩
      -- Also every `j ∈ B_m` projects into `B₀`
      have hmaps : ∀ j ∈ B_m, proj j ∈ B₀ := by
        intro j hj
        by_contra hnot
        have hgood : ConstDyad f (grid (proj j)) (gridR (proj j)) := by
          by_contra hnb; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb⟩)
        -- If `ConstDyad` holds on `[grid (proj j), gridR (proj j)]`, it holds on every dyadic subinterval of level `r`
        have hjbad := (Finset.mem_filter.mp hj).2
        apply hjbad
        intro s t
        have hrem : j.1 = (proj j).1 * 2 ^ r + j.1 % 2 ^ r := by
          dsimp only [proj]; rw [mul_comm, Nat.div_add_mod]
        have hsub : ∀ u : ℕ,
            (K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m) +
              (u : ℝ≥0) * (((K : ℝ≥0) + ((j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m)) -
                ((K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))) / ((2 : ℝ≥0) ^ s) =
            grid (proj j) +
              (((j.1 % 2 ^ r) * 2 ^ s + u : ℕ) : ℝ≥0) * (gridR (proj j) - grid (proj j)) / ((2 : ℝ≥0) ^ (r + s)) := by
          intro u
          ext
          have hle1 : (K : ℝ≥0) + (j.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m) ≤
              (K : ℝ≥0) + ((j.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m) := nnreal_grid_step_le K j.1 m
          have hle2 : grid (proj j) ≤ gridR (proj j) := nnreal_grid_step_le K (proj j).1 m₀
          simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hle1,
            NNReal.coe_sub hle2, grid, gridR, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
          have hjcast : (j.1 : ℝ) = ((proj j).1 : ℝ) * (2 : ℝ) ^ r + (j.1 % 2 ^ r : ℕ) := by
            exact_mod_cast hrem
          push_cast [m, pow_add]
          rw [hjcast]
          have h2m0 : (2 : ℝ) ^ m₀ ≠ 0 := by positivity
          have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
          have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
          field_simp [h2m0, h2r, h2s]; ring
        have hlt_rs : (j.1 % 2 ^ r) * 2 ^ s + t.1 < 2 ^ (r + s) := by
          have h1 : j.1 % 2 ^ r < 2 ^ r := Nat.mod_lt _ (by positivity)
          have h2 : t.1 < 2 ^ s := t.2
          have hpow : 2 ^ (r + s) = 2 ^ r * 2 ^ s := pow_add 2 r s
          nlinarith
        have hstep := hgood (r + s) ⟨(j.1 % 2 ^ r) * 2 ^ s + t.1, hlt_rs⟩
        rw [hsub (t.1 + 1), hsub t.1]
        simpa [Nat.add_assoc] using hstep
      -- Since `B_m.card = cnt m = cnt m₀ = B₀.card` and `proj` maps `B_m` surjectively onto `B₀`,
      -- `proj` is injective on `B_m`, so the fiber over `k` has card ≤ 1!
      have hcard_eq : B_m.card = B₀.card := hm₀ m (Nat.le_add_right m₀ r)
      have himg_eq : B_m.image proj = B₀ := by
        apply Finset.Subset.antisymm
        · intro i hi; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi; exact hmaps j hj
        · intro i hi; obtain ⟨j, hj, rfl⟩ := hsurj i hi; exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have hinj : Set.InjOn proj (B_m : Set (Fin (2 ^ m))) := by
        have hcard_img : (B_m.image proj).card = B_m.card := by rw [himg_eq, hcard_eq]
        exact Finset.injOn_of_card_image_eq hcard_img
      -- Embed the filter on `Fin (2^r)` injectively into the fiber `B_m.filter (fun i => proj i = k)`
      let F := Finset.univ.filter fun j : Fin (2 ^ r) =>
        ¬ ConstDyad f (grid k + (j.1 : ℝ≥0) * (gridR k - grid k) / ((2 : ℝ≥0) ^ r))
            (grid k + ((j.1 + 1 : ℕ) : ℝ≥0) * (gridR k - grid k) / ((2 : ℝ≥0) ^ r))
      by_contra hgt1
      have h2 : 1 < F.card := lt_of_not_ge hgt1
      obtain ⟨j₁, hj₁, j₂, hj₂, hjne⟩ := Finset.one_lt_card.mp h2
      let emb : Fin (2 ^ r) → Fin (2 ^ m) := fun j =>
        ⟨k.1 * 2 ^ r + j.1, by
          have hk1 : k.1 + 1 ≤ 2 ^ m₀ := k.2
          have hj1 : j.1 < 2 ^ r := j.2
          rw [show m = m₀ + r from rfl, pow_add]
          have : (k.1 + 1) * 2 ^ r ≤ 2 ^ m₀ * 2 ^ r := Nat.mul_le_mul_right _ hk1
          linarith [Nat.add_mul k.1 1 (2 ^ r)]⟩
      have hemb_proj : ∀ j : Fin (2 ^ r), proj (emb j) = k := fun j => by
        apply Fin.ext
        dsimp only [proj, emb]
        rw [mul_comm k.1 (2 ^ r), Nat.mul_add_div (by positivity : 0 < 2 ^ r),
          Nat.div_eq_of_lt j.2, add_zero]
      have hemb_pt : ∀ (j : Fin (2 ^ r)) (u : ℕ),
          grid k + (u : ℝ≥0) * (gridR k - grid k) / ((2 : ℝ≥0) ^ r) =
            (K : ℝ≥0) + ((k.1 * 2 ^ r + u : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m) := fun j u => by
        ext
        have hle : grid k ≤ gridR k := nnreal_grid_step_le K k.1 m₀
        simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hle,
          grid, gridR, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
        push_cast [m, pow_add]
        have h2m0 : (2 : ℝ) ^ m₀ ≠ 0 := by positivity
        have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
        field_simp [h2m0, h2r]; ring
      have hemb_mem : ∀ j ∈ F, emb j ∈ B_m := fun j hj => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hjbad := (Finset.mem_filter.mp hj).2
        have h1 := hemb_pt j j.1
        have h2 := hemb_pt j (j.1 + 1)
        rw [h1, h2] at hjbad
        simpa [emb, Nat.add_assoc] using hjbad
      have heq_emb : emb j₁ = emb j₂ := hinj (hemb_mem j₁ hj₁) (hemb_mem j₂ hj₂)
        ((hemb_proj j₁).trans (hemb_proj j₂).symm)
      have : j₁.1 = j₂.1 := by
        have := congrArg Fin.val heq_emb
        dsimp only [emb] at this; omega
      exact hjne (Fin.ext this)
    -- For each `k : Fin (2^{m₀})`, get its breakpoint `τ k ∈ [grid k, gridR k]`
    have hbp : ∀ k : Fin (2 ^ m₀), ∃ τ ∈ Set.Icc (grid k) (gridR k),
        (∀ u ∈ Set.Ico (grid k) τ, f u = f (grid k)) ∧
        (∀ u ∈ Set.Ico τ (gridR k), f u = f (gridR k)) := fun k => by
      have hlt : grid k < gridR k := by
        change (K : ℝ) + (k.1 : ℝ) / (2 : ℝ) ^ m₀ < (K : ℝ) + ((k.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m₀
        have : (0 : ℝ) < (2 : ℝ) ^ m₀ := by positivity
        push_cast; linarith [div_lt_div_of_pos_right (show (k.1 : ℝ) < (k.1 : ℝ) + 1 by linarith) this]
      exact piecewiseConst_of_atMostOne_bad hrc hlt (hsub_atMostOne k)
    choose τ hτ_mem hτ_left hτ_right using hbp
    let S : Finset ℝ≥0 :=
      (Finset.univ.image grid) ∪ ((Finset.univ.image τ).filter (fun x => x < ((K + 1 : ℕ) : ℝ≥0)))
    have hK_mem : (K : ℝ≥0) ∈ S := by
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨0, by positivity⟩, Finset.mem_univ _, ?_⟩)
      simp [grid]
    have hS_bounds : ∀ x ∈ S, (K : ℝ≥0) ≤ x ∧ x < ((K + 1 : ℕ) : ℝ≥0) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx1
        refine ⟨by dsimp only [grid]; exact le_self_add, ?_⟩
        change (K : ℝ) + (k.1 : ℝ) / (2 : ℝ) ^ m₀ < ((K + 1 : ℕ) : ℝ)
        have hlt1 : (k.1 : ℝ) / (2 : ℝ) ^ m₀ < 1 := by
          rw [div_lt_one (by positivity)]; exact_mod_cast k.2
        push_cast; linarith
      · rw [Finset.mem_filter] at hx2
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx2.1
        refine ⟨?_, hx2.2⟩
        have h1 : (K : ℝ≥0) ≤ grid k := by dsimp only [grid]; exact le_self_add
        exact h1.trans (hτ_mem k).1
    refine ⟨S, hK_mem, hS_bounds, ?_⟩
    intro u v hu hv huv hno t htu htv
    -- Find the grid cell `k : Fin (2^{m₀})` containing `u`
    have hu_bounds : (K : ℝ≥0) ≤ u ∧ u < ((K + 1 : ℕ) : ℝ≥0) := by
      rcases Finset.mem_insert.mp hu with rfl | huS
      · exfalso
        rcases Finset.mem_insert.mp hv with rfl | hvS
        · exact lt_irrefl _ huv
        · exact not_lt_of_ge (hS_bounds v hvS).2.le huv
      · exact hS_bounds u huS
    let k₀_nat : ℕ := ⌊((u : ℝ) - (K : ℝ)) * (2 : ℝ) ^ m₀⌋₊
    have hk₀_lt : k₀_nat < 2 ^ m₀ := by
      have h1 : (u : ℝ) - (K : ℝ) < 1 := by
        have : (u : ℝ) < ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hu_bounds.2
        push_cast at this; linarith
      have hmul : ((u : ℝ) - (K : ℝ)) * (2 : ℝ) ^ m₀ < ((2 ^ m₀ : ℕ) : ℝ) := by
        push_cast; linarith [mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < (2 : ℝ) ^ m₀)]
      exact (Nat.floor_lt (mul_nonneg (by
        have hKu : (K : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_bounds.1
        linarith) (by positivity))).mpr hmul
    let k₀ : Fin (2 ^ m₀) := ⟨k₀_nat, hk₀_lt⟩
    have hgrid_le_u : grid k₀ ≤ u := by
      change (K : ℝ) + (k₀_nat : ℝ) / (2 : ℝ) ^ m₀ ≤ (u : ℝ)
      have hnn : 0 ≤ ((u : ℝ) - (K : ℝ)) * (2 : ℝ) ^ m₀ :=
        mul_nonneg (by
          have hKu : (K : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_bounds.1
          linarith) (by positivity)
      have hfl : (k₀_nat : ℝ) ≤ ((u : ℝ) - (K : ℝ)) * (2 : ℝ) ^ m₀ := Nat.floor_le hnn
      have hdiv : (k₀_nat : ℝ) / (2 : ℝ) ^ m₀ ≤ (u : ℝ) - (K : ℝ) :=
        (div_le_iff₀ (by positivity)).mpr hfl
      linarith
    have hu_lt_gridR : u < gridR k₀ := by
      change (u : ℝ) < (K : ℝ) + ((k₀_nat + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m₀
      have hfl : ((u : ℝ) - (K : ℝ)) * (2 : ℝ) ^ m₀ < (k₀_nat : ℝ) + 1 := Nat.lt_floor_add_one _
      have hdiv : (u : ℝ) - (K : ℝ) < ((k₀_nat : ℝ) + 1) / (2 : ℝ) ^ m₀ :=
        (lt_div_iff₀ (by positivity)).mpr hfl
      push_cast; linarith
    -- Show `v ≤ gridR k₀` (since otherwise `gridR k₀ ∈ S` would lie strictly between `u` and `v`, or `gridR k₀ = K + 1 ≥ v`)
    have hv_le_gridR : v ≤ gridR k₀ := by
      by_cases htop : k₀.1 + 1 = 2 ^ m₀
      · have heq : gridR k₀ = ((K + 1 : ℕ) : ℝ≥0) := by
          ext; dsimp only [gridR]; rw [htop]; push_cast
          have h2 : (2 : ℝ) ^ m₀ ≠ 0 := by positivity
          field_simp [h2]
        rw [heq]
        rcases Finset.mem_insert.mp hv with rfl | hvS
        · exact le_rfl
        · exact (hS_bounds v hvS).2.le
      · have hlt_next : k₀.1 + 1 < 2 ^ m₀ := by omega
        have hmem_next : gridR k₀ ∈ S := by
          refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨k₀.1 + 1, hlt_next⟩, Finset.mem_univ _, rfl⟩)
        by_contra hgt
        push Not at hgt
        exact hno (gridR k₀) hmem_next ⟨hu_lt_gridR, hgt⟩
    -- Now compare `τ k₀` with `[u, v)`: `τ k₀` cannot lie strictly between `u` and `v`!
    by_cases hv_le_τ : v ≤ τ k₀
    · have h1 := hτ_left k₀ t ⟨hgrid_le_u.trans htu, htv.trans_le hv_le_τ⟩
      have h2 := hτ_left k₀ u ⟨hgrid_le_u, huv.trans_le hv_le_τ⟩
      exact h1.trans h2.symm
    · have hτ_lt_v : τ k₀ < v := lt_of_not_ge hv_le_τ
      have hτ_le_u : τ k₀ ≤ u := by
        by_contra hu_lt_τ
        push Not at hu_lt_τ
        have hτ_lt_K1 : τ k₀ < ((K + 1 : ℕ) : ℝ≥0) := by
          rcases Finset.mem_insert.mp hv with rfl | hvS
          · exact hτ_lt_v
          · exact hτ_lt_v.trans (hS_bounds v hvS).2
        have hτ_mem_S : τ k₀ ∈ S :=
          Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k₀, Finset.mem_univ _, rfl⟩, hτ_lt_K1⟩)
        exact hno (τ k₀) hτ_mem_S ⟨hu_lt_τ, hτ_lt_v⟩
      have h1 := hτ_right k₀ t ⟨hτ_le_u.trans htu, htv.trans_le hv_le_gridR⟩
      have h2 := hτ_right k₀ u ⟨hτ_le_u, huv.trans_le hv_le_gridR⟩
      exact h1.trans h2.symm
  -- Concatenate the sorted finite breakpoint sets `S 0, S 1, S 2, ...` into `T : ℕ → ℝ≥0`
  choose S hK_mem hS_bounds hS_const using hunit_fin
  let L : ℕ → List ℝ≥0 := fun K => (S K).sort (· ≤ ·)
  have hL_len_pos : ∀ K, 0 < (L K).length := fun K => by
    have hne : (S K).Nonempty := ⟨(K : ℝ≥0), hK_mem K⟩
    have := (S K).length_sort (· ≤ ·)
    exact this ▸ hne.card_pos
  have hL_sorted : ∀ K, (L K).Pairwise (· < ·) := fun K =>
    (((S K).pairwise_sort (· ≤ ·)).and ((S K).sort_nodup (· ≤ ·))).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hL_mem : ∀ K x, x ∈ L K ↔ x ∈ S K := fun K x => Finset.mem_sort _
  -- Prefix sums of block lengths
  let off : ℕ → ℕ := fun K => ∑ j ∈ Finset.range K, (L j).length
  have hoff_zero : off 0 = 0 := by simp [off]
  have hoff_succ : ∀ K, off (K + 1) = off K + (L K).length := fun K => Finset.sum_range_succ _ K
  have hoff_strictMono : StrictMono off := strictMono_nat_of_lt_succ fun K => by
    rw [hoff_succ]; exact Nat.lt_add_of_pos_right (hL_len_pos K)
  have hblock : ∀ n : ℕ, ∃ K : ℕ, off K ≤ n ∧ n < off (K + 1) := by
    intro n
    have hex : ∃ K : ℕ, n < off (K + 1) := by
      refine ⟨n, ?_⟩
      have hle : n + 1 ≤ off (n + 1) := hoff_strictMono.id_le (n + 1)
      omega
    have hK_lt : n < off (Nat.find hex + 1) := Nat.find_spec hex
    have hK_le : off (Nat.find hex) ≤ n := by
      cases hK : Nat.find hex with
      | zero => rw [hoff_zero]; exact Nat.zero_le n
      | succ K' =>
        have hnot := Nat.find_min hex (by rw [hK]; exact Nat.lt_succ_self K')
        exact le_of_not_gt hnot
    exact ⟨Nat.find hex, hK_le, hK_lt⟩
  choose blk hblk_le hblk_lt using hblock
  have hblk_uniq : ∀ {n K : ℕ}, off K ≤ n → n < off (K + 1) → blk n = K := by
    intro n K h1 h2
    have hbl := hblk_le n
    have hbr := hblk_lt n
    rcases lt_trichotomy (blk n) K with hlt | heq | hgt
    · have : off (blk n + 1) ≤ off K := hoff_strictMono.monotone (Nat.succ_le_of_lt hlt)
      omega
    · exact heq
    · have : off (K + 1) ≤ off (blk n) := hoff_strictMono.monotone (Nat.succ_le_of_lt hgt)
      omega
  have hsub_lt : ∀ n : ℕ, n - off (blk n) < (L (blk n)).length := fun n => by
    have h1 := hblk_le n
    have h2 := hblk_lt n
    rw [hoff_succ] at h2
    omega
  let T : ℕ → ℝ≥0 := fun n => (L (blk n))[n - off (blk n)]'(hsub_lt n)
  have hT_eq : ∀ {n K i : ℕ} (hi : i < (L K).length),
      blk n = K → n - off K = i → T n = (L K)[i] := by
    intro n K i hi hK hsub
    dsimp only [T]
    subst hK
    simp [hsub]
  have hT_mem : ∀ n : ℕ, T n ∈ S (blk n) := fun n =>
    (hL_mem _ _).mp (List.getElem_mem (hsub_lt n))
  have hT_bounds : ∀ n : ℕ, ((blk n : ℕ) : ℝ≥0) ≤ T n ∧ T n < (((blk n + 1 : ℕ) : ℝ≥0)) := fun n =>
    hS_bounds (blk n) (T n) (hT_mem n)
  have hL_head : ∀ K, (L K)[0]'(hL_len_pos K) = (K : ℝ≥0) := by
    intro K
    have hmem : (L K)[0]'(hL_len_pos K) ∈ S K := (hL_mem K _).mp (List.getElem_mem (hL_len_pos K))
    have hge : (K : ℝ≥0) ≤ (L K)[0]'(hL_len_pos K) := (hS_bounds K _ hmem).1
    have hle : (L K)[0]'(hL_len_pos K) ≤ (K : ℝ≥0) := by
      have hK_in : (K : ℝ≥0) ∈ L K := (hL_mem K _).mpr (hK_mem K)
      obtain ⟨j, hj_lt, hj⟩ := List.mem_iff_getElem.mp hK_in
      by_cases hj0 : j = 0
      · subst hj0; exact hj.le
      · have hlt := List.pairwise_iff_getElem.mp (hL_sorted K) 0 j (hL_len_pos K) hj_lt (by omega)
        rw [hj] at hlt; exact hlt.le
    exact le_antisymm hle hge
  have hT0 : T 0 = 0 := by
    have hb0 : blk 0 = 0 := hblk_uniq (by rw [hoff_zero]) (by rw [hoff_succ, hoff_zero, zero_add]; exact hL_len_pos 0)
    rw [hT_eq (hL_len_pos 0) hb0 (by simp [hoff_zero]), hL_head 0]; simp
  have hT_strictMono : StrictMono T := strictMono_nat_of_lt_succ fun n => by
    by_cases hsame : n + 1 < off (blk n + 1)
    · have hb1 : blk (n + 1) = blk n := hblk_uniq ((hblk_le n).trans (Nat.le_succ n)) hsame
      have h1_lt : n + 1 - off (blk n) < (L (blk n)).length := by
        have := hblk_le n; rw [hoff_succ] at hsame; omega
      rw [hT_eq (hsub_lt n) rfl rfl, hT_eq h1_lt hb1 rfl]
      exact List.pairwise_iff_getElem.mp (hL_sorted (blk n)) _ _ (hsub_lt n) h1_lt
        (by have := hblk_le n; omega)
    · have hge : off (blk n + 1) ≤ n + 1 := le_of_not_gt hsame
      have heq : n + 1 = off (blk n + 1) := le_antisymm (Nat.succ_le_of_lt (hblk_lt n)) hge
      have hb1 : blk (n + 1) = blk n + 1 :=
        hblk_uniq (heq ▸ le_rfl) (by rw [heq]; exact hoff_strictMono (Nat.lt_succ_self _))
      have h1 : T n < (((blk n + 1 : ℕ) : ℝ≥0)) := (hT_bounds n).2
      have h2 : (((blk n + 1 : ℕ) : ℝ≥0)) ≤ T (n + 1) := by rw [← hb1]; exact (hT_bounds (n + 1)).1
      exact h1.trans_le h2
  have hT_tendsto : Tendsto T atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro M
    let K : ℕ := ⌈(M : ℝ)⌉₊
    refine ⟨off K, fun n hn => ?_⟩
    have hK_le_blk : K ≤ blk n := by
      by_contra hlt
      push Not at hlt
      have : off (blk n + 1) ≤ off K := hoff_strictMono.monotone (Nat.succ_le_of_lt hlt)
      have := hblk_lt n; omega
    have h1 : M ≤ (K : ℝ≥0) := by exact_mod_cast Nat.le_ceil (M : ℝ)
    have h2 : (K : ℝ≥0) ≤ ((blk n : ℕ) : ℝ≥0) := by exact_mod_cast hK_le_blk
    exact (h1.trans h2).trans (hT_bounds n).1
  refine ⟨T, hT0, hT_strictMono, hT_tendsto, fun n => ⟨d, f (T n), fun t htn htn1 => ?_⟩⟩
  -- Show `f t = f (T n)` on `[T n, T (n + 1))` using `hS_const (blk n)`
  let K := blk n
  have hu_mem : T n ∈ insert ((K + 1 : ℕ) : ℝ≥0) (S K) := Finset.mem_insert_of_mem (hT_mem n)
  have hconst_n : f t = f (T n) := by
    by_cases hsame : n + 1 < off (K + 1)
    · have hb1 : blk (n + 1) = K := hblk_uniq ((hblk_le n).trans (Nat.le_succ n)) hsame
      have hv_mem : T (n + 1) ∈ insert ((K + 1 : ℕ) : ℝ≥0) (S K) :=
        Finset.mem_insert_of_mem (hb1 ▸ hT_mem (n + 1))
      have h1_lt : n + 1 - off K < (L K).length := by
        have : off K ≤ n := hblk_le n
        rw [hoff_succ] at hsame; omega
      have hTn1_eq : T (n + 1) = (L K)[n + 1 - off K]'h1_lt := hT_eq h1_lt hb1 rfl
      have hno : ∀ w ∈ S K, ¬ (T n < w ∧ w < T (n + 1)) := by
        intro w hw ⟨hw1, hw2⟩
        obtain ⟨j, hj_lt, rfl⟩ := List.mem_iff_getElem.mp ((hL_mem K w).mpr hw)
        have hidx_gt : n - off K < j := by
          by_contra hle; push Not at hle
          rcases eq_or_lt_of_le hle with heq | hlt
          · have hTeq : (L K)[j]'hj_lt = T n := (hT_eq hj_lt rfl heq.symm).symm
            exact lt_irrefl _ (hTeq ▸ hw1)
          · have hlt' := List.pairwise_iff_getElem.mp (hL_sorted K) j (n - off K) hj_lt (hsub_lt n) hlt
            rw [← hT_eq (hsub_lt n) rfl rfl] at hlt'
            exact not_lt_of_gt hw1 hlt'
        have hidx_lt : j < n + 1 - off K := by
          by_contra hge; push Not at hge
          rcases eq_or_lt_of_le hge with heq | hlt
          · have hTeq : (L K)[j]'hj_lt = T (n + 1) := by rw [hTn1_eq]; simp [heq]
            exact lt_irrefl _ (hTeq ▸ hw2)
          · have hlt' := List.pairwise_iff_getElem.mp (hL_sorted K) (n + 1 - off K) j h1_lt hj_lt hlt
            rw [← hTn1_eq] at hlt'
            exact not_lt_of_gt hw2 hlt'
        have := hblk_le n; omega
      exact hS_const K (T n) (T (n + 1)) hu_mem hv_mem (hT_strictMono (Nat.lt_succ_self n)) hno t htn htn1
    · have hge : off (K + 1) ≤ n + 1 := le_of_not_gt hsame
      have heq : n + 1 = off (K + 1) := le_antisymm (Nat.succ_le_of_lt (hblk_lt n)) hge
      have hb1 : blk (n + 1) = K + 1 :=
        hblk_uniq (heq ▸ le_rfl) (by rw [heq]; exact hoff_strictMono (Nat.lt_succ_self _))
      have hTn1_eq : T (n + 1) = ((K + 1 : ℕ) : ℝ≥0) := by
        rw [hT_eq (hL_len_pos (K + 1)) hb1 (by rw [heq, Nat.sub_self]), hL_head (K + 1)]
      have hno : ∀ w ∈ S K, ¬ (T n < w ∧ w < ((K + 1 : ℕ) : ℝ≥0)) := by
        intro w hw ⟨hw1, _⟩
        obtain ⟨j, hj_lt, rfl⟩ := List.mem_iff_getElem.mp ((hL_mem K w).mpr hw)
        have hidx_gt : n - off K < j := by
          by_contra hle; push Not at hle
          rcases eq_or_lt_of_le hle with heq' | hlt
          · have hTeq : (L K)[j]'hj_lt = T n := (hT_eq hj_lt rfl heq'.symm).symm
            exact lt_irrefl _ (hTeq ▸ hw1)
          · have hlt' := List.pairwise_iff_getElem.mp (hL_sorted K) j (n - off K) hj_lt (hsub_lt n) hlt
            rw [← hT_eq (hsub_lt n) rfl rfl] at hlt'
            exact not_lt_of_gt hw1 hlt'
        have hoff_eq : off (K + 1) = off K + (L K).length := hoff_succ K
        have := hblk_le n; omega
      rw [hTn1_eq] at htn1
      exact hS_const K (T n) ((K + 1 : ℕ) : ℝ≥0) hu_mem (Finset.mem_insert_self _ _)
        (hT_bounds n).2 hno t htn htn1
  dsimp only
  rw [hconst_n]; ring

open Classical in
private lemma part3_bwd
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (hσ : σ = 0) (hfin : ν Set.univ < ⊤) :
    ∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω) := by
  have hfin_inst : IsFiniteMeasure ν := ⟨hfin⟩
  have hsf_inst : SigmaFinite ν := inferInstance
  -- Define drift `d = -a - ∫_{|x|<1} x ∂ν` and drift-removed process `Y t ω = X t ω - d * t`
  let d : ℝ := -a - ∫ x in {x : ℝ | |x| < 1}, x ∂ν
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => X t ω - d * (t : ℝ)
  have hY_levy : ProbabilityTheory.IsLevyProcess Y P := {
    start_zero := by funext ω; simp [Y, hX.start_zero]
    indep_increments := by
      intro n t ht
      have hind := hX.indep_increments n t ht
      let shift : Fin n → ℝ → ℝ := fun k x => x - d * (((t k.succ : ℝ) - (t k.castSucc : ℝ)))
      have hmeas : ∀ k, Measurable (shift k) := fun _ => measurable_id.sub measurable_const
      have hcomp := hind.comp shift hmeas
      have heq : (fun k => shift k ∘ ProbabilityTheory.increment X (t k.castSucc) (t k.succ)) =
          fun k => ProbabilityTheory.increment Y (t k.castSucc) (t k.succ) := by
        funext k ω; simp only [Function.comp_apply, shift, ProbabilityTheory.increment, Y]; ring
      rwa [heq] at hcomp
    stationary_increments := by
      intro s h
      have hid := hX.stationary_increments s h
      let f : ℝ → ℝ := fun x => x - d * (h : ℝ)
      have hf : Measurable f := measurable_id.sub measurable_const
      have hcomp := hid.comp hf
      have heq1 : f ∘ ProbabilityTheory.increment X s (s + h) =
          ProbabilityTheory.increment Y s (s + h) := by
        funext ω; simp only [Function.comp_apply, f, ProbabilityTheory.increment, Y]; push_cast; ring
      have heq2 : f ∘ ProbabilityTheory.increment X 0 h =
          ProbabilityTheory.increment Y 0 h := by
        funext ω; simp only [Function.comp_apply, f, ProbabilityTheory.increment, Y]; push_cast; ring
      rwa [heq1, heq2] at hcomp
    cadlag_ae := by
      filter_upwards [hX.cadlag_ae] with ω hω t
      have hlin_cont : Continuous (fun u : ℝ≥0 => d * (u : ℝ)) :=
        continuous_const.mul NNReal.continuous_coe
      refine ⟨(hω t).1.sub hlin_cont.continuousWithinAt, ?_⟩
      obtain ⟨l, hl⟩ := (hω t).2
      exact ⟨l - d * (t : ℝ), hl.sub (hlin_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩
  }
  -- Compute `charFun (P.map (Y t)) ξ = exp(t * ∫ (exp(i ξ x) - 1) ∂ν)`
  have hY_char : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Y t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in (Set.univ : Set ℝ),
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
    intro t ξ
    let g : ℝ → ℝ := fun x => x - d * (t : ℝ)
    have hg : Measurable g := measurable_id.sub measurable_const
    have hY_eq : Y t = g ∘ X t := rfl
    have haeX := levyProcess_aemeasurable hX t
    rw [hY_eq, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable haeX, charFun_apply_real]
    have hcont_exp : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    rw [integral_map hg.aemeasurable hcont_exp.aestronglyMeasurable]
    have hpull : (fun x : ℝ => Complex.exp ((ξ : ℂ) * ((g x : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ => Complex.exp (-(Complex.I * ((d * (t : ℝ) * ξ : ℝ) : ℂ))) *
          Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) := by
      funext x; dsimp only [g]; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hpull, integral_const_mul, ← charFun_apply_real, hchar t ξ, ← Complex.exp_add]
    congr 1
    -- Simplify the exponent using `hσ` and `IsFiniteMeasure ν`
    have hU_meas : MeasurableSet {x : ℝ | |x| < 1} := continuous_abs.measurable measurableSet_Iio
    have hint_lin : Integrable (fun x : ℝ => x) (ν.restrict {x : ℝ | |x| < 1}) :=
      Integrable.of_bound measurable_id.aestronglyMeasurable 1 (by
        filter_upwards [ae_restrict_mem hU_meas] with x hx
        simpa [Real.norm_eq_abs] using hx.le)
    have hint_exp1 : Integrable (fun x : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1) ν :=
      Integrable.of_bound
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.mul continuous_const).mul
          continuous_const)).sub continuous_const).aestronglyMeasurable
        2 (Eventually.of_forall fun x => by
          calc ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1‖
              ≤ ‖Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by
                have hc : (x : ℂ) * (ξ : ℂ) * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; rfl
                rw [hc, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num)
    have hint_comp : Integrable (fun x : ℝ =>
        (x : ℂ) * (ξ : ℂ) * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) ν := by
      have heq : (fun x : ℝ => (x : ℂ) * (ξ : ℂ) * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) =
          {x : ℝ | |x| < 1}.indicator (fun x : ℝ => ((ξ : ℂ) * Complex.I) * (x : ℂ)) := by
        funext x; by_cases hx : |x| < 1 <;> simp [hx]; ring
      rw [heq, integrable_indicator_iff hU_meas]
      exact (Complex.ofRealCLM.integrable_comp hint_lin).const_mul _
    have hint_split : ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν =
        (∫ x, (Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1) ∂ν) -
          (ξ : ℂ) * Complex.I * ((∫ x in {x : ℝ | |x| < 1}, x ∂ν : ℝ) : ℂ) := by
      unfold ProbabilityTheory.levyCompensatedIntegrand
      rw [integral_sub hint_exp1 hint_comp]
      congr 1
      have heq : (fun x : ℝ => (x : ℂ) * (ξ : ℂ) * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) =
          {x : ℝ | |x| < 1}.indicator (fun x : ℝ => ((ξ : ℂ) * Complex.I) * (x : ℂ)) := by
        funext x; by_cases hx : |x| < 1 <;> simp [hx]; ring
      rw [heq, integral_indicator hU_meas, integral_const_mul]
      have hcomm : (∫ x in {x : ℝ | |x| < 1}, (x : ℂ) ∂ν) =
          Complex.ofRealCLM (∫ x in {x : ℝ | |x| < 1}, x ∂ν) :=
        Complex.ofRealCLM.integral_comp_comm hint_lin
      rw [hcomm]; rfl
    unfold Kyprianou.Ch01.levyTripleExponent
    simp only [hσ, NNReal.coe_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div,
      Complex.ofReal_zero, sub_zero]
    rw [hint_split, Measure.restrict_univ]
    have hexp_eq : ∫ x, (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν =
        ∫ x, (Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1) ∂ν := by
      congr 1; funext x; congr 2; push_cast; ring
    rw [hexp_eq]
    dsimp only [d]; push_cast; ring
  -- Compare `Y t` with a finite-intensity Poisson integral `Z t` to get `P {Y t = 0} ≥ exp(-t * ν univ)`
  obtain ⟨Ω', mΩ', P', hP', ⟨N⟩⟩ := Kyprianou.poissonRandomMeasureExists ν
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  obtain ⟨_, hZ_char⟩ := Kyprianou.finiteRegionPoissonIntegralCh02V3 P' ν N Set.univ MeasurableSet.univ hfin
  let Z : ℝ≥0 → Ω' → ℝ := fun t ω' => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ∂(N.N ω')
  let lam : ℝ := (ν Set.univ).toReal
  have hY_zero_ge : ∀ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(t : ℝ) * lam)) ≤ P {ω | Y t ω = 0} := by
    intro t
    have hZ_meas : Measurable (Z t) :=
      Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P' ν N _ (measurableSet_Ioc.prod MeasurableSet.univ)
    have hY_aem : AEMeasurable (Y t) P := levyProcess_aemeasurable hY_levy t
    have : IsProbabilityMeasure (P.map (Y t)) := Measure.isProbabilityMeasure_map hY_aem
    have : IsProbabilityMeasure (P'.map (Z t)) := Measure.isProbabilityMeasure_map hZ_meas.aemeasurable
    have hmap_eq : P.map (Y t) = P'.map (Z t) :=
      Measure.ext_of_charFun (funext fun ξ => (hY_char t ξ).trans (hZ_char t ξ).symm)
    have hP_eq : P {ω | Y t ω = 0} = P' {ω' | Z t ω' = 0} := by
      have h1 : {ω | Y t ω = 0} = (Y t) ⁻¹' {0} := rfl
      have h2 : {ω' | Z t ω' = 0} = (Z t) ⁻¹' {0} := rfl
      rw [h1, h2, ← Measure.map_apply_of_aemeasurable hY_aem (measurableSet_singleton 0),
        ← Measure.map_apply hZ_meas (measurableSet_singleton 0), hmap_eq]
    rw [hP_eq]
    let S : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
    have hSm : MeasurableSet S := measurableSet_Ioc.prod MeasurableSet.univ
    have hSint : LevyStochCalc.Poisson.referenceIntensity ν S = ENNReal.ofReal (t : ℝ) * ν Set.univ := by
      unfold LevyStochCalc.Poisson.referenceIntensity
      rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
        Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) (t : ℝ) ⊆ Set.Ici (0 : ℝ) from fun _ hx => le_of_lt hx.1),
        Real.volume_Ioc, sub_zero]
    have hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤ := by
      rw [hSint]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
    have hsub : {ω' | N.N ω' S = 0} ⊆ {ω' | Z t ω' = 0} := by
      intro ω' h0
      change ∫ z in S, z.2 ∂(N.N ω') = 0
      have hres0 : (N.N ω').restrict S = 0 := Measure.restrict_eq_zero.mpr h0
      rw [hres0]; simp
    have hpois := N.poisson_law hSm hSfin
    have hP_count0 : P' {ω' | N.N ω' S = 0} = ENNReal.ofReal (Real.exp (-(t : ℝ) * lam)) := by
      have hpre : {ω' | N.N ω' S = 0} = (fun ω' => N.N ω' S) ⁻¹' {0} := rfl
      rw [hpre, ← Measure.map_apply (N.measurable_eval hSm) (measurableSet_singleton 0),
        hpois, poissonMeasureENN_apply_zero]
      congr 2
      have htr : ((LevyStochCalc.Poisson.referenceIntensity ν S).toNNReal : ℝ) = (t : ℝ) * lam := by
        change (LevyStochCalc.Poisson.referenceIntensity ν S).toReal = (t : ℝ) * lam
        rw [hSint, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]
      rw [htr]; ring
    exact hP_count0 ▸ measure_mono hsub
  -- Bound `P {ω | ¬ ConstDyad (Y · ω) u v} ≤ ENNReal.ofReal (((v : ℝ) - (u : ℝ)) * lam)`
  have hConst_null : ∀ (u v : ℝ≥0), NullMeasurableSet {ω | ConstDyad (fun t => Y t ω) u v} P := by
    intro u v
    have heq : {ω | ConstDyad (fun t => Y t ω) u v} =
        ⋂ (r : ℕ) (k : Fin (2 ^ r)),
          (fun ω => Y (u + ((k.1 + 1 : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω -
            Y (u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω) ⁻¹' {0} := by
      ext ω; simp [ConstDyad, sub_eq_zero]
    rw [heq]
    refine NullMeasurableSet.iInter fun r => NullMeasurableSet.iInter fun k => ?_
    have hae : AEMeasurable (fun ω => Y (u + ((k.1 + 1 : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω -
        Y (u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω) P :=
      (levyProcess_aemeasurable hY_levy _).sub (levyProcess_aemeasurable hY_levy _)
    exact ⟨hae.mk _ ⁻¹' {0}, hae.measurable_mk (measurableSet_singleton 0), by
      filter_upwards [hae.ae_eq_mk] with ω hω
      show (Y (u + ((k.1 + 1 : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω -
          Y (u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω = 0) = (hae.mk _ ω = 0)
      rw [hω]⟩
  have hNotConst_le : ∀ (u v : ℝ≥0), u ≤ v →
      P {ω | ¬ ConstDyad (fun t => Y t ω) u v} ≤ ENNReal.ofReal (((v : ℝ) - (u : ℝ)) * lam) := by
    intro u v huv
    let Level : ℕ → Set Ω := fun r =>
      ⋂ k : Fin (2 ^ r),
        {ω | ProbabilityTheory.increment Y
          (u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r))
          (u + ((k.1 + 1 : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)) ω = 0}
    have hLevel_nm : ∀ r, NullMeasurableSet (Level r) P := fun r =>
      NullMeasurableSet.iInter fun k => by
        have hae : AEMeasurable (ProbabilityTheory.increment Y
            (u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r))
            (u + ((k.1 + 1 : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r))) P :=
          (levyProcess_aemeasurable hY_levy _).sub (levyProcess_aemeasurable hY_levy _)
        exact ⟨hae.mk _ ⁻¹' {0}, hae.measurable_mk (measurableSet_singleton 0), by
          filter_upwards [hae.ae_eq_mk] with ω hω
          show (ProbabilityTheory.increment Y _ _ ω = 0) = (hae.mk _ ω = 0)
          rw [hω]⟩
    have hLevel_anti : Antitone Level := antitone_nat_of_succ_le fun r ω hω => by
      simp only [Level, Set.mem_iInter, Set.mem_ofPred_eq, ProbabilityTheory.increment, sub_eq_zero] at hω ⊢
      intro k
      have h1 := hω ⟨2 * k.1, by rw [pow_succ']; omega⟩
      have h2 := hω ⟨2 * k.1 + 1, by rw [pow_succ']; omega⟩
      have harg : ∀ j : ℕ, u + ((2 * j : ℕ) : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ (r + 1)) =
          u + (j : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r) := fun j => by
        ext; push_cast [pow_succ]
        have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
        field_simp [h2r]
      rw [harg k.1] at h1
      rw [show 2 * k.1 + 1 + 1 = 2 * (k.1 + 1) by omega, harg (k.1 + 1)] at h2
      exact h2.trans h1
    have hLevel_ge : ∀ r : ℕ, ENNReal.ofReal (Real.exp (-((v : ℝ) - (u : ℝ)) * lam)) ≤ P (Level r) := by
      intro r
      let ts : Fin (2 ^ r + 1) → ℝ≥0 := fun k => u + (k.1 : ℝ≥0) * (v - u) / ((2 : ℝ≥0) ^ r)
      have hts_mono : Monotone ts := fun i j hij => by dsimp only [ts]; gcongr; exact hij
      have hind := hY_levy.indep_increments (2 ^ r) ts hts_mono
      have hprod := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind) Finset.univ
        (sets := fun _ => ({0} : Set ℝ)) (fun _ _ => measurableSet_singleton 0)
      have hLevel_eq : Level r = ⋂ k ∈ (Finset.univ : Finset (Fin (2 ^ r))),
          (ProbabilityTheory.increment Y (ts k.castSucc) (ts k.succ)) ⁻¹' {0} := by
        ext ω; simp [Level, ts]
      rw [hLevel_eq, hprod]
      let δ : ℝ≥0 := (v - u) / ((2 : ℝ≥0) ^ r)
      have hterm : ∀ k : Fin (2 ^ r),
          ENNReal.ofReal (Real.exp (-(δ : ℝ) * lam)) ≤
            P ((ProbabilityTheory.increment Y (ts k.castSucc) (ts k.succ)) ⁻¹' {0}) := fun k => by
        have hadd : ts k.castSucc + δ = ts k.succ := by
          ext; dsimp only [ts, δ]
          simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
            NNReal.coe_pow, NNReal.coe_ofNat, Fin.val_castSucc, Fin.val_succ]
          push_cast; ring
        have hid := hY_levy.stationary_increments (ts k.castSucc) δ
        have h0 : ProbabilityTheory.increment Y 0 δ = Y δ := by
          funext ω; simp [ProbabilityTheory.increment, hY_levy.start_zero]
        rw [hadd, h0] at hid
        have hae1 : AEMeasurable (ProbabilityTheory.increment Y (ts k.castSucc) (ts k.succ)) P :=
          (levyProcess_aemeasurable hY_levy _).sub (levyProcess_aemeasurable hY_levy _)
        have hae2 : AEMeasurable (Y δ) P := levyProcess_aemeasurable hY_levy δ
        rw [← Measure.map_apply_of_aemeasurable hae1 (measurableSet_singleton 0), hid.map_eq,
          Measure.map_apply_of_aemeasurable hae2 (measurableSet_singleton 0)]
        exact hY_zero_ge δ
      calc ENNReal.ofReal (Real.exp (-((v : ℝ) - (u : ℝ)) * lam))
          = ENNReal.ofReal ((Real.exp (-(δ : ℝ) * lam)) ^ (2 ^ r)) := by
            congr 1; rw [← Real.exp_nat_mul]
            congr 1
            have hδr : (δ : ℝ) = ((v : ℝ) - (u : ℝ)) / (2 : ℝ) ^ r := by
              dsimp only [δ]; rw [NNReal.coe_div, NNReal.coe_sub huv]; push_cast; rfl
            rw [hδr]
            have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
            push_cast; field_simp [h2r]
        _ = (ENNReal.ofReal (Real.exp (-(δ : ℝ) * lam))) ^ (2 ^ r) := by
            rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
        _ = ∏ _k : Fin (2 ^ r), ENNReal.ofReal (Real.exp (-(δ : ℝ) * lam)) := by
            simp
        _ ≤ ∏ k : Fin (2 ^ r), P ((ProbabilityTheory.increment Y (ts k.castSucc) (ts k.succ)) ⁻¹' {0}) :=
            Finset.prod_le_prod' fun k _ => hterm k
    have hiInter_eq : (⋂ r : ℕ, Level r) = {ω | ConstDyad (fun t => Y t ω) u v} := by
      ext ω; simp [Level, ConstDyad, ProbabilityTheory.increment, sub_eq_zero]
    have htend := MeasureTheory.tendsto_measure_iInter_atTop hLevel_nm hLevel_anti ⟨0, measure_ne_top P _⟩
    rw [hiInter_eq] at htend
    have hConst_ge : ENNReal.ofReal (Real.exp (-((v : ℝ) - (u : ℝ)) * lam)) ≤
        P {ω | ConstDyad (fun t => Y t ω) u v} :=
      ge_of_tendsto htend (Eventually.of_forall hLevel_ge)
    have hcompl : {ω | ¬ ConstDyad (fun t => Y t ω) u v} = {ω | ConstDyad (fun t => Y t ω) u v}ᶜ := rfl
    rw [hcompl, measure_compl₀ (hConst_null u v) (measure_ne_top P _), measure_univ]
    have hsub_le : 1 - P {ω | ConstDyad (fun t => Y t ω) u v} ≤
        1 - ENNReal.ofReal (Real.exp (-((v : ℝ) - (u : ℝ)) * lam)) :=
      tsub_le_tsub_left hConst_ge 1
    have h1_sub : 1 - ENNReal.ofReal (Real.exp (-((v : ℝ) - (u : ℝ)) * lam)) =
        ENNReal.ofReal (1 - Real.exp (-((v : ℝ) - (u : ℝ)) * lam)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    have hlin_bd : 1 - Real.exp (-((v : ℝ) - (u : ℝ)) * lam) ≤ ((v : ℝ) - (u : ℝ)) * lam := by
      have hv_ge : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
      have hlam_nn : 0 ≤ lam := ENNReal.toReal_nonneg
      have h1 := one_sub_exp_neg_le (mul_nonneg (show 0 ≤ (v : ℝ) - (u : ℝ) by linarith) hlam_nn)
      rwa [← neg_mul] at h1
    exact hsub_le.trans (h1_sub ▸ ENNReal.ofReal_le_ofReal hlin_bd)
  -- For each unit interval `[K, K + 1]`, apply Monotone Convergence to the bad dyadic count
  have hunit_ae : ∀ K : ℕ, ∀ᵐ ω ∂P, ∃ M : ℕ, ∀ m : ℕ,
      (Finset.univ.filter fun k : Fin (2 ^ m) =>
        ¬ ConstDyad (fun t => Y t ω) ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))).card ≤ M := by
    intro K
    let BadSet : (m : ℕ) → Fin (2 ^ m) → Set Ω := fun m k =>
      {ω | ¬ ConstDyad (fun t => Y t ω) ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
          ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))}
    let cnt : ℕ → Ω → ℝ≥0∞ := fun m ω =>
      ∑ k : Fin (2 ^ m), (BadSet m k).indicator (fun _ => (1 : ℝ≥0∞)) ω
    have hcnt_eq_card : ∀ m ω, cnt m ω =
        ((Finset.univ.filter fun k : Fin (2 ^ m) => ω ∈ BadSet m k).card : ℝ≥0∞) := by
      intro m ω
      simp only [cnt, Set.indicator]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcnt_aem : ∀ m, AEMeasurable (cnt m) P := fun m => by
      refine Finset.aemeasurable_fun_sum Finset.univ fun k _ => ?_
      have hnm : NullMeasurableSet (BadSet m k) P := (hConst_null _ _).compl
      exact aemeasurable_const.indicator₀ hnm
    have hcnt_mono : ∀ ω, Monotone (fun m => cnt m ω) := fun ω =>
      monotone_nat_of_le_succ fun m => by
        rw [hcnt_eq_card, hcnt_eq_card]
        norm_cast
        let B₀ := Finset.univ.filter fun k : Fin (2 ^ m) => ω ∈ BadSet m k
        let B₁ := Finset.univ.filter fun j : Fin (2 ^ (m + 1)) => ω ∈ BadSet (m + 1) j
        have hsub : B₀ ⊆ B₁.image (fun j : Fin (2 ^ (m + 1)) =>
            (⟨j.1 / 2, by
              have hj2 : j.1 < 2 * 2 ^ m := by simpa [pow_succ'] using j.2
              omega⟩ : Fin (2 ^ m))) := by
          intro k hk
          have hkbad := (Finset.mem_filter.mp hk).2
          let u : ℝ≥0 := (K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m)
          let v : ℝ≥0 := (K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m)
          have huv : u ≤ v := nnreal_grid_step_le K k.1 m
          have hmid : u + (v - u) / 2 = (K : ℝ≥0) + ((2 * k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
            ext; rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub huv]; dsimp only [u, v]
            push_cast [pow_succ]
            have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
            field_simp [h2m]; ring
          have hu_eq : u = (K : ℝ≥0) + ((2 * k.1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
            ext; dsimp only [u]; push_cast [pow_succ]
            have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
            field_simp [h2m]
          have hv_eq : v = (K : ℝ≥0) + ((2 * k.1 + 1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (m + 1)) := by
            ext; dsimp only [v]; push_cast [pow_succ]
            have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
            field_simp [h2m]; ring
          by_cases h1 : ¬ ConstDyad (fun t => Y t ω) u (u + (v - u) / 2)
          · refine Finset.mem_image.mpr ⟨⟨2 * k.1, by rw [pow_succ']; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext (by dsimp only; omega)⟩
            change ¬ ConstDyad (fun t => Y t ω) _ _
            rwa [← hmid, ← hu_eq]
          · push Not at h1
            have h2 : ¬ ConstDyad (fun t => Y t ω) (u + (v - u) / 2) v :=
              fun h2' => hkbad (constDyad_join huv h1 h2')
            refine Finset.mem_image.mpr ⟨⟨2 * k.1 + 1, by rw [pow_succ']; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext (by dsimp only; omega)⟩
            change ¬ ConstDyad (fun t => Y t ω) _ _
            rwa [← hmid, ← hv_eq]
        exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hlint_le : ∀ m : ℕ, ∫⁻ ω, cnt m ω ∂P ≤ ENNReal.ofReal lam := fun m => by
      dsimp only [cnt]
      rw [lintegral_finset_sum' _ fun k _ => by
        have hnm : NullMeasurableSet (BadSet m k) P := (hConst_null _ _).compl
        exact aemeasurable_const.indicator₀ hnm]
      have hterm : ∀ k : Fin (2 ^ m),
          ∫⁻ ω, (BadSet m k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
            ENNReal.ofReal (lam / (2 : ℝ) ^ m) := fun k => by
        have hnm : NullMeasurableSet (BadSet m k) P := (hConst_null _ _).compl
        rw [lintegral_indicator_const₀ hnm, one_mul]
        have hle : (K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m) ≤
            (K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m) := nnreal_grid_step_le K k.1 m
        have hbd := hNotConst_le _ _ hle
        have hdiff : ((((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m) : ℝ≥0) : ℝ) -
            (((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m) : ℝ≥0) : ℝ)) * lam = lam / (2 : ℝ) ^ m := by
          push_cast; ring
        rwa [hdiff] at hbd
      calc ∑ k : Fin (2 ^ m), ∫⁻ ω, (BadSet m k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P
          ≤ ∑ _k : Fin (2 ^ m), ENNReal.ofReal (lam / (2 : ℝ) ^ m) := Finset.sum_le_sum fun k _ => hterm k
        _ = ((2 ^ m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (lam / (2 : ℝ) ^ m) := by simp
        _ = ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) * (lam / (2 : ℝ) ^ m)) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ = ENNReal.ofReal lam := by
            congr 1; push_cast
            have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
            field_simp [h2m]
    have hsup_lt : ∫⁻ ω, (⨆ m : ℕ, cnt m ω) ∂P < ⊤ := by
      rw [lintegral_iSup' hcnt_aem (Eventually.of_forall hcnt_mono)]
      exact lt_of_le_of_lt (iSup_le hlint_le) ENNReal.ofReal_lt_top
    have hae_lt := ae_lt_top' (AEMeasurable.iSup hcnt_aem) hsup_lt.ne
    filter_upwards [hae_lt] with ω hω
    obtain ⟨M, hM⟩ := exists_nat_gt (⨆ m : ℕ, cnt m ω).toReal
    refine ⟨M, fun m => ?_⟩
    have h1 : cnt m ω ≤ ⨆ n : ℕ, cnt n ω := le_iSup (fun n => cnt n ω) m
    have h2 : (cnt m ω).toReal ≤ (⨆ n : ℕ, cnt n ω).toReal := ENNReal.toReal_mono hω.ne h1
    rw [hcnt_eq_card, ENNReal.toReal_natCast] at h2
    have hle_nat : (Finset.univ.filter fun k : Fin (2 ^ m) => ω ∈ BadSet m k).card ≤ M := by
      exact_mod_cast (h2.trans hM.le)
    simpa [BadSet] using hle_nat
  have hall_unit : ∀ᵐ ω ∂P, ∀ K : ℕ, ∃ M : ℕ, ∀ m : ℕ,
      (Finset.univ.filter fun k : Fin (2 ^ m) =>
        ¬ ConstDyad (fun t => Y t ω) ((K : ℝ≥0) + (k.1 : ℝ≥0) / ((2 : ℝ≥0) ^ m))
            ((K : ℝ≥0) + ((k.1 + 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ m))).card ≤ M :=
    ae_all_iff.mpr hunit_ae
  filter_upwards [hY_levy.cadlag_ae, hall_unit] with ω hcad hunit
  have hpl := piecewiseLinear_of_bounded_unit_bad d (fun t => (hcad t).1) hunit
  have heq : (fun t => Y t ω + d * (t : ℝ)) = fun t => X t ω := by
    funext t; simp [Y]
  rwa [heq] at hpl

end Exercise27Helpers

theorem solution
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    :
    let piecewiseLinear : (ℝ≥0 → ℝ) → Prop := fun f =>
      ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
        Tendsto T atTop atTop ∧
        ∀ n : ℕ, ∃ (slope intercept : ℝ),
          ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
            f t = slope * (t : ℝ) + intercept
    (∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) *
          (ν {x : ℝ | threshold < |x|}).toReal))) ∧
    ((∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔
      ν = 0) ∧
    ((∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) ↔
      σ = 0 ∧ ν Set.univ < ⊤) ∧
    (ν Set.univ = ⊤ →
      ∀ᵐ ω ∂P,
        closure {t : ℝ≥0 |
          ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} =
          Set.univ) :=
  ⟨fun t threshold hthresh => Exercise27Helpers.part1_jump_prob a σ ν hν P X hX hchar t threshold hthresh,
   Exercise27Helpers.part2_continuous_iff_nu_zero a σ ν hν P X hX hchar,
   ⟨Exercise27Helpers.part3_fwd a σ ν hν P X hX hchar,
    fun ⟨hσ, hfin⟩ => Exercise27Helpers.part3_bwd a σ ν hν P X hX hchar hσ hfin⟩,
   Exercise27Helpers.part4_dense_jumps a σ ν hν P X hX hchar⟩
