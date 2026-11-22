-- Prove2me | solution 1 for Kyprianou.Ch01.brownianFirstPassageCharacteristicComplexSqrtPublic
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T10:08:36.229711+00:00
-- url     : https://prove2.me/submissions/b1a78dee-6d63-4b61-aa59-61322da0c6c5

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
import Theorems.Thm_Kyprianou_Ch01_brownianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceMeasurableFromTimePublic
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal Topology
set_option autoImplicit false
universe u

/-- Principal square root of `-2 i ξ` for `ξ > 0`. -/
theorem bfp_sqrt_pos (ξ : ℝ) (hξ : 0 < ξ) :
    (-2 * ((ξ : ℂ) * I)) ^ (1 / 2 : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) * (1 - I) := by
  have hz : -2 * ((ξ : ℂ) * I) = ((2 * ξ : ℝ) : ℂ) * (-I) := by push_cast; ring
  have h2ξ : (0 : ℝ) < 2 * ξ := by positivity
  rw [hz, cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast h2ξ.ne') (neg_ne_zero.mpr I_ne_zero)),
    log_ofReal_mul h2ξ (neg_ne_zero.mpr I_ne_zero), log_neg_I]
  have he : ((Real.log (2 * ξ) : ℂ) + -(↑Real.pi / 2) * I) * (1 / 2) =
      ((Real.log (2 * ξ) / 2 : ℝ) : ℂ) + ((-(Real.pi / 4) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hexp : Real.exp (Real.log (2 * ξ) / 2) = Real.sqrt 2 * Real.sqrt ξ := by
    rw [← Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2ξ]
    ring_nf
  rw [hexp]
  have h22 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (((Real.sqrt ξ : ℝ) : ℂ) / 2 * (1 - I)) * h22

/-- Principal square root of `-2 i ξ` for `ξ < 0`. -/
theorem bfp_sqrt_neg (ξ : ℝ) (hξ : ξ < 0) :
    (-2 * ((ξ : ℂ) * I)) ^ (1 / 2 : ℂ) = ((Real.sqrt |ξ| : ℝ) : ℂ) * (1 + I) := by
  have hz : -2 * ((ξ : ℂ) * I) = ((2 * |ξ| : ℝ) : ℂ) * I := by
    rw [abs_of_neg hξ]; push_cast; ring
  have h2ξ : (0 : ℝ) < 2 * |ξ| := by have := abs_pos.mpr hξ.ne; linarith
  rw [hz, cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast h2ξ.ne') I_ne_zero),
    log_ofReal_mul h2ξ I_ne_zero, log_I]
  have he : ((Real.log (2 * |ξ|) : ℂ) + (↑Real.pi / 2) * I) * (1 / 2) =
      ((Real.log (2 * |ξ|) / 2 : ℝ) : ℂ) + (((Real.pi / 4) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hexp : Real.exp (Real.log (2 * |ξ|) / 2) = Real.sqrt 2 * Real.sqrt |ξ| := by
    rw [← Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2ξ]
    ring_nf
  rw [hexp]
  have h22 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (((Real.sqrt |ξ| : ℝ) : ℂ) / 2 * (1 + I)) * h22

/-- Analytic continuation: a nonnegative random variable with the half-stable Laplace
transform has the half-stable characteristic function `exp(-s (-2 i ξ)^{1/2})`. -/
theorem bfp_charFun_of_laplace
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hTmeas : Measurable T) (hTnn : ∀ ω, 0 ≤ T ω)
    (s : ℝ)
    (hlap : ∀ q : ℝ, 0 ≤ q →
      ∫ ω, Real.exp (-q * T ω) ∂P = Real.exp (-s * Real.sqrt (2 * q)))
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    charFun (P.map T) ξ = Complex.exp (-(s : ℂ) * (-2 * ((ξ : ℂ) * I)) ^ (1 / 2 : ℂ)) := by
  set f : ℂ → ℂ := complexMGF T P with hf
  set G : ℂ → ℂ := fun z => Complex.exp (-(s : ℂ) * (-2 * z) ^ (1 / 2 : ℂ)) with hG
  set U : Set ℂ := {z : ℂ | z.re < 0} with hU
  -- exponential integrability on the closed left half-line
  have hint_le : ∀ t : ℝ, t ≤ 0 → Integrable (fun ω => Real.exp (t * T ω)) P := by
    intro t ht
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg ht (hTnn ω)
  have hset : Set.Iio (0 : ℝ) ⊆ interior (integrableExpSet T P) := by
    rw [← interior_Iio]
    exact interior_mono fun t ht => hint_le t (le_of_lt ht)
  have hfU : AnalyticOnNhd ℂ f U :=
    analyticOnNhd_complexMGF.mono fun z hz => hset hz
  have hslit : ∀ z : ℂ, z.re < 0 → -2 * z ∈ slitPlane := by
    intro z hz
    rw [mem_slitPlane_iff]; left; simp; linarith
  have hGU : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_re continuous_const)
    intro z hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => -2 * w) z := by fun_prop
    exact (((differentiableAt_const _).mul
      (hd.cpow_const (hslit z hz))).cexp).differentiableWithinAt
  -- agreement on the negative real axis
  have hreal : ∀ x : ℝ, x < 0 → f x = G x := by
    intro x hx
    rw [hf, complexMGF_ofReal, mgf]
    have := hlap (-x) (by linarith)
    simp only [neg_neg] at this
    rw [this, hG]
    simp only
    have h2x : (0 : ℝ) ≤ 2 * -x := by linarith
    have hc : (-2 * (x : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * -x) : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h2x]
      push_cast; ring_nf
    rw [hc, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  have hEq : EqOn f G U := by
    refine hfU.eqOn_of_preconnected_of_frequently_eq hGU (convex_halfSpace_re_lt 0).isPreconnected
      (z₀ := -1) (by simp [hU]) ?_
    have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (-1 : ℝ)) (𝓝[≠] (-1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := (Complex.continuous_ofReal.tendsto (-1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({-1}ᶜ : Set ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
        exact_mod_cast hx
    refine htend.frequently (Eventually.frequently ?_)
    have : ∀ᶠ x in 𝓝[≠] (-1 : ℝ), x < 0 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))
    filter_upwards [this] with x hx
    exact hreal x hx
  -- boundary limit along z = -ε + ξ i
  set p : ℝ → ℂ := fun ε => ((-ε : ℝ) : ℂ) + (ξ : ℂ) * I with hp
  have hp0 : p 0 = (ξ : ℂ) * I := by simp [hp]
  have hpc : Continuous p := by fun_prop
  have hlimf : Tendsto (fun ε => f (p ε)) (𝓝[>] 0) (𝓝 (f ((ξ : ℂ) * I))) := by
    rw [hf]
    simp only [complexMGF]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun ε => by fun_prop
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ω => ?_
      rw [Complex.norm_exp]
      simp only [hp, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im]
      rw [Real.exp_le_one_iff]
      have := hTnn ω
      have hε' : (0 : ℝ) < ε := hε
      nlinarith
    · refine Eventually.of_forall fun ω => ?_
      have hc : Continuous fun ε : ℝ => Complex.exp (p ε * (T ω : ℂ)) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      rwa [hp0] at this
  have hGcont : ContinuousAt G ((ξ : ℂ) * I) := by
    have hs : -2 * ((ξ : ℂ) * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right; simp [hξ]
    have hd : DifferentiableAt ℂ (fun w : ℂ => -2 * w) ((ξ : ℂ) * I) := by fun_prop
    exact (((differentiableAt_const _).mul (hd.cpow_const hs)).cexp).continuousAt
  have hlimG : Tendsto (fun ε => G (p ε)) (𝓝[>] 0) (𝓝 (G ((ξ : ℂ) * I))) := by
    have := ContinuousAt.comp (g := G) (f := p) (x := 0) (by rw [hp0]; exact hGcont)
      hpc.continuousAt
    have h2 := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [Function.comp_apply, hp0] at h2
    exact h2
  have hev : (fun ε => f (p ε)) =ᶠ[𝓝[>] 0] fun ε => G (p ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply hEq
    simp only [hU, hp, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    have hε' : (0 : ℝ) < ε := hε
    linarith
  have hfg : f ((ξ : ℂ) * I) = G ((ξ : ℂ) * I) :=
    tendsto_nhds_unique (hlimf.congr' hev) hlimG
  rw [← complexMGF_mul_I hTmeas.aemeasurable, ← hf, hfg]

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω))
    (s : ℝ) (hs : 0 < s) :
    let T : Ω → ℝ :=
      fun ω => match Kyprianou.Ch01.firstUpperPassage B s ω with
        | none => 0
        | some t => (t : ℝ);
    ∀ ξ : ℝ,
      charFun (P.map T) ξ =
        Complex.exp
          (-(s : ℂ) * Complex.sqrt ((-2 : ℂ) * Complex.I * (ξ : ℂ))) := by
  intro T xi
  have hτ : Measurable (firstUpperPassage B s) :=
    Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic B hMeas hContinuous s
  have hTlog : T = fun ω => -Real.log (passageLaplace (firstUpperPassage B s) 1 ω) := by
    funext ω
    simp only [T, passageLaplace]
    cases firstUpperPassage B s ω with
    | top => simp
    | coe t => simp
  have hTmeas : Measurable T := by
    rw [hTlog]
    exact ((Kyprianou.Ch01.passageLaplaceMeasurableFromTimePublic _ 1 hτ).log).neg
  have hTnn : ∀ ω, 0 ≤ T ω := by
    intro ω
    simp only [T]
    cases firstUpperPassage B s ω with
    | top => simp
    | coe t => simp
  have hfin := Kyprianou.Ch01.brownianFirstUpperPassageAlmostSureFinitePublic P B hB hMeas s hs
  have hlap : ∀ q : ℝ, 0 ≤ q →
      ∫ ω, Real.exp (-q * T ω) ∂P = Real.exp (-s * Real.sqrt (2 * q)) := by
    intro q hq
    rw [← (Kyprianou.Ch01.brownianFirstPassageStableHalf P B hB hMeas s q hs hq).2]
    refine integral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    simp only [T, passageLaplace]
    cases h : firstUpperPassage B s ω with
    | top => exact absurd h hω
    | coe t => simp
  by_cases h0 : xi = 0
  · subst h0
    haveI := Measure.isProbabilityMeasure_map (μ := P) hTmeas.aemeasurable
    simp [Complex.sqrt]
  rw [bfp_charFun_of_laplace P T hTmeas hTnn s hlap xi h0, Complex.sqrt]
  congr 3
  · ring
  · norm_num
