-- Prove2me | solution 1 for ImpulseGames.LinearGame.prop_4_7_player_one_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:32:57.481819+00:00
-- url     : https://prove2.me/submissions/ff275598-d7e7-4ce0-90f5-92b74ce02f4e

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium

set_option autoImplicit false
set_option linter.all false

open MeasureTheory Filter Topology Real Set ProbabilityTheory
open scoped NNReal

namespace P2b17

-- ===== from scratch/probe/2b17c77f_heat.lean =====


/-! ## Part H: Gaussian integration by parts (Stein) and the heat identity -/

lemma exp_abs_mul_gauss_le (K w : ℝ) :
    exp (K * |w|) * exp (-w ^ 2 / 2) ≤ exp (K ^ 2) * exp (-(1/4 : ℝ) * |w| ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← sq_abs w]
  nlinarith [sq_nonneg (|w| / 2 - K)]

lemma integrable_abs_mul_gauss_quarter :
    Integrable (fun w : ℝ => |w| * exp (-(1/4 : ℝ) * |w| ^ 2)) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := (1/4 : ℝ)) (by norm_num)).abs
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp [abs_mul, abs_of_pos (Real.exp_pos _), sq_abs]

lemma integrable_gauss_quarter : Integrable (fun w : ℝ => exp (-(1/4 : ℝ) * |w| ^ 2)) := by
  have h := integrable_exp_neg_mul_sq (b := (1/4 : ℝ)) (by norm_num)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp [sq_abs]

/-- The basic Gaussian-integrable envelope `e^{K|w|} (1+|w|) e^{-w²/2}`. -/
lemma integrable_env (K : ℝ) :
    Integrable (fun w : ℝ => exp (K * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by
  have hI : Integrable
      (fun w : ℝ => exp (K ^ 2) * ((1 + |w|) * exp (-(1/4 : ℝ) * |w| ^ 2))) := by
    refine Integrable.const_mul ?_ _
    have := integrable_gauss_quarter.add integrable_abs_mul_gauss_quarter
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]; ring
  refine hI.mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w => ?_)
  have h1 := exp_abs_mul_gauss_le K w
  have h2 : 0 ≤ 1 + |w| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc exp (K * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)
      = (exp (K * |w|) * exp (-w ^ 2 / 2)) * (1 + |w|) := by ring
    _ ≤ (exp (K ^ 2) * exp (-(1/4 : ℝ) * |w| ^ 2)) * (1 + |w|) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

lemma tendsto_gauss_bound {l : Filter ℝ} (hl : Tendsto (fun w : ℝ => |w|) l atTop) (C K : ℝ)
    (h : ℝ → ℝ) (hb : ∀ w, |h w| ≤ C * exp (K * |w|) * exp (-w ^ 2 / 2)) :
    Tendsto h l (𝓝 0) := by
  have hC : 0 ≤ C := by
    have := hb 0
    simp at this
    linarith [abs_nonneg (h 0)]
  have h1 : Tendsto (fun w : ℝ => C * exp (K ^ 2) * exp (-(1/4 : ℝ) * |w| ^ 2)) l (𝓝 0) := by
    have h2 : Tendsto (fun w : ℝ => exp (-(1/4 : ℝ) * |w| ^ 2)) l (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact Tendsto.const_mul_atTop_of_neg (by norm_num) ((tendsto_pow_atTop two_ne_zero).comp hl)
    have := h2.const_mul (C * exp (K ^ 2))
    rw [mul_zero] at this
    exact this
  refine squeeze_zero_norm (fun w => ?_) h1
  rw [Real.norm_eq_abs]
  calc |h w| ≤ C * exp (K * |w|) * exp (-w ^ 2 / 2) := hb w
    _ = C * (exp (K * |w|) * exp (-w ^ 2 / 2)) := by ring
    _ ≤ C * (exp (K ^ 2) * exp (-(1/4 : ℝ) * |w| ^ 2)) :=
        mul_le_mul_of_nonneg_left (exp_abs_mul_gauss_le K w) hC
    _ = _ := by ring

lemma hasDerivAt_gauss (w : ℝ) :
    HasDerivAt (fun w : ℝ => exp (-w ^ 2 / 2)) (-w * exp (-w ^ 2 / 2)) w := by
  have := ((hasDerivAt_pow 2 w).neg.div_const 2).exp
  convert this using 1
  all_goals first | rfl | (simp only [Pi.neg_apply]; ring) | ring | (norm_num; ring)

/-- **Stein's lemma** (Gaussian integration by parts), for `g` continuous, differentiable off a
countable set, with exponential growth. -/
theorem stein (g g' : ℝ → ℝ) (S : Set ℝ) (hS : S.Countable) (C K : ℝ) (hg : Continuous g)
    (hd : ∀ w, w ∉ S → HasDerivAt g (g' w) w) (hg'm : Measurable g')
    (hbd : ∀ w, |g w| ≤ C * exp (K * |w|)) (hbd' : ∀ w, |g' w| ≤ C * exp (K * |w|)) :
    ∫ w, w * g w * exp (-w ^ 2 / 2) = ∫ w, g' w * exp (-w ^ 2 / 2) := by
  have hC : 0 ≤ C := by
    have := hbd 0
    simp at this
    linarith [abs_nonneg (g 0)]
  have hhd : ∀ w, w ∉ S → HasDerivAt (fun w => g w * exp (-w ^ 2 / 2))
      (g' w * exp (-w ^ 2 / 2) - w * g w * exp (-w ^ 2 / 2)) w := by
    intro w hw
    have := (hd w hw).mul (hasDerivAt_gauss w)
    convert this using 1
    all_goals first | rfl | ring
  have henv := (integrable_env K).const_mul C
  have i1 : Integrable (fun w => g' w * exp (-w ^ 2 / 2)) := by
    refine henv.mono' ((hg'm.mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h0 := hbd' w
    have : 0 ≤ exp (K * |w|) * |w| * exp (-w ^ 2 / 2) := by positivity
    calc |g' w| * exp (-w ^ 2 / 2) ≤ C * exp (K * |w|) * exp (-w ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
      _ ≤ C * (exp (K * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by nlinarith
  have i2 : Integrable (fun w => w * g w * exp (-w ^ 2 / 2)) := by
    refine henv.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h0 := hbd w
    have : 0 ≤ exp (K * |w|) * exp (-w ^ 2 / 2) := by positivity
    have h3 : |w| * |g w| ≤ |w| * (C * exp (K * |w|)) :=
      mul_le_mul_of_nonneg_left h0 (abs_nonneg w)
    calc |w| * |g w| * exp (-w ^ 2 / 2) ≤ |w| * (C * exp (K * |w|)) * exp (-w ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ C * (exp (K * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by nlinarith
  have ih' : Integrable (fun w => g' w * exp (-w ^ 2 / 2) - w * g w * exp (-w ^ 2 / 2)) :=
    i1.sub i2
  have hcont : Continuous (fun w => g w * exp (-w ^ 2 / 2)) := hg.mul (by fun_prop)
  have hbh : ∀ w, |(fun w => g w * exp (-w ^ 2 / 2)) w| ≤ C * exp (K * |w|) * exp (-w ^ 2 / 2) := by
    intro w
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hbd w) (Real.exp_pos _).le
  have htop := tendsto_gauss_bound tendsto_abs_atTop_atTop C K _ hbh
  have hbot := tendsto_gauss_bound tendsto_abs_atBot_atTop C K _ hbh
  have hlim := intervalIntegral_tendsto_integral ih' tendsto_neg_atTop_atBot tendsto_id
  have heq : ∀ᶠ R in atTop, (∫ x in -R..id R, (g' x * exp (-x ^ 2 / 2) - x * g x * exp (-x ^ 2 / 2)))
      = g R * exp (-R ^ 2 / 2) - g (-R) * exp (-(-R) ^ 2 / 2) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    exact integral_eq_of_hasDerivAt_off_countable_of_le _ _ (by simp only [id]; linarith) hS
      hcont.continuousOn (fun x hx => hhd x hx.2) (ih'.intervalIntegrable)
  have h0 : Tendsto (fun R : ℝ => g R * exp (-R ^ 2 / 2) - g (-R) * exp (-(-R) ^ 2 / 2)) atTop
      (𝓝 0) := by
    have := htop.sub (hbot.comp tendsto_neg_atTop_atBot)
    simpa using this
  have htot : ∫ w, (g' w * exp (-w ^ 2 / 2) - w * g w * exp (-w ^ 2 / 2)) = 0 :=
    tendsto_nhds_unique (hlim.congr' heq) h0
  rw [integral_sub i1 i2] at htot
  linarith

/-- Regularity class for the heat identity: `u` is differentiable with derivative `u1`; `u1` is
continuous and differentiable off the countable set `S` with measurable derivative `u2`; all three
have growth `C e^{K|x|}`. -/
structure Reg (u u1 u2 : ℝ → ℝ) (S : Set ℝ) (C K : ℝ) : Prop where
  d0 : ∀ x, HasDerivAt u (u1 x) x
  c1 : Continuous u1
  cS : S.Countable
  d1 : ∀ x, x ∉ S → HasDerivAt u1 (u2 x) x
  m2 : Measurable u2
  K0 : 0 ≤ K
  b0 : ∀ x, |u x| ≤ C * exp (K * |x|)
  b1 : ∀ x, |u1 x| ≤ C * exp (K * |x|)
  b2 : ∀ x, |u2 x| ≤ C * exp (K * |x|)

lemma Reg.C0 {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K : ℝ} (h : Reg u u1 u2 S C K) : 0 ≤ C := by
  have := h.b0 0
  simp at this
  linarith [abs_nonneg (u 0)]

lemma Reg.cont {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K : ℝ} (h : Reg u u1 u2 S C K) : Continuous u :=
  continuous_iff_continuousAt.2 fun x => (h.d0 x).continuousAt

lemma comp_bound {f : ℝ → ℝ} {C K : ℝ} (hf : ∀ x, |f x| ≤ C * exp (K * |x|)) (hK : 0 ≤ K)
    (z c w : ℝ) : |f (z + c * w)| ≤ (C * exp (K * |z|)) * exp ((K * |c|) * |w|) := by
  have hC : 0 ≤ C := by
    have := hf 0
    simp at this
    linarith [abs_nonneg (f 0)]
  have h1 : K * |z + c * w| ≤ K * |z| + (K * |c|) * |w| := by
    have : |z + c * w| ≤ |z| + |c| * |w| := (abs_add_le _ _).trans (by rw [abs_mul])
    nlinarith
  calc |f (z + c * w)| ≤ C * exp (K * |z + c * w|) := hf _
    _ ≤ C * exp (K * |z| + (K * |c|) * |w|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hC
    _ = _ := by rw [Real.exp_add]; ring

/-- Integrability of `w ↦ f(z + c w) e^{-w²/2}` for `f` measurable with exponential growth. -/
lemma integrable_comp_gauss {f : ℝ → ℝ} {C K : ℝ} (hf : ∀ x, |f x| ≤ C * exp (K * |x|))
    (hK : 0 ≤ K) (hm : Measurable f) (z c : ℝ) :
    Integrable (fun w => f (z + c * w) * exp (-w ^ 2 / 2)) := by
  refine ((integrable_env (K * |c|)).const_mul (C * exp (K * |z|))).mono'
    (((hm.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h0 := comp_bound hf hK z c w
  have hC : 0 ≤ C * exp (K * |z|) := by
    have := hf 0
    simp at this
    have : 0 ≤ C := by linarith [abs_nonneg (f 0)]
    positivity
  have : 0 ≤ exp ((K * |c|) * |w|) * |w| * exp (-w ^ 2 / 2) := by positivity
  calc |f (z + c * w)| * exp (-w ^ 2 / 2)
      ≤ (C * exp (K * |z|)) * exp ((K * |c|) * |w|) * exp (-w ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
    _ ≤ (C * exp (K * |z|)) * (exp ((K * |c|) * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by
        nlinarith

/-- Gaussian smoothing `G σ u z t = ∫ u (z + σ √t w) e^{-w²/2} dw`. -/
noncomputable def G (σ : ℝ) (u : ℝ → ℝ) (z t : ℝ) : ℝ :=
  ∫ w, u (z + σ * √t * w) * exp (-w ^ 2 / 2)

/-- Stein applied to `u1(z + c ·)`: `∫ w u1(z+cw) e^{-w²/2} = c ∫ u2(z+cw) e^{-w²/2}`. -/
lemma stein_comp {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K : ℝ} (hR : Reg u u1 u2 S C K) (z c : ℝ) (hc : c ≠ 0) :
    ∫ w, w * u1 (z + c * w) * exp (-w ^ 2 / 2) =
      c * ∫ w, u2 (z + c * w) * exp (-w ^ 2 / 2) := by
  have hC := hR.C0
  have key := stein (fun w => u1 (z + c * w)) (fun w => c * u2 (z + c * w))
    ((fun x => (x - z) / c) '' S) (hR.cS.image _)
    ((1 + |c|) * (C * exp (K * |z|))) (K * |c|) (hR.c1.comp (by fun_prop))
    (by
      intro w hw
      have hne : z + c * w ∉ S := by
        intro h; apply hw; exact ⟨_, h, by field_simp; ring⟩
      have := (hR.d1 _ hne).comp w ((hasDerivAt_id' w).const_mul c |>.const_add z)
      convert this using 1
      all_goals first | rfl | ring)
    (measurable_const.mul (hR.m2.comp (by fun_prop)))
    (by
      intro w
      have h0 := comp_bound hR.b1 hR.K0 z c w
      have : 0 ≤ C * exp (K * |z|) * exp ((K * |c|) * |w|) := by positivity
      nlinarith [abs_nonneg c])
    (by
      intro w
      have h0 := comp_bound hR.b2 hR.K0 z c w
      have : 0 ≤ C * exp (K * |z|) * exp ((K * |c|) * |w|) := by positivity
      rw [abs_mul]
      nlinarith [abs_nonneg c, abs_nonneg (u2 (z + c * w))])
  rw [key, ← integral_const_mul]
  congr 1
  funext w
  ring

/-- **Heat equation for Gaussian smoothing**: for `t > 0`,
`∂ₜ G σ u z t = (σ²/2) G σ u2 z t`. -/
theorem hasDerivAt_G {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ : ℝ} (hR : Reg u u1 u2 S C K) (hσ : σ ≠ 0)
    (z t : ℝ) (ht : 0 < t) :
    HasDerivAt (G σ u z) (σ ^ 2 / 2 * G σ u2 z t) t := by
  have hC := hR.C0
  have hK := hR.K0
  have hdiff : ∀ s : ℝ, 0 < s → ∀ w : ℝ, HasDerivAt (fun s => u (z + σ * √s * w) * exp (-w ^ 2 / 2))
      (u1 (z + σ * √s * w) * (σ * (1 / (2 * √s)) * w) * exp (-w ^ 2 / 2)) s := by
    intro s hs w
    have h1 : HasDerivAt (fun s => z + σ * √s * w) (σ * (1 / (2 * √s)) * w) s :=
      (((Real.hasDerivAt_sqrt hs.ne').const_mul σ).mul_const w).const_add z
    exact ((hR.d0 _).comp s h1).mul_const (exp (-w ^ 2 / 2))
  have hnhds : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : 0 < √(t / 2) := Real.sqrt_pos.mpr (by linarith)
  set K' := K * (|σ| * √(2 * t)) with hK'
  set C' := C * exp (K * |z|) * (|σ| / (2 * √(t / 2))) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hbound : ∀ w : ℝ, ∀ s ∈ Ioo (t / 2) (2 * t),
      ‖u1 (z + σ * √s * w) * (σ * (1 / (2 * √s)) * w) * exp (-w ^ 2 / 2)‖ ≤
        C' * (exp (K' * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by
    intro w s hs
    have hs1 : √(t / 2) ≤ √s := Real.sqrt_le_sqrt hs.1.le
    have hs2 : √s ≤ √(2 * t) := Real.sqrt_le_sqrt hs.2.le
    have hsp : 0 < √s := lt_of_lt_of_le hpos hs1
    have hA : |u1 (z + σ * √s * w)| ≤ C * exp (K * |z|) * exp (K' * |w|) := by
      refine (comp_bound hR.b1 hK z (σ * √s) w).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_pos hsp]
      have : |σ| * √s ≤ |σ| * √(2 * t) := mul_le_mul_of_nonneg_left hs2 (abs_nonneg σ)
      have := mul_le_mul_of_nonneg_left this hK
      exact mul_le_mul_of_nonneg_right this (abs_nonneg w)
    have hB : |σ * (1 / (2 * √s)) * w| ≤ |σ| / (2 * √(t / 2)) * (1 + |w|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * √s))]
      have h3 : 1 / (2 * √s) ≤ 1 / (2 * √(t / 2)) := by gcongr
      have h4 : |w| ≤ 1 + |w| := by linarith
      calc |σ| * (1 / (2 * √s)) * |w| ≤ |σ| * (1 / (2 * √(t / 2))) * (1 + |w|) := by gcongr
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |u1 (z + σ * √s * w)| * |σ * (1 / (2 * √s)) * w| * exp (-w ^ 2 / 2)
        ≤ (C * exp (K * |z|) * exp (K' * |w|)) * (|σ| / (2 * √(t / 2)) * (1 + |w|))
            * exp (-w ^ 2 / 2) := by gcongr
      _ = C' * (exp (K' * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by rw [hC']; ring
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun s w => u (z + σ * √s * w) * exp (-w ^ 2 / 2))
    (F' := fun s w => u1 (z + σ * √s * w) * (σ * (1 / (2 * √s)) * w) * exp (-w ^ 2 / 2))
    (bound := fun w => C' * (exp (K' * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)))
    hnhds
    (Eventually.of_forall fun s =>
      (Continuous.aestronglyMeasurable ((hR.cont.comp (by fun_prop)).mul (by fun_prop))))
    (integrable_comp_gauss hR.b0 hK hR.cont.measurable z (σ * √t))
    (Continuous.aestronglyMeasurable (by
      have := hR.c1
      fun_prop))
    (Eventually.of_forall fun w s hs => hbound w s hs)
    ((integrable_env K').const_mul C')
    (Eventually.of_forall fun w s hs => hdiff s (by linarith [hs.1]) w)
  have hval : ∫ w, u1 (z + σ * √t * w) * (σ * (1 / (2 * √t)) * w) * exp (-w ^ 2 / 2) =
      σ ^ 2 / 2 * G σ u2 z t := by
    have hst : √t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have e1 : (fun w => u1 (z + σ * √t * w) * (σ * (1 / (2 * √t)) * w) * exp (-w ^ 2 / 2)) =
        fun w => (σ * (1 / (2 * √t))) * (w * u1 (z + σ * √t * w) * exp (-w ^ 2 / 2)) := by
      funext w; ring
    rw [e1, integral_const_mul, stein_comp hR z (σ * √t) (mul_ne_zero hσ hst)]
    unfold G
    field_simp
  rw [← hval]
  exact hD.2

lemma gbound {f : ℝ → ℝ} {C K : ℝ} (hf : ∀ x, |f x| ≤ C * exp (K * |x|)) (hK : 0 ≤ K)
    (z σ t T w : ℝ) (htT : t ≤ T) :
    ‖f (z + σ * √t * w) * exp (-w ^ 2 / 2)‖ ≤
      (C * exp (K * |z|)) * (exp ((K * (|σ| * √T)) * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)) := by
  have hC : 0 ≤ C := by
    have := hf 0
    simp at this
    linarith [abs_nonneg (f 0)]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h0 := comp_bound hf hK z (σ * √t) w
  have h1 : exp ((K * |σ * √t|) * |w|) ≤ exp ((K * (|σ| * √T)) * |w|) := by
    apply Real.exp_le_exp.mpr
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
    have : |σ| * √t ≤ |σ| * √T :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT) (abs_nonneg σ)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hK) (abs_nonneg w)
  have hCz : 0 ≤ C * exp (K * |z|) := by positivity
  calc |f (z + σ * √t * w)| * exp (-w ^ 2 / 2)
      ≤ (C * exp (K * |z|)) * exp ((K * (|σ| * √T)) * |w|) * exp (-w ^ 2 / 2) := by
        gcongr
        exact h0.trans (mul_le_mul_of_nonneg_left h1 hCz)
    _ ≤ _ := by
        have : 0 ≤ (C * exp (K * |z|)) * exp ((K * (|σ| * √T)) * |w|) * exp (-w ^ 2 / 2) := by
          positivity
        nlinarith [abs_nonneg w]

lemma G_abs_le {f : ℝ → ℝ} {C K : ℝ} (hf : ∀ x, |f x| ≤ C * exp (K * |x|)) (hK : 0 ≤ K)
    (z σ t T : ℝ) (htT : t ≤ T) :
    |G σ f z t| ≤ (C * exp (K * |z|)) *
      ∫ w, exp ((K * (|σ| * √T)) * |w|) * (1 + |w|) * exp (-w ^ 2 / 2) := by
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrable_env _).const_mul _)
    (Eventually.of_forall fun w => gbound hf hK z σ t T w htT)

lemma measurable_G {f : ℝ → ℝ} (hm : Measurable f) (σ z : ℝ) :
    Measurable (fun t => G σ f z t) := by
  have h : Measurable fun p : ℝ × ℝ => f (z + σ * √p.1 * p.2) * exp (-p.2 ^ 2 / 2) :=
    (hm.comp (by fun_prop : Continuous fun p : ℝ × ℝ => z + σ * √p.1 * p.2).measurable).mul
      (by fun_prop : Continuous fun p : ℝ × ℝ => exp (-p.2 ^ 2 / 2)).measurable
  exact (StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun t w => f (z + σ * √t * w) * exp (-w ^ 2 / 2)) h.stronglyMeasurable).measurable

lemma continuousOn_G {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K : ℝ} (hR : Reg u u1 u2 S C K) (σ z T : ℝ) :
    ContinuousOn (G σ u z) (Icc 0 T) := by
  have := continuousOn_of_dominated (μ := volume) (s := Icc 0 T)
    (F := fun t w => u (z + σ * √t * w) * exp (-w ^ 2 / 2))
    (bound := fun w => (C * exp (K * |z|)) *
      (exp ((K * (|σ| * √T)) * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)))
    (fun t _ => Continuous.aestronglyMeasurable ((hR.cont.comp (by fun_prop)).mul (by fun_prop)))
    (fun t ht => Eventually.of_forall fun w => gbound hR.b0 hR.K0 z σ t T w ht.2)
    ((integrable_env _).const_mul _)
    (Eventually.of_forall fun w =>
      (((hR.cont.comp (by fun_prop : Continuous fun t : ℝ => z + σ * √t * w)).mul
        continuous_const)).continuousOn)
  exact this

/-- **Deterministic-time Dynkin identity** for Gaussian smoothing, with discount `ρ`:
`e^{-ρT} G(T) − G(0) = ∫₀ᵀ e^{-ρt} ((σ²/2) G[u''](t) − ρ G[u](t)) dt`. -/
theorem heat_dynkin {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ : ℝ} (hR : Reg u u1 u2 S C K) (hσ : σ ≠ 0)
    (ρ z T : ℝ) (hT : 0 ≤ T) :
    exp (-ρ * T) * G σ u z T - exp (-ρ * 0) * G σ u z 0 =
      ∫ t in (0:ℝ)..T, exp (-ρ * t) * (σ ^ 2 / 2 * G σ u2 z t - ρ * G σ u z t) := by
  have hcont := continuousOn_G hR σ z T
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-ρ * t)).continuousOn).mul hcont
  · intro t ht
    have h1 : HasDerivAt (fun t : ℝ => exp (-ρ * t)) (exp (-ρ * t) * (-ρ * 1)) t :=
      ((hasDerivAt_id' t).const_mul (-ρ)).exp
    have := h1.mul (hasDerivAt_G hR hσ z t ht.1)
    convert this using 1
    all_goals first | rfl | ring
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    set M0 := (C * exp (K * |z|)) *
      ∫ w, exp ((K * (|σ| * √T)) * |w|) * (1 + |w|) * exp (-w ^ 2 / 2)
    have hmeas : Measurable fun t => exp (-ρ * t) * (σ ^ 2 / 2 * G σ u2 z t - ρ * G σ u z t) :=
      (by fun_prop : Continuous fun t : ℝ => exp (-ρ * t)).measurable.mul
        ((measurable_const.mul (measurable_G hR.m2 σ z)).sub
          (measurable_const.mul (measurable_G hR.cont.measurable σ z)))
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (exp (|ρ| * T) * (σ ^ 2 / 2 * M0 + |ρ| * M0)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have h2 := G_abs_le hR.b2 hR.K0 z σ t T ht.2
    have h0 := G_abs_le hR.b0 hR.K0 z σ t T ht.2
    have he : exp (-ρ * t) ≤ exp (|ρ| * T) := by
      apply Real.exp_le_exp.mpr
      have : -ρ * t ≤ |ρ| * t := by
        have := neg_abs_le ρ
        nlinarith [ht.1]
      nlinarith [abs_nonneg ρ, ht.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hA : |σ ^ 2 / 2 * G σ u2 z t - ρ * G σ u z t| ≤ σ ^ 2 / 2 * M0 + |ρ| * M0 := by
      calc |σ ^ 2 / 2 * G σ u2 z t - ρ * G σ u z t|
          ≤ |σ ^ 2 / 2 * G σ u2 z t| + |ρ * G σ u z t| := abs_sub _ _
        _ = σ ^ 2 / 2 * |G σ u2 z t| + |ρ| * |G σ u z t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
        _ ≤ σ ^ 2 / 2 * M0 + |ρ| * M0 := by
            gcongr
    have hM : 0 ≤ σ ^ 2 / 2 * M0 + |ρ| * M0 := (abs_nonneg _).trans hA
    calc exp (-ρ * t) * |σ ^ 2 / 2 * G σ u2 z t - ρ * G σ u z t|
        ≤ exp (|ρ| * T) * (σ ^ 2 / 2 * M0 + |ρ| * M0) :=
          mul_le_mul he hA (abs_nonneg _) (Real.exp_pos _).le

/-! ## Part B0: from Gaussian smoothing to Brownian expectations -/

open ProbabilityTheory in
lemma integral_comp_bm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (f : ℝ → ℝ) (hf : Measurable f) (t : NNReal) :
    ∫ ω, f (B t ω) ∂P = (√(2 * π))⁻¹ * ∫ w, f (√(t : ℝ) * w) * exp (-w ^ 2 / 2) := by
  have h1 : ∫ ω, f (B t ω) ∂P = ∫ x, f x ∂(gaussianReal 0 t) := by
    rw [← (hB.hasLaw_eval t).map_eq, integral_map (hB.aemeasurable t) hf.aestronglyMeasurable]
  have h2 : gaussianReal 0 t = (gaussianReal 0 1).map (fun w => √(t : ℝ) * w) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  rw [h1, h2, integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  congr 1
  funext w
  simp [gaussianPDFReal_def]
  ring

lemma integral_gauss_one : ∫ w : ℝ, exp (-w ^ 2 / 2) = √(2 * π) := by
  have := integral_gaussian (1 / 2)
  have e : (fun w : ℝ => exp (-w ^ 2 / 2)) = fun w : ℝ => exp (-(1 / 2) * w ^ 2) := by
    funext w; ring_nf
  rw [e, this]
  congr 1
  field_simp

lemma G_zero {u : ℝ → ℝ} (σ z : ℝ) : G σ u z 0 = u z * √(2 * π) := by
  unfold G
  simp only [Real.sqrt_zero, mul_zero, zero_mul, add_zero]
  rw [integral_const_mul, integral_gauss_one]

lemma G_eq_bm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : ProbabilityTheory.IsPreBrownianReal B P) (f : ℝ → ℝ) (hf : Measurable f) (σ z : ℝ)
    (t : NNReal) :
    ∫ ω, f (z + σ * B t ω) ∂P = (√(2 * π))⁻¹ * G σ f z t := by
  rw [integral_comp_bm hB (fun x => f (z + σ * x)) (hf.comp (by fun_prop)) t]
  unfold G
  congr 1
  congr 1
  funext w
  ring_nf

/-- Grid points `k/(n+1)`. -/
noncomputable def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n + 1)

/-- Approximation of `t` from below on the grid of mesh `1/(n+1)`. -/
noncomputable def gridApprox (t : ℝ≥0) (n : ℕ) : ℝ≥0 := grid n (⌊(t : ℝ) * (n + 1)⌋₊)

lemma gridApprox_coe (t : ℝ≥0) (n : ℕ) :
    (gridApprox t n : ℝ) = (⌊(t : ℝ) * (n + 1)⌋₊ : ℝ) / (n + 1) := by
  simp [gridApprox, grid]

lemma tendsto_gridApprox (t : ℝ≥0) : Tendsto (gridApprox t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  have h1 : ∀ n : ℕ, (t : ℝ) - 1 / (n + 1) ≤ (gridApprox t n : ℝ) := by
    intro n
    rw [gridApprox_coe, le_div_iff₀ (hpos n)]
    have := Nat.lt_floor_add_one ((t : ℝ) * (n + 1))
    have e : ((t : ℝ) - 1 / (n + 1)) * (n + 1) = (t : ℝ) * (n + 1) - 1 := by
      field_simp
    rw [e]; linarith
  have h2 : ∀ n : ℕ, (gridApprox t n : ℝ) ≤ t := by
    intro n
    rw [gridApprox_coe, div_le_iff₀ (hpos n)]
    exact Nat.floor_le (by positivity)
  have hlow : Tendsto (fun n : ℕ => (t : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
    have := tendsto_const_nhds (x := (t : ℝ)) |>.sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds h1 h2

/-- Every Brownian motion has a version that is measurable at each time and has continuous paths
everywhere, and that agrees with it at all times outside a null set. -/
theorem exists_good_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsBrownianReal W P) :
    ∃ B : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B t)) ∧ (∀ ω, Continuous fun t => B t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, W t ω = B t ω) ∧ IsBrownianReal B P := by
  classical
  set g : ℕ → ℕ → Ω → ℝ := fun n k => (hW.aemeasurable (grid n k)).mk _ with hgdef
  have hg : ∀ n k, Measurable (g n k) := fun n k => (hW.aemeasurable _).measurable_mk
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ ∀ n k, W (grid n k) ω = g n k ω :=
    hW.cont.and (ae_all_iff.2 fun n => ae_all_iff.2 fun k => (hW.aemeasurable _).ae_eq_mk)
  set N := toMeasurable P
    {ω | ¬ (Continuous (fun t => W t ω) ∧ ∀ n k, W (grid n k) ω = g n k ω)} with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hgoodE : ∀ ω, ω ∉ N →
      Continuous (fun t => W t ω) ∧ ∀ n k, W (grid n k) ω = g n k ω := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hnotN : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  refine ⟨fun t ω => if ω ∈ N then 0 else W t ω, ?_, ?_, ?_, ?_⟩
  · intro t
    apply measurable_of_tendsto_metrizable
      (f := fun n ω => if ω ∈ N then 0 else g n (⌊(t : ℝ) * (n + 1)⌋₊) ω)
    · intro n
      exact Measurable.ite hN measurable_const (hg _ _)
    · rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ N
      · simp [hω]
      · simp only [hω, if_false]
        have := ((hgoodE ω hω).1.tendsto t).comp (tendsto_gridApprox t)
        refine this.congr (fun n => ?_)
        simp only [Function.comp, gridApprox]
        exact (hgoodE ω hω).2 _ _
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [hω, if_true]
      exact continuous_const
    · simp only [hω, if_false]
      exact (hgoodE ω hω).1
  · filter_upwards [hnotN] with ω hω t
    simp [hω]
  · have hae : ∀ t, W t =ᵐ[P] fun ω => if ω ∈ N then 0 else W t ω := by
      intro t
      filter_upwards [hnotN] with ω hω
      simp [hω]
    refine { toIsPreBrownianReal := hW.toIsPreBrownianReal.congr hae, cont := ?_ }
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ N
    · simp only [hω, if_true]
      exact continuous_const
    · simp only [hω, if_false]
      exact (hgoodE ω hω).1

/-! ## Part B1: freezing lemma and independence of the past from the increments -/

/-- **Freezing lemma**: for independent `X`, `Z`, `E[F(X, Z)] = E[ω ↦ E[F(X ω, Z)]]`. -/
lemma freeze {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Z : Ω → β}
    (hXZ : IndepFun X Z P) (hX : Measurable X) (hZ : Measurable Z)
    (F : α → β → ℝ) (hF : Measurable (Function.uncurry F))
    (hint : Integrable (fun ω => F (X ω) (Z ω)) P) :
    ∫ ω, F (X ω) (Z ω) ∂P = ∫ ω, (∫ ω', F (X ω) (Z ω') ∂P) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hXZ
  have hXZm : Measurable (fun ω => (X ω, Z ω)) := hX.prodMk hZ
  have e1 : ∫ ω, F (X ω) (Z ω) ∂P =
      ∫ p, Function.uncurry F p ∂(P.map (fun ω => (X ω, Z ω))) := by
    rw [integral_map hXZm.aemeasurable hF.aestronglyMeasurable]
    rfl
  have hint' : Integrable (Function.uncurry F) ((P.map X).prod (P.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hXZm.aemeasurable).2 hint
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, Function.uncurry F (x, y) ∂(P.map Z))
      (P.map X) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := P.map Z)).aestronglyMeasurable
  rw [e1, hmap, integral_prod _ hint', integral_map hX.aemeasurable hmeas]
  congr 1
  funext ω
  have hm : Measurable fun y => Function.uncurry F (X ω, y) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [integral_map hZ.aemeasurable hm.aestronglyMeasurable]
  rfl

/-- The natural filtration of a measurable process. -/
noncomputable abbrev nat {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (fun t => B t) (fun t => (hBm t).stronglyMeasurable)

/-- **Weak Markov property, usable form**: any `𝓕ₛ`-measurable `X` is independent of the
increment `B (s + v) − B s`. -/
lemma indep_past_shift {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (s v : ℝ≥0)
    (X : Ω → α) (hX : Measurable[nat B hBm s] X) :
    IndepFun X (fun ω => B (s + v) ω - B s ω) P := by
  have h := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at h ⊢
  have h1 : MeasurableSpace.comap X ‹_› ≤
      MeasurableSpace.comap (fun ω (t : Set.Iic s) => B t ω) MeasurableSpace.pi := by
    have := Filtration.natural_eq_comap (fun t => B t) (fun t => (hBm t).stronglyMeasurable) s
    rw [← this]
    exact hX.comap_le
  have h2 : MeasurableSpace.comap (fun ω => B (s + v) ω - B s ω) (inferInstance : MeasurableSpace ℝ)
      ≤ MeasurableSpace.comap (fun ω t => B (s + t) ω - B s ω) MeasurableSpace.pi := by
    have e : (fun ω => B (s + v) ω - B s ω) =
        (fun f : ℝ≥0 → ℝ => f v) ∘ (fun ω t => B (s + t) ω - B s ω) := rfl
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply v).comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h.symm h1) h2


-- ===== from scratch/probe/2b17c77f_ms.lean =====


/-! ## Part MS: the Markov step with an `𝓕ₛ`-measurable random starting point -/

lemma measurable_G2 {f : ℝ → ℝ} (hm : Measurable f) (σ : ℝ) :
    Measurable (fun p : ℝ × ℝ => G σ f p.1 p.2) := by
  have h : Measurable fun q : (ℝ × ℝ) × ℝ => f (q.1.1 + σ * √q.1.2 * q.2) * exp (-q.2 ^ 2 / 2) :=
    (hm.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 + σ * √q.1.2 * q.2).measurable).mul
      (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => exp (-q.2 ^ 2 / 2)).measurable
  exact (StronglyMeasurable.integral_prod_right' (ν := volume) h.stronglyMeasurable).measurable

lemma integrable_one_add_abs_gauss :
    Integrable (fun w : ℝ => (1 + |w|) * exp (-w ^ 2 / 2)) := by
  refine (integrable_env 0).congr (Eventually.of_forall fun w => ?_)
  simp

lemma lin_C0 {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|)) : 0 ≤ D := by
  have := hf 0
  simp at this
  linarith [abs_nonneg (f 0)]

/-- Linear-growth bound for Gaussian smoothing. -/
lemma G_lin_le {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|)) (hm : Measurable f)
    (σ y t T : ℝ) (htT : t ≤ T) :
    |G σ f y t| ≤ D * (1 + |y| + |σ| * √T) * ∫ w, (1 + |w|) * exp (-w ^ 2 / 2) := by
  have hD := lin_C0 hf
  unfold G
  rw [← integral_const_mul (D * (1 + |y| + |σ| * √T)), ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    (integrable_one_add_abs_gauss.const_mul (D * (1 + |y| + |σ| * √T)))
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |y + σ * √t * w| ≤ |y| + |σ| * √T * |w| := by
    calc |y + σ * √t * w| ≤ |y| + |σ * √t * w| := abs_add_le _ _
      _ = |y| + |σ| * √t * |w| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
      _ ≤ |y| + |σ| * √T * |w| := by
          gcongr
  have h2 : 1 + (|y| + |σ| * √T * |w|) ≤ (1 + |y| + |σ| * √T) * (1 + |w|) := by
    have : 0 ≤ |σ| * √T := by positivity
    nlinarith [abs_nonneg y, abs_nonneg w]
  have h3 : |f (y + σ * √t * w)| ≤ D * ((1 + |y| + |σ| * √T) * (1 + |w|)) :=
    (hf _).trans (mul_le_mul_of_nonneg_left (by linarith) hD)
  calc |f (y + σ * √t * w)| * exp (-w ^ 2 / 2)
      ≤ D * ((1 + |y| + |σ| * √T) * (1 + |w|)) * exp (-w ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = D * (1 + |y| + |σ| * √T) * ((1 + |w|) * exp (-w ^ 2 / 2)) := by ring

/-- Freezing applied to an `𝓕ₛ`-measurable pair `(a, Y)` and the increment over `[s, s+t]`. -/
lemma freeze_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (s t : ℝ≥0)
    (a Y : Ω → ℝ) (ha : Measurable[nat B hBm s] a) (hab : ∀ ω, |a ω| ≤ 1)
    (hY : Measurable[nat B hBm s] Y) (hYi : Integrable Y P)
    {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|)) (hm : Measurable f) (σ : ℝ) :
    ∫ ω, a ω * f (Y ω + σ * (B (s + t) ω - B s ω)) ∂P =
      ∫ ω, a ω * ((√(2 * π))⁻¹ * G σ f (Y ω) t) ∂P := by
  have hD := lin_C0 hf
  have hle := (nat B hBm).le s
  have ham : Measurable a := ha.mono hle le_rfl
  have hYm : Measurable Y := hY.mono hle le_rfl
  have hZm : Measurable fun ω => B (s + t) ω - B s ω := (hBm _).sub (hBm _)
  have hX : Measurable[nat B hBm s] (fun ω => (a ω, Y ω)) := ha.prodMk hY
  have hind := indep_past_shift hB hBm s t (fun ω => (a ω, Y ω)) hX
  have hZ : IsPreBrownianReal (fun t ω => B (s + t) ω - B s ω) P := hB.shift s
  have hZi : Integrable (fun ω => B (s + t) ω - B s ω) P := hZ.integrable_eval t
  have hint : Integrable (fun ω => a ω * f (Y ω + σ * (B (s + t) ω - B s ω))) P := by
    refine (((integrable_const (1 : ℝ)).add hYi.abs).add (hZi.abs.const_mul |σ|)).const_mul D
      |>.mono' ((ham.mul (hm.comp (hYm.add (hZm.const_mul σ)))).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hf (Y ω + σ * (B (s + t) ω - B s ω))
    have h2 : |Y ω + σ * (B (s + t) ω - B s ω)| ≤ |Y ω| + |σ| * |B (s + t) ω - B s ω| := by
      calc _ ≤ |Y ω| + |σ * (B (s + t) ω - B s ω)| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    have h3 : 0 ≤ |f (Y ω + σ * (B (s + t) ω - B s ω))| := abs_nonneg _
    have h4 := hab ω
    simp only [Pi.add_apply]
    calc |a ω| * |f (Y ω + σ * (B (s + t) ω - B s ω))|
        ≤ 1 * |f (Y ω + σ * (B (s + t) ω - B s ω))| := mul_le_mul_of_nonneg_right h4 h3
      _ ≤ D * (1 + |Y ω| + |σ| * |B (s + t) ω - B s ω|) := by
          rw [one_mul]
          refine h1.trans ?_
          apply mul_le_mul_of_nonneg_left _ hD
          linarith
  have key := freeze hind (ham.prodMk hYm) hZm (fun p z => p.1 * f (p.2 + σ * z))
    (measurable_fst.fst.mul (hm.comp (measurable_fst.snd.add (measurable_snd.const_mul σ))))
    hint
  simp only at key
  rw [key]
  congr 1
  funext ω
  rw [integral_const_mul]
  congr 1
  exact G_eq_bm hZ f hm σ (Y ω) t

lemma G_sub_smul {f g : ℝ → ℝ} (σ α β z t : ℝ)
    (hf : Integrable fun w => f (z + σ * √t * w) * exp (-w ^ 2 / 2))
    (hg : Integrable fun w => g (z + σ * √t * w) * exp (-w ^ 2 / 2)) :
    G σ (fun x => α * f x - β * g x) z t = α * G σ f z t - β * G σ g z t := by
  unfold G
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hf.const_mul _) (hg.const_mul _)]
  congr 1
  funext w
  ring

/-- Pointwise Dynkin identity in Gaussian-smoothing form, normalised. -/
lemma dynkin_G {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ : ℝ} (hR : Reg u u1 u2 S C K) (hσ : σ ≠ 0)
    (ρ y v : ℝ) (hv : 0 ≤ v) :
    (√(2 * π))⁻¹ * (exp (-ρ * v) * G σ u y v) - u y =
      (√(2 * π))⁻¹ * ∫ t in (0:ℝ)..v,
        exp (-ρ * t) * G σ (fun x => σ ^ 2 / 2 * u2 x - ρ * u x) y t := by
  have hd := heat_dynkin hR hσ ρ y v hv
  rw [G_zero] at hd
  have hc : (√(2 * π))⁻¹ * √(2 * π) = 1 := by
    have : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have e : ∀ t, G σ (fun x => σ ^ 2 / 2 * u2 x - ρ * u x) y t =
      σ ^ 2 / 2 * G σ u2 y t - ρ * G σ u y t := fun t =>
    G_sub_smul σ _ _ y t (integrable_comp_gauss hR.b2 hR.K0 hR.m2 y (σ * √t))
      (integrable_comp_gauss hR.b0 hR.K0 hR.cont.measurable y (σ * √t))
  simp_rw [e]
  rw [← hd]
  simp only [mul_zero, Real.exp_zero, one_mul]
  rw [mul_sub, show (√(2 * π))⁻¹ * (u y * √(2 * π)) = u y * ((√(2 * π))⁻¹ * √(2 * π)) by ring,
    hc, mul_one]

lemma integrable_mul_lin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a X : Ω → ℝ} (ham : Measurable a) (hab : ∀ ω, |a ω| ≤ 1) (hXm : Measurable X)
    (hXi : Integrable X P) {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|))
    (hm : Measurable f) : Integrable (fun ω => a ω * f (X ω)) P := by
  have hD := lin_C0 hf
  refine (((integrable_const (1 : ℝ)).add hXi.abs).const_mul D).mono'
    ((ham.mul (hm.comp hXm)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  calc |a ω| * |f (X ω)| ≤ 1 * |f (X ω)| := mul_le_mul_of_nonneg_right (hab ω) (abs_nonneg _)
    _ ≤ D * (1 + |X ω|) := by rw [one_mul]; exact hf _

lemma integrable_mul_G {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a Y : Ω → ℝ} (ham : Measurable a) (hab : ∀ ω, |a ω| ≤ 1) (hYm : Measurable Y)
    (hYi : Integrable Y P) {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|))
    (hm : Measurable f) (σ t c : ℝ) : Integrable (fun ω => a ω * (c * G σ f (Y ω) t)) P := by
  have hD := lin_C0 hf
  set M := ∫ w, (1 + |w|) * exp (-w ^ 2 / 2)
  have hGm : Measurable fun ω => G σ f (Y ω) t :=
    (measurable_G2 hm σ).comp (hYm.prodMk measurable_const)
  refine ((((integrable_const (1 + |σ| * √t)).add hYi.abs).const_mul (|c| * D * M))).mono'
    ((ham.mul (measurable_const.mul hGm)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
  have hG := G_lin_le hf hm σ (Y ω) t t le_rfl
  have hM : 0 ≤ M := integral_nonneg fun w => by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  simp only [Pi.add_apply]
  calc |a ω| * (|c| * |G σ f (Y ω) t|) ≤ 1 * (|c| * |G σ f (Y ω) t|) :=
        mul_le_mul_of_nonneg_right (hab ω) (by positivity)
    _ ≤ |c| * (D * (1 + |Y ω| + |σ| * √t) * M) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hG (abs_nonneg c)
    _ = |c| * D * M * (1 + |σ| * √t + |Y ω|) := by ring

/-- **Markov step**: Dynkin's formula on `[s, s+v]` for the process `Y + σ (B_· − B_s)` started at an
`𝓕ₛ`-measurable integrable point `Y`, tested against a bounded `𝓕ₛ`-measurable `a`. -/
theorem markov_step {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ D : ℝ} (hR : Reg u u1 u2 S C K)
    (hσ : σ ≠ 0) (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (ρ : ℝ)
    (s v : ℝ≥0) (a Y : Ω → ℝ) (ha : Measurable[nat B hBm s] a) (hab : ∀ ω, |a ω| ≤ 1)
    (hY : Measurable[nat B hBm s] Y) (hYi : Integrable Y P) :
    ∫ ω, a ω * (exp (-ρ * (s + v)) * u (Y ω + σ * (B (s + v) ω - B s ω))
        - exp (-ρ * s) * u (Y ω)) ∂P =
      ∫ r in (0:ℝ)..v, exp (-ρ * (s + r)) * ∫ ω, a ω *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B (s + r.toNNReal) ω - B s ω))
          - ρ * u (Y ω + σ * (B (s + r.toNNReal) ω - B s ω))) ∂P := by
  have hD := lin_C0 hl0
  have hle := (nat B hBm).le s
  have ham : Measurable a := ha.mono hle le_rfl
  have hYm : Measurable Y := hY.mono hle le_rfl
  set c0 := (√(2 * π))⁻¹ with hc0
  set L : ℝ → ℝ := fun x => σ ^ 2 / 2 * u2 x - ρ * u x with hL
  have hLm : Measurable L :=
    (measurable_const.mul hR.m2).sub (measurable_const.mul hR.cont.measurable)
  have hLl : ∀ x, |L x| ≤ ((σ ^ 2 / 2 + |ρ|) * D) * (1 + |x|) := by
    intro x
    simp only [hL]
    have h1 := hl0 x
    have h2 := hl2 x
    have h3 : |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ σ ^ 2 / 2 * |u2 x| + |ρ| * |u x| := by
      calc |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ |σ ^ 2 / 2 * u2 x| + |ρ * u x| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
    have h4 : 0 ≤ σ ^ 2 / 2 := by positivity
    nlinarith [abs_nonneg ρ, abs_nonneg x, mul_le_mul_of_nonneg_left h2 h4,
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
  have hZm : Measurable fun ω => B (s + v) ω - B s ω := (hBm _).sub (hBm _)
  have hZi : Integrable (fun ω => B (s + v) ω - B s ω) P := (hB.shift s).integrable_eval v
  have hXi : Integrable (fun ω => Y ω + σ * (B (s + v) ω - B s ω)) P := hYi.add (hZi.const_mul σ)
  -- the right-hand side, rewritten through freezing
  have hRHS : ∀ r ∈ Set.uIcc (0:ℝ) v,
      exp (-ρ * (s + r)) * ∫ ω, a ω *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B (s + r.toNNReal) ω - B s ω))
          - ρ * u (Y ω + σ * (B (s + r.toNNReal) ω - B s ω))) ∂P =
      exp (-ρ * s) * c0 * ∫ ω, a ω * (exp (-ρ * r) * G σ L (Y ω) r) ∂P := by
    intro r hr
    have h0r : 0 ≤ r := by
      rcases Set.mem_uIcc.1 hr with h | h
      · exact h.1
      · linarith [h.1, h.2, NNReal.coe_nonneg v]
    have hfr := freeze_step hB hBm s r.toNNReal a Y ha hab hY hYi hLl hLm σ
    simp only [hL] at hfr ⊢
    rw [hfr, Real.coe_toNNReal r h0r, show -ρ * (↑s + r) = -ρ * ↑s + -ρ * r by ring, Real.exp_add,
      ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext ω
    simp only [hc0]
    ring
  rw [intervalIntegral.integral_congr hRHS, intervalIntegral.integral_const_mul]
  -- the left-hand side
  have hfu := freeze_step hB hBm s v a Y ha hab hY hYi hl0 hR.cont.measurable σ
  have i1 : Integrable (fun ω => a ω * u (Y ω + σ * (B (s + v) ω - B s ω))) P :=
    integrable_mul_lin ham hab (hYm.add (hZm.const_mul σ)) hXi hl0 hR.cont.measurable
  have i2 : Integrable (fun ω => a ω * u (Y ω)) P :=
    integrable_mul_lin ham hab hYm hYi hl0 hR.cont.measurable
  have i3 : Integrable (fun ω => a ω * (c0 * G σ u (Y ω) v)) P :=
    integrable_mul_G ham hab hYm hYi hl0 hR.cont.measurable σ v c0
  have hL1 : ∫ ω, a ω * (exp (-ρ * (s + v)) * u (Y ω + σ * (B (s + v) ω - B s ω))
        - exp (-ρ * s) * u (Y ω)) ∂P =
      exp (-ρ * s) * ∫ ω, a ω * (c0 * (exp (-ρ * v) * G σ u (Y ω) v) - u (Y ω)) ∂P := by
    have e1 : (fun ω => a ω * (exp (-ρ * (s + v)) * u (Y ω + σ * (B (s + v) ω - B s ω))
        - exp (-ρ * s) * u (Y ω))) = fun ω => exp (-ρ * (s + v)) *
          (a ω * u (Y ω + σ * (B (s + v) ω - B s ω))) - exp (-ρ * s) * (a ω * u (Y ω)) := by
      funext ω; ring
    have e2 : (fun ω => a ω * (c0 * (exp (-ρ * v) * G σ u (Y ω) v) - u (Y ω))) =
        fun ω => exp (-ρ * v) * (a ω * (c0 * G σ u (Y ω) v)) - a ω * u (Y ω) := by
      funext ω; ring
    rw [e1, e2, integral_sub (i1.const_mul _) (i2.const_mul _), integral_sub (i3.const_mul _) i2,
      integral_const_mul, integral_const_mul, integral_const_mul, hfu,
      show -ρ * (↑s + ↑v) = -ρ * ↑s + -ρ * ↑v by ring, Real.exp_add]
    ring
  rw [hL1]
  have hpt : ∀ ω, a ω * (c0 * (exp (-ρ * v) * G σ u (Y ω) v) - u (Y ω)) =
      c0 * (a ω * ∫ t in (0:ℝ)..v, exp (-ρ * t) * G σ L (Y ω) t) := by
    intro ω
    simp only [hL]
    rw [dynkin_G hR hσ ρ (Y ω) v v.2]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  -- Fubini
  have hGm : Measurable fun p : Ω × ℝ => a p.1 * (exp (-ρ * p.2) * G σ L (Y p.1) p.2) :=
    (ham.comp measurable_fst).mul ((by fun_prop : Measurable fun p : Ω × ℝ => exp (-ρ * p.2)).mul
      ((measurable_G2 hLm σ).comp ((hYm.comp measurable_fst).prodMk measurable_snd)))
  have hDL := lin_C0 hLl
  set M := ∫ w, (1 + |w|) * exp (-w ^ 2 / 2)
  have hM : 0 ≤ M := integral_nonneg fun w => by positivity
  have hint : Integrable (Function.uncurry fun ω t => a ω * (exp (-ρ * t) * G σ L (Y ω) t))
      (P.prod (volume.restrict (Set.Ioc (0:ℝ) v))) := by
    have hbase : Integrable (fun p : Ω × ℝ => (exp (|ρ| * v) * ((σ ^ 2 / 2 + |ρ|) * D) * M) *
        ((1 + |σ| * √v + |Y p.1|) * 1)) (P.prod (volume.restrict (Set.Ioc (0:ℝ) v))) :=
      (((integrable_const (1 + |σ| * √(v:ℝ))).add hYi.abs).mul_prod
        (integrable_const (1 : ℝ))).const_mul _
    refine hbase.mono' hGm.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae ?_]
    swap
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    refine Eventually.of_forall fun ω => ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    simp only [Function.uncurry_apply_pair]
    have hG := G_lin_le hLl hLm σ (Y ω) t v ht.2
    have he : exp (-ρ * t) ≤ exp (|ρ| * v) := by
      apply Real.exp_le_exp.mpr
      have := neg_abs_le ρ
      nlinarith [ht.1, ht.2, abs_nonneg ρ]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |a ω| * (exp (-ρ * t) * |G σ L (Y ω) t|)
        ≤ 1 * (exp (|ρ| * v) * (((σ ^ 2 / 2 + |ρ|) * D) * (1 + |Y ω| + |σ| * √↑v) * M)) := by
          gcongr
          · exact hab ω
      _ = _ := by ring
  have hsw : ∫ ω, a ω * (∫ t in (0:ℝ)..v, exp (-ρ * t) * G σ L (Y ω) t) ∂P =
      ∫ t in (0:ℝ)..v, ∫ ω, a ω * (exp (-ρ * t) * G σ L (Y ω) t) ∂P := by
    simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg v), ← integral_const_mul]
    exact integral_integral_swap hint
  rw [hsw]
  ring

/-- Joint measurability of a measurable process with continuous paths, in the `(ω, r)` order. -/
lemma measurable_B_joint {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) :
    Measurable fun p : Ω × ℝ => B p.2.toNNReal p.1 := by
  have h : Measurable (Function.uncurry B) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hBc ω) hBm
  exact h.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)

lemma integral_abs_bm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (T : ℝ) (htT : (t : ℝ) ≤ T) :
    ∫ ω, |B t ω| ∂P ≤ (√(2 * π))⁻¹ * (√T * ∫ w, (1 + |w|) * exp (-w ^ 2 / 2)) := by
  rw [integral_comp_bm hB (fun x => |x|) continuous_abs.measurable t]
  gcongr
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun w => by positivity)
    (integrable_one_add_abs_gauss.const_mul _) (Eventually.of_forall fun w => ?_)
  simp only
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : √(t : ℝ) ≤ √T := Real.sqrt_le_sqrt htT
  have h2 : 0 ≤ exp (-w ^ 2 / 2) := (Real.exp_pos _).le
  have h3 : |w| ≤ 1 + |w| := by linarith
  calc √(t : ℝ) * |w| * exp (-w ^ 2 / 2) ≤ √T * (1 + |w|) * exp (-w ^ 2 / 2) := by gcongr
    _ = _ := by ring

/-- Product integrability of the Markov-step integrand on `Ω × (s, s+v]`. -/
lemma markov_int_integrable {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ D : ℝ} (hR : Reg u u1 u2 S C K)
    (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ρ : ℝ)
    (s v : ℝ≥0) (a Y : Ω → ℝ) (ham : Measurable a) (hab : ∀ ω, |a ω| ≤ 1)
    (hYm : Measurable Y) (hYi : Integrable Y P) :
    Integrable (fun p : Ω × ℝ => a p.1 * (exp (-ρ * p.2) *
        (σ ^ 2 / 2 * u2 (Y p.1 + σ * (B p.2.toNNReal p.1 - B s p.1))
          - ρ * u (Y p.1 + σ * (B p.2.toNNReal p.1 - B s p.1)))))
      (P.prod (volume.restrict (Set.Ioc (s:ℝ) (s + v)))) := by
  set L : ℝ → ℝ := fun x => σ ^ 2 / 2 * u2 x - ρ * u x with hL
  have hLm : Measurable L :=
    (measurable_const.mul hR.m2).sub (measurable_const.mul hR.cont.measurable)
  have hD := lin_C0 hl0
  have hLl : ∀ x, |L x| ≤ ((σ ^ 2 / 2 + |ρ|) * D) * (1 + |x|) := by
    intro x
    simp only [hL]
    have h1 := hl0 x
    have h2 := hl2 x
    have h3 : |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ σ ^ 2 / 2 * |u2 x| + |ρ| * |u x| := by
      calc |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ |σ ^ 2 / 2 * u2 x| + |ρ * u x| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
    have h4 : 0 ≤ σ ^ 2 / 2 := by positivity
    nlinarith [abs_nonneg ρ, abs_nonneg x, mul_le_mul_of_nonneg_left h2 h4,
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
  have hDL := lin_C0 hLl
  have hBj := measurable_B_joint hBm hBc
  set F : Ω → ℝ → ℝ := fun ω r => a ω * (exp (-ρ * r) * L (Y ω + σ * (B r.toNNReal ω - B s ω)))
    with hF
  have hFm : Measurable (Function.uncurry F) :=
    (ham.comp measurable_fst).mul ((by fun_prop : Measurable fun p : Ω × ℝ => exp (-ρ * p.2)).mul
      (hLm.comp ((hYm.comp measurable_fst).add
        ((hBj.sub ((hBm s).comp measurable_fst)).const_mul σ))))
  have hsv : (s : ℝ) ≤ s + v := by linarith [NNReal.coe_nonneg v]
  -- integrability of `F` on the product
  have hint : Integrable (Function.uncurry F) (P.prod (volume.restrict (Set.Ioc (s:ℝ) (s + v)))) := by
    set c1 := exp (|ρ| * (s + v)) * ((σ ^ 2 / 2 + |ρ|) * D)
    have hc1 : 0 ≤ c1 := by positivity
    have hA : Integrable (fun p : Ω × ℝ => c1 * ((1 + |Y p.1| + |σ| * |B s p.1|) * 1))
        (P.prod (volume.restrict (Set.Ioc (s:ℝ) (s + v)))) :=
      ((((integrable_const (1 : ℝ)).add hYi.abs).add
        (((hB.integrable_eval s).abs).const_mul |σ|)).mul_prod (integrable_const (1 : ℝ))).const_mul c1
    have hBi : Integrable (fun p : Ω × ℝ => |B p.2.toNNReal p.1|)
        (P.prod (volume.restrict (Set.Ioc (s:ℝ) (s + v)))) := by
      rw [integrable_prod_iff' hBj.abs.aestronglyMeasurable]
      refine ⟨Eventually.of_forall fun (r : ℝ) => (hB.integrable_eval r.toNNReal).abs, ?_⟩
      have hmeas : Measurable fun r : ℝ => ∫ ω, ‖|B r.toNNReal ω|‖ ∂P :=
        (StronglyMeasurable.integral_prod_left (μ := P)
          (f := fun (ω : Ω) (r : ℝ) => ‖|B r.toNNReal ω|‖) hBj.abs.norm.stronglyMeasurable).measurable
      refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
        ((√(2 * π))⁻¹ * (√((s:ℝ) + v) * ∫ w, (1 + |w|) * exp (-w ^ 2 / 2))) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      have h0r : 0 ≤ r := le_trans (NNReal.coe_nonneg s) hr.1.le
      simp only [Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)]
      exact integral_abs_bm_le hB r.toNNReal _ (by rw [Real.coe_toNNReal r h0r]; exact hr.2)
    refine (hA.add (hBi.const_mul (c1 * |σ|))).mono' hFm.aestronglyMeasurable ?_
    have hBs := hBm s
    rw [Measure.ae_prod_iff_ae_ae ?_]
    swap
    · exact measurableSet_le hFm.norm
        ((by fun_prop : Measurable fun p : Ω × ℝ => c1 * ((1 + |Y p.1| + |σ| * |B s p.1|) * 1)).add
          (hBj.abs.const_mul _))
    refine Eventually.of_forall fun ω => ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
    simp only [Function.uncurry_apply_pair, hF, Pi.add_apply]
    have he : exp (-ρ * r) ≤ exp (|ρ| * (s + v)) := by
      apply Real.exp_le_exp.mpr
      have := neg_abs_le ρ
      have h0r : 0 ≤ r := le_trans (NNReal.coe_nonneg s) hr.1.le
      nlinarith [hr.1, hr.2, abs_nonneg ρ]
    have hL0 := hLl (Y ω + σ * (B r.toNNReal ω - B s ω))
    have habs : |Y ω + σ * (B r.toNNReal ω - B s ω)| ≤
        |Y ω| + |σ| * |B s ω| + |σ| * |B r.toNNReal ω| := by
      calc _ ≤ |Y ω| + |σ * (B r.toNNReal ω - B s ω)| := abs_add_le _ _
        _ = |Y ω| + |σ| * |B r.toNNReal ω - B s ω| := by rw [abs_mul]
        _ ≤ |Y ω| + |σ| * (|B r.toNNReal ω| + |B s ω|) := by gcongr; exact abs_sub _ _
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |a ω| * (exp (-ρ * r) * |L (Y ω + σ * (B r.toNNReal ω - B s ω))|)
        ≤ 1 * (exp (|ρ| * (s + v)) * (((σ ^ 2 / 2 + |ρ|) * D) *
            (1 + (|Y ω| + |σ| * |B s ω| + |σ| * |B r.toNNReal ω|)))) := by
          gcongr
          · exact hab ω
          · exact hL0.trans (mul_le_mul_of_nonneg_left (by linarith) hDL)
      _ = _ := by simp only [c1]; ring
  exact hint

/-- **Markov step, integral form**: the right-hand side of `markov_step` as `E[a ∫ₛ^{s+v} …]`. -/
theorem markov_step_int {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ D : ℝ} (hR : Reg u u1 u2 S C K)
    (hσ : σ ≠ 0) (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ρ : ℝ)
    (s v : ℝ≥0) (a Y : Ω → ℝ) (ha : Measurable[nat B hBm s] a) (hab : ∀ ω, |a ω| ≤ 1)
    (hY : Measurable[nat B hBm s] Y) (hYi : Integrable Y P) :
    ∫ ω, a ω * (exp (-ρ * (s + v)) * u (Y ω + σ * (B (s + v) ω - B s ω))
        - exp (-ρ * s) * u (Y ω)) ∂P =
      ∫ ω, a ω * (∫ r in (s:ℝ)..(s + v), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B s ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B s ω)))) ∂P := by
  rw [markov_step hR hσ hl0 hl2 hB hBm ρ s v a Y ha hab hY hYi]
  have hle := (nat B hBm).le s
  have ham : Measurable a := ha.mono hle le_rfl
  have hYm : Measurable Y := hY.mono hle le_rfl
  set L : ℝ → ℝ := fun x => σ ^ 2 / 2 * u2 x - ρ * u x with hL
  have hLm : Measurable L :=
    (measurable_const.mul hR.m2).sub (measurable_const.mul hR.cont.measurable)
  have hD := lin_C0 hl0
  have hLl : ∀ x, |L x| ≤ ((σ ^ 2 / 2 + |ρ|) * D) * (1 + |x|) := by
    intro x
    simp only [hL]
    have h1 := hl0 x
    have h2 := hl2 x
    have h3 : |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ σ ^ 2 / 2 * |u2 x| + |ρ| * |u x| := by
      calc |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ |σ ^ 2 / 2 * u2 x| + |ρ * u x| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
    have h4 : 0 ≤ σ ^ 2 / 2 := by positivity
    nlinarith [abs_nonneg ρ, abs_nonneg x, mul_le_mul_of_nonneg_left h2 h4,
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
  have hDL := lin_C0 hLl
  have hBj := measurable_B_joint hBm hBc
  set F : Ω → ℝ → ℝ := fun ω r => a ω * (exp (-ρ * r) * L (Y ω + σ * (B r.toNNReal ω - B s ω)))
    with hF
  have hFm : Measurable (Function.uncurry F) :=
    (ham.comp measurable_fst).mul ((by fun_prop : Measurable fun p : Ω × ℝ => exp (-ρ * p.2)).mul
      (hLm.comp ((hYm.comp measurable_fst).add
        ((hBj.sub ((hBm s).comp measurable_fst)).const_mul σ))))
  have hsv : (s : ℝ) ≤ s + v := by linarith [NNReal.coe_nonneg v]
  -- integrability of `F` on the product
  have hint : Integrable (Function.uncurry F) (P.prod (volume.restrict (Set.Ioc (s:ℝ) (s + v)))) :=
    markov_int_integrable hR hl0 hl2 hB hBm hBc ρ s v a Y ham hab hYm hYi
  -- right-hand side: swap and substitute
  have hRHS : ∫ ω, a ω * (∫ r in (s:ℝ)..(s + v), exp (-ρ * r) *
        L (Y ω + σ * (B r.toNNReal ω - B s ω))) ∂P =
      ∫ r in (s:ℝ)..(s + v), ∫ ω, F ω r ∂P := by
    simp_rw [intervalIntegral.integral_of_le hsv, ← integral_const_mul]
    exact integral_integral_swap hint
  have hsub : ∫ r in (s:ℝ)..(s + v), ∫ ω, F ω r ∂P = ∫ r in (0:ℝ)..v, ∫ ω, F ω (s + r) ∂P := by
    have := intervalIntegral.integral_comp_add_left (fun r => ∫ ω, F ω r ∂P) (a := 0) (b := (v:ℝ))
      (s:ℝ)
    simp only [add_zero] at this
    exact this.symm
  simp only [hL] at hRHS ⊢
  rw [hRHS, hsub]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have h0r : 0 ≤ r := by
    rcases Set.mem_uIcc.1 hr with h | h
    · exact h.1
    · linarith [h.1, h.2, NNReal.coe_nonneg v]
  have e : ((s : ℝ) + r).toNNReal = s + r.toNNReal := by
    rw [Real.toNNReal_add (NNReal.coe_nonneg s) h0r, Real.toNNReal_coe]
  simp only [hF, hL, e]
  rw [← integral_const_mul]
  congr 1
  funext ω
  ring


-- ===== from scratch/probe/2b17c77f_grid.lean =====


/-! ## Part C1: Dynkin's formula between grid-valued optional times -/

lemma tele_Ico (g : ℕ → ℝ) {m k : ℕ} (hmk : m ≤ k) :
    ∑ i ∈ Finset.Ico m k, (g (i + 1) - g i) = g k - g m := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hk ih => rw [Finset.sum_Ico_succ_top hk, ih]; ring

lemma intervalIntegrable_path {f : ℝ → ℝ} (hfm : Measurable f) {D : ℝ}
    (hf : ∀ x, |f x| ≤ D * (1 + |x|)) {p : ℝ → ℝ} (hp : Continuous p) (ρ : ℝ) {a b : ℝ}
    (hab : a ≤ b) : IntervalIntegrable (fun r => exp (-ρ * r) * f (p r)) volume a b := by
  have hD := lin_C0 hf
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((by fun_prop : Continuous fun r : ℝ => exp (-ρ * r)).continuousOn)
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hp.continuousOn
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    (((by fun_prop : Measurable fun r : ℝ => exp (-ρ * r)).mul
      (hfm.comp hp.measurable)).aestronglyMeasurable) (M1 * (D * (1 + M2))) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
  have hr' : r ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hr
  have h1 := hM1 r hr'
  have h2 := hM2 r hr'
  rw [Real.norm_eq_abs] at h2
  have h3 : ‖f (p r)‖ ≤ D * (1 + M2) := by
    rw [Real.norm_eq_abs]
    exact (hf (p r)).trans (by gcongr)
  rw [norm_mul]
  exact mul_le_mul h1 h3 (norm_nonneg _) ((norm_nonneg _).trans h1)

lemma measurableSet_eq_of_le {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (h : ℝ≥0) (k : Ω → ℕ) (hk : ∀ i : ℕ, MeasurableSet[𝓕 (i * h)] {ω | k ω ≤ i}) (j : ℕ) :
    MeasurableSet[𝓕 (j * h)] {ω | k ω = j} := by
  rcases j with _ | l
  · have e : {ω | k ω = 0} = {ω | k ω ≤ 0} := by ext ω; simp
    rw [e]; exact hk 0
  · have e : {ω | k ω = l + 1} = {ω | k ω ≤ l + 1} \ {ω | k ω ≤ l} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_diff]; omega
    rw [e]
    refine (hk (l + 1)).diff (𝓕.mono ?_ _ (hk l))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ l) (by positivity)

lemma integrable_ite_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (p : Ω → Prop)
    [DecidablePred p] {f : Ω → ℝ} (hf : Integrable f P)
    (hm : Measurable fun ω => if p ω then f ω else 0) :
    Integrable (fun ω => if p ω then f ω else 0) P :=
  hf.mono hm.aestronglyMeasurable (Eventually.of_forall fun ω => by split_ifs <;> simp)

/-- **Grid optional sampling**: Dynkin's formula between two grid-valued optional times
`k₁ h ≤ k₂ h ≤ n h`, for a bounded weight `a` and a start `Y` known at time `k₁ h`. -/
theorem grid_dynkin {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ D : ℝ} (hR : Reg u u1 u2 S C K)
    (hσ : σ ≠ 0) (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ρ : ℝ) (h : ℝ≥0) (n : ℕ)
    (k₁ k₂ : Ω → ℕ) (h12 : ∀ ω, k₁ ω ≤ k₂ ω) (h2n : ∀ ω, k₂ ω ≤ n)
    (hk₁ : ∀ i : ℕ, MeasurableSet[nat B hBm (i * h)] {ω | k₁ ω ≤ i})
    (hk₂ : ∀ i : ℕ, MeasurableSet[nat B hBm (i * h)] {ω | k₂ ω ≤ i})
    (a Y : Ω → ℝ)
    (ha : ∀ i : ℕ, Measurable[nat B hBm (i * h)] fun ω => if k₁ ω ≤ i then a ω else 0)
    (hab : ∀ ω, |a ω| ≤ 1)
    (hY : ∀ i : ℕ, Measurable[nat B hBm (i * h)] fun ω => if k₁ ω ≤ i then Y ω else 0)
    (hYi : Integrable Y P) :
    ∫ ω, a ω * (exp (-ρ * (k₂ ω * h)) * u (Y ω + σ * (B (k₂ ω * h) ω - B (k₁ ω * h) ω))
        - exp (-ρ * (k₁ ω * h)) * u (Y ω)) ∂P =
      ∫ ω, a ω * (∫ r in ((k₁ ω : ℝ) * h)..((k₂ ω : ℝ) * h), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω)))) ∂P := by
  classical
  have hD := lin_C0 hl0
  have hle : ∀ i : ℕ, nat B hBm ((i : ℝ≥0) * h) ≤ ‹MeasurableSpace Ω› := fun i => (nat B hBm).le _
  have hBn : ∀ t, Measurable[nat B hBm t] (B t) := fun t =>
    (Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) t).measurable
  -- the weights and the restarted points of the grid steps
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Ω → ℝ, A = fun i ω =>
      (if k₁ ω ≤ i then a ω else 0) * (if k₂ ω ≤ i then 0 else 1) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Ω → ℝ, Z = fun i ω =>
      if k₁ ω ≤ i then Y ω + σ * (B ((i : ℝ≥0) * h) ω - B ((k₁ ω : ℝ≥0) * h) ω) else 0 :=
    ⟨_, rfl⟩
  have hAm : ∀ i : ℕ, Measurable[nat B hBm (i * h)] (A i) := by
    intro i
    rw [hA]
    exact (ha i).mul (Measurable.ite (hk₂ i) measurable_const measurable_const)
  have hAb : ∀ i ω, |A i ω| ≤ 1 := by
    intro i ω
    rw [hA]
    dsimp only
    split_ifs <;> simp [hab ω]
  have hZe : ∀ i : ℕ, Z i = fun ω => (if k₁ ω ≤ i then Y ω else 0) +
      σ * ((if k₁ ω ≤ i then B ((i : ℝ≥0) * h) ω else 0) -
        ∑ j ∈ Finset.range (i + 1), (if k₁ ω = j then B ((j : ℝ≥0) * h) ω else 0)) := by
    intro i
    funext ω
    rw [hZ]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h1 h2 h2 <;> first | omega | ring
  have hEq : ∀ j : ℕ, MeasurableSet[nat B hBm (j * h)] {ω | k₁ ω = j} :=
    measurableSet_eq_of_le (nat B hBm) h k₁ hk₁
  have hZm : ∀ i : ℕ, Measurable[nat B hBm (i * h)] (Z i) := by
    intro i
    rw [hZe i]
    refine (hY i).add (measurable_const.mul ((Measurable.ite (hk₁ i) (hBn _)
      measurable_const).sub ?_))
    refine Finset.measurable_sum _ fun j hj => ?_
    have hji : (j : ℝ≥0) * h ≤ (i : ℝ≥0) * h := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (by positivity)
    exact Measurable.ite ((nat B hBm).mono hji _ (hEq j))
      ((hBn _).mono ((nat B hBm).mono hji) le_rfl) measurable_const
  have hZi : ∀ i : ℕ, Integrable (Z i) P := by
    intro i
    rw [hZe i]
    have h1 := integrable_ite_zero (fun ω => k₁ ω ≤ i) hYi ((hY i).mono (hle i) le_rfl)
    have h2 := integrable_ite_zero (fun ω => k₁ ω ≤ i) (hB.integrable_eval ((i : ℝ≥0) * h))
      ((Measurable.ite (hk₁ i) (hBn _) measurable_const).mono (hle i) le_rfl)
    have h3 := integrable_finset_sum (Finset.range (i + 1)) (μ := P)
      (f := fun j ω => if k₁ ω = j then B ((j : ℝ≥0) * h) ω else 0) fun j _ =>
        integrable_ite_zero (fun ω => k₁ ω = j) (hB.integrable_eval ((j : ℝ≥0) * h))
          (Measurable.ite ((nat B hBm).le _ _ (hEq j)) (hBm _) measurable_const)
    exact h1.add ((h2.sub h3).const_mul σ)
  have hAm' : ∀ i : ℕ, Measurable (A i) := fun i => (hAm i).mono (hle i) le_rfl
  have hZm' : ∀ i : ℕ, Measurable (Z i) := fun i => (hZm i).mono (hle i) le_rfl
  -- the step integrands
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℕ → Ω → ℝ, Lf = fun i ω => A i ω *
      (exp (-ρ * ((((i : ℝ≥0) * h : ℝ≥0) : ℝ) + (h : ℝ))) *
        u (Z i ω + σ * (B ((i : ℝ≥0) * h + h) ω - B ((i : ℝ≥0) * h) ω))
        - exp (-ρ * (((i : ℝ≥0) * h : ℝ≥0) : ℝ)) * u (Z i ω)) := ⟨_, rfl⟩
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ℕ → Ω → ℝ, Rf = fun i ω => A i ω *
      (∫ r in (((i : ℝ≥0) * h : ℝ≥0) : ℝ)..((((i : ℝ≥0) * h : ℝ≥0) : ℝ) + (h : ℝ)),
        exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Z i ω + σ * (B r.toNNReal ω - B ((i : ℝ≥0) * h) ω))
          - ρ * u (Z i ω + σ * (B r.toNNReal ω - B ((i : ℝ≥0) * h) ω)))) := ⟨_, rfl⟩
  have key : ∀ i : ℕ, ∫ ω, Lf i ω ∂P = ∫ ω, Rf i ω ∂P := by
    intro i
    rw [hLf, hRf]
    exact markov_step_int hR hσ hl0 hl2 hB hBm hBc ρ ((i : ℝ≥0) * h) h (A i) (Z i) (hAm i)
      (hAb i) (hZm i) (hZi i)
  have intL : ∀ i : ℕ, Integrable (Lf i) P := by
    intro i
    have hl : ∀ c : ℝ, ∀ x, |exp c * u x| ≤ (exp c * D) * (1 + |x|) := fun c x => by
      rw [abs_mul, abs_of_pos (exp_pos _), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hl0 x) (exp_pos _).le
    have hum : ∀ c : ℝ, Measurable fun x => exp c * u x := fun c =>
      measurable_const.mul hR.cont.measurable
    have hX1m : Measurable fun ω => Z i ω + σ * (B ((i : ℝ≥0) * h + h) ω - B ((i : ℝ≥0) * h) ω) :=
      (hZm' i).add (measurable_const.mul ((hBm _).sub (hBm _)))
    have hX1i : Integrable (fun ω => Z i ω + σ * (B ((i : ℝ≥0) * h + h) ω
        - B ((i : ℝ≥0) * h) ω)) P :=
      (hZi i).add (((hB.integrable_eval _).sub (hB.integrable_eval _)).const_mul σ)
    set c1 : ℝ := -ρ * ((((i : ℝ≥0) * h : ℝ≥0) : ℝ) + (h : ℝ))
    set c2 : ℝ := -ρ * (((i : ℝ≥0) * h : ℝ≥0) : ℝ)
    have := (integrable_mul_lin (hAm' i) (hAb i) hX1m hX1i (hl c1) (hum c1)).sub
      (integrable_mul_lin (hAm' i) (hAb i) (hZm' i) (hZi i) (hl c2) (hum c2))
    rw [hLf]
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  have hLl : ∀ x, |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ ((σ ^ 2 / 2 + |ρ|) * D) * (1 + |x|) := by
    intro x
    have h1 := hl0 x
    have h2 := hl2 x
    have h3 : |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ σ ^ 2 / 2 * |u2 x| + |ρ| * |u x| := by
      calc |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ |σ ^ 2 / 2 * u2 x| + |ρ * u x| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
    have h4 : 0 ≤ σ ^ 2 / 2 := by positivity
    nlinarith [abs_nonneg ρ, abs_nonneg x, mul_le_mul_of_nonneg_left h2 h4,
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
  have hLm : Measurable fun x => σ ^ 2 / 2 * u2 x - ρ * u x :=
    (measurable_const.mul hR.m2).sub (measurable_const.mul hR.cont.measurable)
  have intR : ∀ i : ℕ, Integrable (Rf i) P := by
    intro i
    have hp := markov_int_integrable (σ := σ) hR hl0 hl2 hB hBm hBc ρ ((i : ℝ≥0) * h) h (A i) (Z i)
      (hAm' i) (hAb i) (hZm' i) (hZi i)
    rw [hRf]
    refine hp.integral_prod_left.congr (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [intervalIntegral.integral_of_le (by linarith [NNReal.coe_nonneg h]),
      ← integral_const_mul]
  -- pointwise decompositions
  have hfilt : ∀ ω, (Finset.range n).filter (fun i => k₁ ω ≤ i ∧ i < k₂ ω) =
      Finset.Ico (k₁ ω) (k₂ ω) := by
    intro ω
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have := h2n ω
    omega
  have eA1 : ∀ i ω, k₁ ω ≤ i → ¬ k₂ ω ≤ i → A i ω = a ω := by
    intro i ω h1 h2
    rw [hA]
    dsimp only
    rw [if_pos h1, if_neg h2, mul_one]
  have eA0 : ∀ i ω, ¬ (k₁ ω ≤ i ∧ i < k₂ ω) → A i ω = 0 := by
    intro i ω hn
    rw [hA]
    dsimp only
    by_cases h1 : k₁ ω ≤ i
    · rw [if_pos h1, if_pos (by omega), mul_zero]
    · rw [if_neg h1, zero_mul]
  have eZ : ∀ i ω, k₁ ω ≤ i →
      Z i ω = Y ω + σ * (B ((i : ℝ≥0) * h) ω - B ((k₁ ω : ℝ≥0) * h) ω) := by
    intro i ω h1
    rw [hZ]
    dsimp only
    rw [if_pos h1]
  have e1 : ∀ i : ℕ, (((i + 1 : ℕ) : ℝ≥0) * h) = (i : ℝ≥0) * h + h := by
    intro i; push_cast; ring
  have eqL : ∀ ω, a ω * (exp (-ρ * (k₂ ω * h)) * u (Y ω + σ * (B (k₂ ω * h) ω - B (k₁ ω * h) ω))
        - exp (-ρ * (k₁ ω * h)) * u (Y ω)) = ∑ i ∈ Finset.range n, Lf i ω := by
    intro ω
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun j : ℕ => exp (-ρ * (((j : ℝ≥0) * h : ℝ≥0) : ℝ)) *
        u (Y ω + σ * (B ((j : ℝ≥0) * h) ω - B ((k₁ ω : ℝ≥0) * h) ω)) := ⟨_, rfl⟩
    have hs : ∑ i ∈ Finset.range n, Lf i ω = ∑ i ∈ Finset.range n,
        if k₁ ω ≤ i ∧ i < k₂ ω then a ω * (g (i + 1) - g i) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : k₁ ω ≤ i ∧ i < k₂ ω
      · rw [if_pos hc, hLf, hg]
        dsimp only
        rw [eA1 i ω hc.1 (by omega), eZ i ω hc.1, e1 i, NNReal.coe_add]
        rw [show Y ω + σ * (B ((i : ℝ≥0) * h) ω - B ((k₁ ω : ℝ≥0) * h) ω) +
            σ * (B ((i : ℝ≥0) * h + h) ω - B ((i : ℝ≥0) * h) ω) =
            Y ω + σ * (B ((i : ℝ≥0) * h + h) ω - B ((k₁ ω : ℝ≥0) * h) ω) by ring]
      · rw [if_neg hc, hLf]
        dsimp only
        rw [eA0 i ω hc, zero_mul]
    rw [hs, ← Finset.sum_filter, hfilt ω, ← Finset.mul_sum, tele_Ico g (h12 ω), hg]
    simp only [sub_self, mul_zero, add_zero, NNReal.coe_mul, NNReal.coe_natCast]
  have eqR : ∀ ω, a ω * (∫ r in ((k₁ ω : ℝ) * h)..((k₂ ω : ℝ) * h), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω)))) =
      ∑ i ∈ Finset.range n, Rf i ω := by
    intro ω
    have hs : ∑ i ∈ Finset.range n, Rf i ω = ∑ i ∈ Finset.range n,
        if k₁ ω ≤ i ∧ i < k₂ ω then a ω * (∫ r in ((i : ℕ) : ℝ) * h..((i + 1 : ℕ) : ℝ) * h,
          exp (-ρ * r) *
          (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω))
            - ρ * u (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω)))) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : k₁ ω ≤ i ∧ i < k₂ ω
      · rw [if_pos hc, hRf]
        dsimp only
        rw [eA1 i ω hc.1 (by omega), eZ i ω hc.1]
        congr 1
        have hb2 : (((i : ℝ≥0) * h : ℝ≥0) : ℝ) + h = ((i + 1 : ℕ) : ℝ) * h := by
          push_cast; ring
        have hb1 : (((i : ℝ≥0) * h : ℝ≥0) : ℝ) = (i : ℝ) * h := by push_cast; ring
        rw [hb2, hb1]
        refine intervalIntegral.integral_congr fun r _ => ?_
        rw [show Y ω + σ * (B ((i : ℝ≥0) * h) ω - B ((k₁ ω : ℝ≥0) * h) ω) +
            σ * (B r.toNNReal ω - B ((i : ℝ≥0) * h) ω) =
            Y ω + σ * (B r.toNNReal ω - B ((k₁ ω : ℝ≥0) * h) ω) by ring]
      · rw [if_neg hc, hRf]
        dsimp only
        rw [eA0 i ω hc, zero_mul]
    have hadj := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ) * h) (μ := volume)
      (f := fun r => exp (-ρ * r) *
          (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω))
            - ρ * u (Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω)))) (h12 ω)
      (fun k _ => intervalIntegrable_path (f := fun x => σ ^ 2 / 2 * u2 x - ρ * u x) hLm hLl
        (p := fun r => Y ω + σ * (B r.toNNReal ω - B (k₁ ω * h) ω))
        (continuous_const.add (continuous_const.mul
          (((hBc ω).comp continuous_real_toNNReal).sub continuous_const))) ρ
        (by gcongr; push_cast; linarith))
    rw [hs, ← Finset.sum_filter, hfilt ω, ← Finset.mul_sum, hadj]
  simp_rw [eqL, eqR]
  rw [integral_finsetSum _ (fun i _ => intL i), integral_finsetSum _ (fun i _ => intR i)]
  exact Finset.sum_congr rfl fun i _ => key i


-- ===== from scratch/probe/2b17c77f_sup.lean =====


/-! ## Part C3: an integrable bound for the running maximum of Brownian motion -/

lemma integral_sq_gauss (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

lemma integrable_sq_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P) (hX : Measurable X) :
    Integrable (fun ω => X ω ^ 2) P := by
  have := (memLp_id_gaussianReal' (μ := (0:ℝ)) (v := v) 2 (by simp)).integrable_sq
  rw [← h.map_eq] at this
  exact this.comp_measurable hX

lemma integral_sq_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = v := by
  have := h.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [integral_sq_gauss] at this
  exact this

/-- `B²` has increasing set integrals over past events (the submartingale inequality). -/
lemma setIntegral_sq_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[nat B hBm s] A) :
    ∫ ω in A, B s ω ^ 2 ∂P ≤ ∫ ω in A, B t ω ^ 2 ∂P := by
  have hBn : Measurable[nat B hBm s] (B s) :=
    (Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) s).measurable
  have hA' : MeasurableSet A := (nat B hBm).le s _ hA
  obtain ⟨v, rfl⟩ : ∃ v, t = s + v := ⟨t - s, (add_tsub_cancel_of_le hst).symm⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Ω → ℝ, Δ = fun ω => B (s + v) ω - B s ω := ⟨_, rfl⟩
  have hΔm : Measurable Δ := by rw [hΔ]; exact (hBm _).sub (hBm _)
  have hsq : ∀ (t : ℝ≥0), Integrable (fun ω => B t ω ^ 2) P := fun t =>
    integrable_sq_of_hasLaw (hB.hasLaw_eval t) (hBm t)
  have hΔsq : Integrable (fun ω => Δ ω ^ 2) P := by
    rw [hΔ]; exact integrable_sq_of_hasLaw (hB.hasLaw_sub (s + v) s) ((hBm _).sub (hBm _))
  have hprod : Integrable (fun ω => B s ω * Δ ω) P := by
    refine ((hsq s).add hΔsq).mono' ((hBm s).mul hΔm).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|B s ω| - |Δ ω|), sq_abs (B s ω), sq_abs (Δ ω), abs_nonneg (B s ω),
      abs_nonneg (Δ ω)]
  have hind : IndepFun (A.indicator (B s)) Δ P := by
    rw [hΔ]; exact indep_past_shift hB hBm s v _ (hBn.indicator hA)
  have hmid : ∫ ω in A, B s ω * Δ ω ∂P = 0 := by
    rw [← integral_indicator hA']
    have e : A.indicator (fun ω => B s ω * Δ ω) = fun ω => A.indicator (B s) ω * Δ ω := by
      funext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e, hind.integral_fun_mul_eq_mul_integral ((hBm s).indicator hA').aestronglyMeasurable
      hΔm.aestronglyMeasurable]
    have : ∫ ω, Δ ω ∂P = 0 := by
      rw [hΔ, integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
        hB.integral_eval, sub_zero]
    rw [this, mul_zero]
  have hexp : (fun ω => B (s + v) ω ^ 2) =
      fun ω => (B s ω ^ 2 + 2 * (B s ω * Δ ω)) + Δ ω ^ 2 := by
    funext ω; rw [hΔ]; ring
  have i1 : Integrable (fun ω => B s ω ^ 2 + 2 * (B s ω * Δ ω)) (P.restrict A) :=
    ((hsq s).add (hprod.const_mul 2)).integrableOn
  have i2 : Integrable (fun ω => B s ω ^ 2) (P.restrict A) := (hsq s).integrableOn
  have i3 : Integrable (fun ω => 2 * (B s ω * Δ ω)) (P.restrict A) :=
    (hprod.const_mul 2).integrableOn
  have i4 : Integrable (fun ω => Δ ω ^ 2) (P.restrict A) := hΔsq.integrableOn
  rw [hexp, integral_add i1 i4, integral_add i2 i3, integral_const_mul, hmid]
  have : 0 ≤ ∫ ω in A, Δ ω ^ 2 ∂P := setIntegral_nonneg hA' fun ω _ => sq_nonneg _
  linarith

/-- The filtration `k ↦ 𝓕_{k / 2^N}`, indexed by `ℕ`. -/
noncomputable def dyFilt {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (N : ℕ) : Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := nat B hBm ((k : ℝ≥0) / 2 ^ N)
  mono' i j hij := (nat B hBm).mono (div_le_div_of_nonneg_right (by exact_mod_cast hij)
    (by positivity))
  le' k := (nat B hBm).le _

lemma dy_submart {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (N : ℕ) :
    Submartingale (fun (k : ℕ) ω => B ((k : ℝ≥0) / 2 ^ N) ω ^ 2) (dyFilt B hBm N) P := by
  refine submartingale_of_setIntegral_le (fun k => ?_)
    (fun k => integrable_sq_of_hasLaw (hB.hasLaw_eval _) (hBm _))
    (fun i j hij A hA => setIntegral_sq_mono hB hBm
      (div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)) hA)
  exact (((Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable)
    ((k : ℝ≥0) / 2 ^ N)).measurable).pow_const 2).stronglyMeasurable

/-- Doob's maximal inequality on the dyadic grid: `P(max_{j ≤ n} |B_{j/2^N}| ≥ k) ≤ T / k²`. -/
lemma dy_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (N n : ℕ)
    (T : ℝ) (hT : (((n : ℝ≥0) / 2 ^ N : ℝ≥0) : ℝ) ≤ T) (k : ℝ) (hk : 0 < k) :
    P {ω | k ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun j => |B ((j : ℝ≥0) / 2 ^ N) ω|} ≤ ENNReal.ofReal (T / k ^ 2) := by
  have hmax := maximal_ineq (dy_submart hB hBm N)
    (fun k ω => by simp only [Pi.zero_apply]; positivity) (ε := Real.toNNReal (k ^ 2)) n
  have hk2 : ((Real.toNNReal (k ^ 2) : ℝ≥0) : ℝ) = k ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hset : {ω | k ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun j => |B ((j : ℝ≥0) / 2 ^ N) ω|} =
      {ω | ((Real.toNNReal (k ^ 2) : ℝ≥0) : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one fun j => B ((j : ℝ≥0) / 2 ^ N) ω ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range, hk2]
    constructor
    · rintro ⟨j, hj, h⟩
      refine ⟨j, hj, ?_⟩
      have := sq_abs (B ((j : ℝ≥0) / 2 ^ N) ω)
      nlinarith
    · rintro ⟨j, hj, h⟩
      refine ⟨j, hj, ?_⟩
      have := sq_le_sq.1 h
      rwa [abs_of_pos hk] at this
  rw [hset]
  have hint : ∫ ω in {ω | ((Real.toNNReal (k ^ 2) : ℝ≥0) : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one fun j => B ((j : ℝ≥0) / 2 ^ N) ω ^ 2},
        B ((n : ℝ≥0) / 2 ^ N) ω ^ 2 ∂P ≤ T := by
    refine le_trans (setIntegral_le_integral (integrable_sq_of_hasLaw (hB.hasLaw_eval _) (hBm _))
      (Eventually.of_forall fun ω => sq_nonneg _)) ?_
    rw [integral_sq_of_hasLaw (hB.hasLaw_eval _)]
    exact hT
  have h2 := hmax.trans (ENNReal.ofReal_le_ofReal hint)
  have hpos : 0 < k ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h2

/-- `E X ≤ Σ_j P(X ≥ j)` for `X ≥ 0`. -/
lemma lintegral_le_tsum_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≤ ∑' j : ℕ, P {ω | (j : ℝ) ≤ X ω} := by
  have hpt : ∀ ω, ENNReal.ofReal (X ω) ≤
      ∑' j : ℕ, {ω | (j : ℝ) ≤ X ω}.indicator (fun _ => (1 : ENNReal)) ω := by
    intro ω
    by_cases h0 : X ω ≤ 0
    · rw [ENNReal.ofReal_of_nonpos h0]; exact zero_le
    push_neg at h0
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range (⌊X ω⌋₊ + 1)))
    have hs : ∑ j ∈ Finset.range (⌊X ω⌋₊ + 1),
        {ω | (j : ℝ) ≤ X ω}.indicator (fun _ => (1 : ENNReal)) ω = (⌊X ω⌋₊ + 1 : ℕ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ENNReal))]
      · simp
      · intro j hj
        have hj' : j ≤ ⌊X ω⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have : (j : ℝ) ≤ X ω := (Nat.cast_le.2 hj').trans (Nat.floor_le h0.le)
        simp [Set.indicator_of_mem, this]
    rw [hs]
    have := Nat.lt_floor_add_one (X ω)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun j => (measurable_const.indicator
    (measurableSet_le measurable_const hX)).aemeasurable]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [lintegral_indicator_const (measurableSet_le measurable_const hX), one_mul]

lemma summable_tail_bound (T : ℝ) (hT : 0 ≤ T) :
    Summable fun j : ℕ => if j = 0 then (1 : ℝ) else T / (j : ℝ) ^ 2 := by
  rw [← summable_nat_add_iff 1]
  have h := (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left T
  rw [← summable_nat_add_iff 1] at h
  refine h.congr fun j => ?_
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  push_cast
  ring

/-- **Integrable running maximum**: on `[0, T]` the Brownian path is dominated by an integrable
random variable. -/
theorem exists_sup_bm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℕ) :
    ∃ M : Ω → ℝ, Measurable M ∧ Integrable M P ∧ ∀ ω, ∀ t : ℝ≥0, t ≤ T → |B t ω| ≤ M ω := by
  -- dyadic maxima
  set f : ℕ → Ω → ℝ := fun N ω => (Finset.range (T * 2 ^ N + 1)).sup'
    Finset.nonempty_range_add_one fun j => |B ((j : ℝ≥0) / 2 ^ N) ω| with hf
  have hfm : ∀ N, Measurable (f N) := fun N =>
    Finset.measurable_range_sup'' fun j _ => (hBm _).abs
  have hfle : ∀ N ω j, j ≤ T * 2 ^ N → |B ((j : ℝ≥0) / 2 ^ N) ω| ≤ f N ω := fun N ω j hj =>
    Finset.le_sup' (fun j : ℕ => |B ((j : ℝ≥0) / 2 ^ N) ω|)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hmono : ∀ ω, Monotone fun N => f N ω := by
    intro ω
    refine monotone_nat_of_le_succ fun N => ?_
    refine Finset.sup'_le _ _ fun j hj => ?_
    have hj' : j ≤ T * 2 ^ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have e : ((j : ℝ≥0) / 2 ^ N) = ((2 * j : ℕ) : ℝ≥0) / 2 ^ (N + 1) := by
      push_cast; rw [pow_succ]; field_simp
    rw [e]
    exact hfle (N + 1) ω (2 * j) (by rw [pow_succ]; nlinarith)
  have hf0 : ∀ N ω, 0 ≤ f N ω := fun N ω =>
    (abs_nonneg _).trans (hfle N ω 0 (Nat.zero_le _))
  -- the uniform tail bound and the uniform bound on `E f_N`
  set b : ℕ → ℝ := fun j => if j = 0 then (1 : ℝ) else T / (j : ℝ) ^ 2 with hb
  have hbs := summable_tail_bound T (Nat.cast_nonneg T)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by simp only [hb]; split_ifs <;> positivity
  have htail : ∀ (N j : ℕ), P {ω | (j : ℝ) ≤ f N ω} ≤ ENNReal.ofReal (b j) := by
    intro N j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [hb, if_true]
      rw [ENNReal.ofReal_one]
      exact prob_le_one
    · simp only [hb, (Nat.pos_iff_ne_zero.1 hj), if_false]
      refine dy_tail hB hBm N (T * 2 ^ N) T ?_ j (by exact_mod_cast hj)
      push_cast
      rw [mul_div_assoc, div_self (by positivity), mul_one]
  have hEf : ∀ N, ∫⁻ ω, ENNReal.ofReal (f N ω) ∂P ≤ ENNReal.ofReal (∑' j, b j) := by
    intro N
    refine (lintegral_le_tsum_meas (hfm N)).trans ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hb0 hbs]
    exact ENNReal.tsum_le_tsum (htail N)
  -- pathwise boundedness
  have hbdd : ∀ ω, ∃ K, ∀ N, f N ω ≤ K := by
    intro ω
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (T : ℝ≥0))).exists_bound_of_continuousOn
      (hBc ω).continuousOn
    refine ⟨K, fun N => Finset.sup'_le _ _ fun j hj => ?_⟩
    have hj' : j ≤ T * 2 ^ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hmem : ((j : ℝ≥0) / 2 ^ N) ∈ Set.Icc (0 : ℝ≥0) T := by
      refine ⟨zero_le, ?_⟩
      rw [div_le_iff₀ (by positivity)]
      exact_mod_cast hj'
    have := hK _ hmem
    rwa [Real.norm_eq_abs] at this
  set F : Ω → ENNReal := fun ω => ⨆ N, ENNReal.ofReal (f N ω) with hF
  have hFm : Measurable F := Measurable.iSup fun N => (hfm N).ennreal_ofReal
  have hFfin : ∀ ω, F ω ≠ ⊤ := by
    intro ω
    obtain ⟨K, hK⟩ := hbdd ω
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := K)) ?_
    simp only [hF]
    exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hK N)
  have hFint : ∫⁻ ω, F ω ∂P ≠ ⊤ := by
    rw [hF, lintegral_iSup (fun N => (hfm N).ennreal_ofReal)
      (fun N₁ N₂ h ω => ENNReal.ofReal_le_ofReal (hmono ω h))]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hEf)
  refine ⟨fun ω => (F ω).toReal, hFm.ennreal_toReal,
    integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hFint, fun ω t ht => ?_⟩
  -- approximate `t` from below by dyadics
  have hfF : ∀ N, f N ω ≤ (F ω).toReal := fun N =>
    (ENNReal.ofReal_le_iff_le_toReal (hFfin ω)).1 (le_iSup (fun N => ENNReal.ofReal (f N ω)) N)
  set tN : ℕ → ℝ≥0 := fun N => ((⌊(t : ℝ) * 2 ^ N⌋₊ : ℕ) : ℝ≥0) / 2 ^ N with htN
  have hlim : Tendsto tN atTop (𝓝 t) := by
    rw [← NNReal.tendsto_coe]
    have hlow : ∀ N, (t : ℝ) - (1 / 2) ^ N ≤ ((tN N : ℝ≥0) : ℝ) := by
      intro N
      simp only [htN, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
      have h1 := Nat.sub_one_lt_floor ((t : ℝ) * 2 ^ N)
      have h2 : (0 : ℝ) < 2 ^ N := by positivity
      rw [le_div_iff₀ h2, sub_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
      linarith
    have hup : ∀ N, ((tN N : ℝ≥0) : ℝ) ≤ t := by
      intro N
      simp only [htN, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
      have h2 : (0 : ℝ) < 2 ^ N := by positivity
      rw [div_le_iff₀ h2]
      exact Nat.floor_le (by positivity)
    have h0 : Tendsto (fun N : ℕ => (t : ℝ) - (1 / 2) ^ N) atTop (𝓝 t) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_sub (t : ℝ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hlow hup
  have hcont : Tendsto (fun N => |B (tN N) ω|) atTop (𝓝 |B t ω|) :=
    ((continuous_abs.comp (hBc ω)).tendsto t).comp hlim
  refine le_of_tendsto hcont (Eventually.of_forall fun N => ?_)
  refine (hfle N ω _ ?_).trans (hfF N)
  have h1 : ⌊(t : ℝ) * 2 ^ N⌋₊ ≤ ⌊((T : ℝ)) * 2 ^ N⌋₊ :=
    Nat.floor_le_floor (by gcongr; exact_mod_cast ht)
  have h2 : ⌊((T : ℝ)) * 2 ^ N⌋₊ = T * 2 ^ N := by
    rw [show ((T : ℝ)) * 2 ^ N = ((T * 2 ^ N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  omega


-- ===== from scratch/probe/2b17c77f_opt.lean =====


/-! ## Part C2: Dynkin's formula between optional times (dyadic approximation from above) -/

/-- Upper dyadic index `⌊τ 2^m⌋ + 1` of a time `τ`. -/
noncomputable def dyIdx (m : ℕ) (τ : ℝ≥0) : ℕ := ⌊(τ : ℝ) * 2 ^ m⌋₊ + 1

lemma dyIdx_le_iff (m i : ℕ) (τ : ℝ≥0) :
    dyIdx m τ ≤ i ↔ τ < (i : ℝ≥0) * (1 / 2 ^ m) := by
  unfold dyIdx
  rw [Nat.add_one_le_iff, Nat.floor_lt (by positivity), ← NNReal.coe_lt_coe]
  push_cast
  rw [mul_one_div, lt_div_iff₀ (by positivity)]

lemma dyIdx_bounds (m : ℕ) (τ : ℝ≥0) :
    (τ : ℝ) < (dyIdx m τ : ℝ) * (1 / 2 ^ m) ∧ (dyIdx m τ : ℝ) * (1 / 2 ^ m) ≤ τ + 1 / 2 ^ m := by
  unfold dyIdx
  have h2 : (0:ℝ) < 2 ^ m := by positivity
  have hx : (0:ℝ) ≤ (τ:ℝ) * 2 ^ m := by positivity
  have h1 := Nat.floor_le hx
  have h3 := Nat.lt_floor_add_one ((τ:ℝ) * 2 ^ m)
  push_cast
  constructor
  · rw [mul_one_div, lt_div_iff₀ h2]; linarith
  · rw [mul_one_div, div_le_iff₀ h2, add_mul, one_div_mul_cancel h2.ne']; linarith

lemma dyIdx_mono (m : ℕ) {τ τ' : ℝ≥0} (h : τ ≤ τ') : dyIdx m τ ≤ dyIdx m τ' := by
  unfold dyIdx
  have : (τ : ℝ) * 2 ^ m ≤ (τ' : ℝ) * 2 ^ m := by gcongr
  have := Nat.floor_le_floor this
  omega

lemma dyIdx_le_nat (m T : ℕ) {τ : ℝ≥0} (h : τ ≤ T) : dyIdx m τ ≤ T * 2 ^ m + 1 := by
  unfold dyIdx
  have h' : (τ : ℝ) * 2 ^ m ≤ ((T * 2 ^ m : ℕ) : ℝ) := by
    push_cast; gcongr; exact_mod_cast h
  have := Nat.floor_le_floor h'
  rw [Nat.floor_natCast] at this
  omega

lemma measurable_dyIdx (m : ℕ) : Measurable (dyIdx m) := by
  unfold dyIdx
  exact (Nat.measurable_floor.comp (measurable_coe_nnreal_real.mul_const _)).add_const 1

lemma tendsto_dyIdx (τ : ℝ≥0) :
    Tendsto (fun m : ℕ => (dyIdx m τ : ℝ≥0) * (1 / 2 ^ m)) atTop (𝓝 τ) := by
  rw [← NNReal.tendsto_coe]
  have hup : Tendsto (fun m : ℕ => (τ : ℝ) + 1 / 2 ^ m) atTop (𝓝 τ) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_add (τ : ℝ)
    simpa [one_div, inv_pow] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_)
    (fun m => ?_)
  · have := (dyIdx_bounds m τ).1
    push_cast
    exact this.le
  · have := (dyIdx_bounds m τ).2
    push_cast
    exact this

/-- Real-time form of `tendsto_dyIdx`. -/
lemma tendsto_dyIdx_real (τ : ℝ≥0) :
    Tendsto (fun m : ℕ => (dyIdx m τ : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ)) atTop (𝓝 (τ : ℝ)) := by
  have := NNReal.tendsto_coe.2 (tendsto_dyIdx τ)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using this

lemma measurable_B_at {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) {s : Ω → ℝ≥0}
    (hs : Measurable s) : Measurable fun ω => B (s ω) ω :=
  (measurable_uncurry_of_continuous_of_measurable hBc hBm).comp (hs.prodMk measurable_id)

/-- Progressive measurability, as needed: `1{τ < t} B_τ` is `𝓕ₜ`-measurable for an optional `τ`. -/
lemma meas_stopped {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[nat B hBm t] {ω | τ ω < t}) (t : ℝ≥0) :
    Measurable[nat B hBm t] fun ω => if τ ω < t then B (τ ω) ω else 0 := by
  have hBn : ∀ s, Measurable[nat B hBm s] (B s) := fun s =>
    (Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) s).measurable
  have hU : Measurable[@Prod.instMeasurableSpace ℝ≥0 Ω _ (nat B hBm t)]
      (Function.uncurry fun s ω => B (min s t) ω) :=
    measurable_uncurry_of_continuous_of_measurable (m := nat B hBm t)
      (fun ω => (hBc ω).comp (continuous_id.min continuous_const))
      (fun s => (hBn _).mono ((nat B hBm).mono (min_le_right s t)) le_rfl)
  have hτ' : Measurable[nat B hBm t] fun ω => min (τ ω) t := by
    refine measurable_of_Iio (mδ := nat B hBm t) fun s => ?_
    by_cases hs : s ≤ t
    · have e : (fun ω => min (τ ω) t) ⁻¹' Set.Iio s = {ω | τ ω < s} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq, min_lt_iff]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd (lt_of_lt_of_le h hs) (lt_irrefl _)
        · exact Or.inl
      rw [e]
      exact (nat B hBm).mono hs _ (hτ s)
    · push_neg at hs
      have e : (fun ω => min (τ ω) t) ⁻¹' Set.Iio s = Set.univ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true]
        exact lt_of_le_of_lt (min_le_right _ _) hs
      rw [e]
      exact MeasurableSet.univ
  have hcomp : Measurable[nat B hBm t] fun ω => B (min (min (τ ω) t) t) ω :=
    hU.comp (hτ'.prodMk measurable_id)
  have e : (fun ω => if τ ω < t then B (τ ω) ω else 0) =
      fun ω => if τ ω < t then B (min (min (τ ω) t) t) ω else 0 := by
    funext ω
    split_ifs with h
    · rw [min_eq_left h.le, min_eq_left h.le]
    · rfl
  rw [e]
  exact Measurable.ite (hτ t) hcomp measurable_const

/-- `1{k ≤ i} B_{k h}` is `𝓕_{i h}`-measurable for a grid optional index `k`. -/
lemma meas_grid_val {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (h : ℝ≥0) (k : Ω → ℕ)
    (hk : ∀ i : ℕ, MeasurableSet[nat B hBm (i * h)] {ω | k ω ≤ i}) (i : ℕ) :
    Measurable[nat B hBm (i * h)] fun ω => if k ω ≤ i then B ((k ω : ℝ≥0) * h) ω else 0 := by
  classical
  have hBn : ∀ s, Measurable[nat B hBm s] (B s) := fun s =>
    (Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) s).measurable
  have e : (fun ω => if k ω ≤ i then B ((k ω : ℝ≥0) * h) ω else 0) = fun ω =>
      ∑ j ∈ Finset.range (i + 1), (if k ω = j then B ((j : ℝ≥0) * h) ω else 0) := by
    funext ω
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  rw [e]
  refine Finset.measurable_sum _ fun j hj => ?_
  have hji : (j : ℝ≥0) * h ≤ (i : ℝ≥0) * h := mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (by positivity)
  exact Measurable.ite ((nat B hBm).mono hji _ (measurableSet_eq_of_le (nat B hBm) h k hk j))
    ((hBn _).mono ((nat B hBm).mono hji) le_rfl) measurable_const

/-- Uniform bound for one discounted term. -/
lemma term_bound {f : ℝ → ℝ} {D : ℝ} (hf : ∀ x, |f x| ≤ D * (1 + |x|)) {ρ s T' σ y b1 b2 M : ℝ}
    (hs0 : 0 ≤ s) (hsT : s ≤ T') (hb1 : |b1| ≤ M) (hb2 : |b2| ≤ M) :
    |exp (-ρ * s) * f (y + σ * (b1 - b2))| ≤
      exp (|ρ| * T') * (D * (1 + (|y| + 2 * |σ| * M))) := by
  have hD := lin_C0 hf
  rw [abs_mul, abs_of_pos (exp_pos _)]
  have he : exp (-ρ * s) ≤ exp (|ρ| * T') := by
    apply Real.exp_le_exp.mpr
    have := neg_abs_le ρ
    nlinarith [abs_nonneg ρ]
  have hz : |y + σ * (b1 - b2)| ≤ |y| + 2 * |σ| * M := by
    calc |y + σ * (b1 - b2)| ≤ |y| + |σ| * |b1 - b2| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |y| + |σ| * (|b1| + |b2|) := by gcongr; exact abs_sub _ _
      _ ≤ |y| + 2 * |σ| * M := by nlinarith [abs_nonneg σ]
  have hfz : |f (y + σ * (b1 - b2))| ≤ D * (1 + (|y| + 2 * |σ| * M)) :=
    (hf _).trans (by gcongr)
  exact mul_le_mul he hfz (abs_nonneg _) (exp_pos _).le

/-- Measurability of `ω ↦ ∫_{α ω}^{β ω} f ω r dr` for a jointly measurable `f`. -/
lemma measurable_interval_integral {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (α β : Ω → ℝ) (hα : Measurable α) (hβ : Measurable β)
    (L : ℝ) (h0 : ∀ ω, 0 ≤ α ω) (hαβ : ∀ ω, α ω ≤ β ω) (hβL : ∀ ω, β ω ≤ L) :
    Measurable fun ω => ∫ r in α ω..β ω, f ω r := by
  classical
  have e : (fun ω => ∫ r in α ω..β ω, f ω r) = fun ω => ∫ r in Set.Ioc 0 L,
      (fun p : Ω × ℝ => if α p.1 < p.2 ∧ p.2 ≤ β p.1 then f p.1 p.2 else 0) (ω, r) := by
    funext ω
    rw [intervalIntegral.integral_of_le (hαβ ω)]
    have h1 : (fun r => (fun p : Ω × ℝ => if α p.1 < p.2 ∧ p.2 ≤ β p.1 then f p.1 p.2 else 0)
        (ω, r)) = (Set.Ioc (α ω) (β ω)).indicator (f ω) := by
      funext r
      simp only [Set.indicator_apply, Set.mem_Ioc]
    rw [h1, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 (Set.Ioc_subset_Ioc (h0 ω) (hβL ω))]
  rw [e]
  have hm : Measurable fun p : Ω × ℝ => if α p.1 < p.2 ∧ p.2 ≤ β p.1 then f p.1 p.2 else 0 :=
    Measurable.ite ((measurableSet_lt (hα.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hβ.comp measurable_fst))) hf measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 L))).measurable


-- ===== from scratch/probe/2b17c77f_opt2.lean =====


/-- **Optional sampling (Dynkin's formula) between optional times** `τ₁ ≤ τ₂ ≤ T` of the natural
filtration (`{τ < t} ∈ 𝓕ₜ`), for a bounded weight `a` and a start `Y` known at `τ₁+`. -/
theorem opt_dynkin {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K σ D : ℝ} (hR : Reg u u1 u2 S C K)
    (hσ : σ ≠ 0) (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ρ : ℝ) (T : ℕ)
    (τ₁ τ₂ : Ω → ℝ≥0) (h12 : ∀ ω, τ₁ ω ≤ τ₂ ω) (h2T : ∀ ω, τ₂ ω ≤ T)
    (hτ₁ : ∀ t, MeasurableSet[nat B hBm t] {ω | τ₁ ω < t})
    (hτ₂ : ∀ t, MeasurableSet[nat B hBm t] {ω | τ₂ ω < t})
    (a Y : Ω → ℝ) (ha : ∀ t, Measurable[nat B hBm t] fun ω => if τ₁ ω < t then a ω else 0)
    (hab : ∀ ω, |a ω| ≤ 1)
    (hY : ∀ t, Measurable[nat B hBm t] fun ω => if τ₁ ω < t then Y ω else 0)
    (hYi : Integrable Y P) :
    ∫ ω, a ω * (exp (-ρ * τ₂ ω) * u (Y ω + σ * (B (τ₂ ω) ω - B (τ₁ ω) ω))
        - exp (-ρ * τ₁ ω) * u (Y ω)) ∂P =
      ∫ ω, a ω * (∫ r in (τ₁ ω : ℝ)..(τ₂ ω), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) ∂P := by
  classical
  have hD := lin_C0 hl0
  have hle : ∀ t, nat B hBm t ≤ ‹MeasurableSpace Ω› := fun t => (nat B hBm).le t
  have hτm : ∀ τ : Ω → ℝ≥0, (∀ t, MeasurableSet[nat B hBm t] {ω | τ ω < t}) → Measurable τ :=
    fun τ hτ => measurable_of_Iio fun t => (hle t) _ (hτ t)
  have hτ₁m := hτm τ₁ hτ₁
  have hτ₂m := hτm τ₂ hτ₂
  have hT1 : ∀ ω, τ₁ ω < ((T + 1 : ℕ) : ℝ≥0) := fun ω =>
    lt_of_le_of_lt ((h12 ω).trans (h2T ω)) (by exact_mod_cast Nat.lt_succ_self T)
  have ham : Measurable a := by
    have e : a = fun ω => if τ₁ ω < ((T + 1 : ℕ) : ℝ≥0) then a ω else 0 := by
      funext ω; rw [if_pos (hT1 ω)]
    rw [e]; exact (ha _).mono (hle _) le_rfl
  have hYm : Measurable Y := by
    have e : Y = fun ω => if τ₁ ω < ((T + 1 : ℕ) : ℝ≥0) then Y ω else 0 := by
      funext ω; rw [if_pos (hT1 ω)]
    rw [e]; exact (hY _).mono (hle _) le_rfl
  obtain ⟨Mx, hMm, hMi, hMb⟩ := exists_sup_bm hB hBm hBc (T + 1)
  -- the grid times
  have hkm : ∀ (m : ℕ) (τ : Ω → ℝ≥0), Measurable τ →
      Measurable fun ω => ((dyIdx m (τ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m) := fun m τ hτ =>
    (measurable_from_nat.comp ((measurable_dyIdx m).comp hτ)).mul_const _
  have hkr : ∀ (m : ℕ) (τ : Ω → ℝ≥0), Measurable τ →
      Measurable fun ω => ((dyIdx m (τ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ) := fun m τ hτ =>
    (measurable_from_nat.comp ((measurable_dyIdx m).comp hτ)).mul_const _
  have htle : ∀ (m : ℕ) (τ : ℝ≥0), τ ≤ T →
      ((dyIdx m τ : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ) ≤ (T : ℝ) + 1 := by
    intro m τ hτ
    have h1 := (dyIdx_bounds m τ).2
    have h2 : (1 : ℝ) / 2 ^ m ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h3 : (τ : ℝ) ≤ T := by exact_mod_cast hτ
    push_cast
    linarith
  have htleN : ∀ (m : ℕ) (τ : ℝ≥0), τ ≤ T →
      ((dyIdx m τ : ℕ) : ℝ≥0) * (1 / 2 ^ m) ≤ ((T + 1 : ℕ) : ℝ≥0) := by
    intro m τ hτ
    rw [← NNReal.coe_le_coe]
    have := htle m τ hτ
    push_cast at this ⊢
    exact this
  have ht0 : ∀ (m : ℕ) (τ : ℝ≥0), 0 ≤ ((dyIdx m τ : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ) :=
    fun m τ => by positivity
  have hτ₁T : ∀ ω, τ₁ ω ≤ T := fun ω => (h12 ω).trans (h2T ω)
  have hBτ : ∀ ω, |B (τ₁ ω) ω| ≤ Mx ω := fun ω =>
    hMb ω _ ((hτ₁T ω).trans (by exact_mod_cast Nat.le_succ T))
  have hBt : ∀ (m : ℕ) (τ : Ω → ℝ≥0), (∀ ω, τ ω ≤ T) → ∀ ω,
      |B (((dyIdx m (τ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω| ≤ Mx ω :=
    fun m τ hτ ω => hMb ω _ (htleN m _ (hτ ω))
  have hBτm : Measurable fun ω => B (τ₁ ω) ω := measurable_B_at hBm hBc hτ₁m
  -- the restarted points `Y + σ (B_{t₁} − B_{τ₁})`
  obtain ⟨Ym, hYmd⟩ : ∃ Ym : ℕ → Ω → ℝ, Ym = fun m ω =>
      Y ω + σ * (B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω) := ⟨_, rfl⟩
  have hk_set : ∀ (m i : ℕ) (τ : Ω → ℝ≥0),
      {ω | dyIdx m (τ ω) ≤ i} = {ω | τ ω < (i : ℝ≥0) * (1 / 2 ^ m)} := fun m i τ =>
    Set.ext fun ω => dyIdx_le_iff m i (τ ω)
  have G : ∀ m : ℕ,
      ∫ ω, a ω * (exp (-ρ * (((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))) *
          u (Y ω + σ * (B (((dyIdx m (τ₂ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω))
        - exp (-ρ * (((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))) *
          u (Y ω + σ * (B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω))) ∂P =
      ∫ ω, a ω * (∫ r in (((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))..
          (((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ)), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) ∂P := by
    intro m
    have hk1 : ∀ i : ℕ, MeasurableSet[nat B hBm (i * (1 / 2 ^ m))] {ω | dyIdx m (τ₁ ω) ≤ i} :=
      fun i => by rw [hk_set]; exact hτ₁ _
    have hk2 : ∀ i : ℕ, MeasurableSet[nat B hBm (i * (1 / 2 ^ m))] {ω | dyIdx m (τ₂ ω) ≤ i} :=
      fun i => by rw [hk_set]; exact hτ₂ _
    have ha' : ∀ i : ℕ, Measurable[nat B hBm (i * (1 / 2 ^ m))]
        fun ω => if dyIdx m (τ₁ ω) ≤ i then a ω else 0 := by
      intro i
      simp only [dyIdx_le_iff]
      exact ha _
    have hY' : ∀ i : ℕ, Measurable[nat B hBm (i * (1 / 2 ^ m))]
        fun ω => if dyIdx m (τ₁ ω) ≤ i then Ym m ω else 0 := by
      intro i
      have e : (fun ω => if dyIdx m (τ₁ ω) ≤ i then Ym m ω else 0) = fun ω =>
          (if τ₁ ω < (i : ℝ≥0) * (1 / 2 ^ m) then Y ω else 0) + σ *
            ((if dyIdx m (τ₁ ω) ≤ i then B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω
              else 0) - (if τ₁ ω < (i : ℝ≥0) * (1 / 2 ^ m) then B (τ₁ ω) ω else 0)) := by
        funext ω
        rw [hYmd]
        by_cases hc : dyIdx m (τ₁ ω) ≤ i
        · have hc' := (dyIdx_le_iff m i (τ₁ ω)).1 hc
          simp only [hc, hc', if_true]
        · have hc' : ¬ τ₁ ω < (i : ℝ≥0) * (1 / 2 ^ m) := fun h => hc ((dyIdx_le_iff m i _).2 h)
          simp only [hc, hc', if_false]
          ring
      rw [e]
      exact (hY _).add (measurable_const.mul
        ((meas_grid_val hBm (1 / 2 ^ m) (fun ω => dyIdx m (τ₁ ω)) hk1 i).sub
          (meas_stopped hBm hBc τ₁ hτ₁ _)))
    have hYi' : Integrable (Ym m) P := by
      rw [hYmd]
      have hB1 : Integrable (fun ω => B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω) P :=
        hMi.mono' (measurable_B_at hBm hBc (hkm m τ₁ hτ₁m)).aestronglyMeasurable
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBt m τ₁ hτ₁T ω)
      have hB2 : Integrable (fun ω => B (τ₁ ω) ω) P :=
        hMi.mono' hBτm.aestronglyMeasurable
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBτ ω)
      exact hYi.add ((hB1.sub hB2).const_mul σ)
    have g := grid_dynkin hR hσ hl0 hl2 hB hBm hBc ρ (1 / 2 ^ m) (T * 2 ^ m + 1)
      (fun ω => dyIdx m (τ₁ ω)) (fun ω => dyIdx m (τ₂ ω)) (fun ω => dyIdx_mono m (h12 ω))
      (fun ω => dyIdx_le_nat m T (h2T ω)) hk1 hk2 a (Ym m) ha' hab hY' hYi'
    refine Eq.trans ?_ (g.trans ?_)
    · congr 1
      funext ω
      rw [hYmd]
      try dsimp only
      rw [show Y ω + σ * (B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω) +
          σ * (B (((dyIdx m (τ₂ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω
            - B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω) =
          Y ω + σ * (B (((dyIdx m (τ₂ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω) by ring]
    · congr 1
      funext ω
      rw [hYmd]
      try dsimp only
      congr 1
      refine intervalIntegral.integral_congr fun r _ => ?_
      try dsimp only
      rw [show Y ω + σ * (B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω) +
          σ * (B r.toNNReal ω - B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω) =
          Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω) by ring]
  -- passage to the limit on the left
  set E := exp (|ρ| * ((T : ℝ) + 1)) with hE
  have hlimL : Tendsto (fun m : ℕ =>
      ∫ ω, a ω * (exp (-ρ * (((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))) *
          u (Y ω + σ * (B (((dyIdx m (τ₂ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω))
        - exp (-ρ * (((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))) *
          u (Y ω + σ * (B (((dyIdx m (τ₁ ω) : ℕ) : ℝ≥0) * (1 / 2 ^ m)) ω - B (τ₁ ω) ω))) ∂P)
      atTop (𝓝 (∫ ω, a ω * (exp (-ρ * τ₂ ω) * u (Y ω + σ * (B (τ₂ ω) ω - B (τ₁ ω) ω))
        - exp (-ρ * τ₁ ω) * u (Y ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => 2 * (E * (D * (1 + (|Y ω| + 2 * |σ| * Mx ω))))) (fun m => ?_) ?_
      (fun m => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · have hu := hR.cont.measurable
      refine (ham.mul (((Real.measurable_exp.comp (measurable_const.mul (hkr m τ₂ hτ₂m))).mul
        (hu.comp (hYm.add (((measurable_B_at hBm hBc (hkm m τ₂ hτ₂m)).sub hBτm).const_mul σ)))).sub
        ((Real.measurable_exp.comp (measurable_const.mul (hkr m τ₁ hτ₁m))).mul
        (hu.comp (hYm.add (((measurable_B_at hBm hBc (hkm m τ₁ hτ₁m)).sub hBτm).const_mul
          σ)))))).aestronglyMeasurable
    · exact ((((integrable_const 1).add (hYi.abs.add (hMi.const_mul (2 * |σ|)))).const_mul
        D).const_mul E).const_mul 2
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 := term_bound hl0 (ρ := ρ) (σ := σ) (y := Y ω) (ht0 m (τ₂ ω))
        (htle m _ (h2T ω)) (hBt m τ₂ h2T ω) (hBτ ω)
      have h2 := term_bound hl0 (ρ := ρ) (σ := σ) (y := Y ω) (ht0 m (τ₁ ω))
        (htle m _ (hτ₁T ω)) (hBt m τ₁ hτ₁T ω) (hBτ ω)
      calc |a ω| * |_ - _| ≤ 1 * (|_| + |_|) :=
            mul_le_mul (hab ω) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 1 * (E * (D * (1 + (|Y ω| + 2 * |σ| * Mx ω))) +
              E * (D * (1 + (|Y ω| + 2 * |σ| * Mx ω)))) := by gcongr
        _ = _ := by ring
    · have hc : ∀ (tm : ℕ → ℝ≥0) (t : ℝ≥0), Tendsto tm atTop (𝓝 t) →
          Tendsto (fun m => u (Y ω + σ * (B (tm m) ω - B (τ₁ ω) ω))) atTop
            (𝓝 (u (Y ω + σ * (B t ω - B (τ₁ ω) ω)))) := fun tm t h =>
        (hR.cont.tendsto _).comp (tendsto_const_nhds.add
          (((((hBc ω).tendsto t).comp h).sub tendsto_const_nhds).const_mul σ))
      have he : ∀ (tm : ℕ → ℝ) (t : ℝ), Tendsto tm atTop (𝓝 t) →
          Tendsto (fun m => exp (-ρ * tm m)) atTop (𝓝 (exp (-ρ * t))) := fun tm t h =>
        ((Real.continuous_exp.tendsto _).comp (h.const_mul (-ρ)))
      have := tendsto_const_nhds (x := a ω) |>.mul
        (((he _ _ (tendsto_dyIdx_real (τ₂ ω))).mul (hc _ _ (tendsto_dyIdx (τ₂ ω)))).sub
          ((he _ _ (tendsto_dyIdx_real (τ₁ ω))).mul (hc _ _ (tendsto_dyIdx (τ₁ ω)))))
      rw [sub_self, mul_zero, add_zero] at this
      exact this
  -- passage to the limit on the right
  have hLl : ∀ x, |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ ((σ ^ 2 / 2 + |ρ|) * D) * (1 + |x|) := by
    intro x
    have h1 := hl0 x
    have h2 := hl2 x
    have h3 : |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ σ ^ 2 / 2 * |u2 x| + |ρ| * |u x| := by
      calc |σ ^ 2 / 2 * u2 x - ρ * u x| ≤ |σ ^ 2 / 2 * u2 x| + |ρ * u x| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ ^ 2 / 2)]
    have h4 : 0 ≤ σ ^ 2 / 2 := by positivity
    nlinarith [abs_nonneg ρ, abs_nonneg x, mul_le_mul_of_nonneg_left h2 h4,
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
  have hLm : Measurable fun x => σ ^ 2 / 2 * u2 x - ρ * u x :=
    (measurable_const.mul hR.m2).sub (measurable_const.mul hR.cont.measurable)
  have hii : ∀ ω x y, IntervalIntegrable (fun r => exp (-ρ * r) *
      (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
        - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) volume x y := by
    intro ω x y
    have hp : Continuous fun r : ℝ => Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω) :=
      continuous_const.add (continuous_const.mul
        (((hBc ω).comp continuous_real_toNNReal).sub continuous_const))
    rcases le_total x y with h | h
    · exact intervalIntegrable_path (f := fun x => σ ^ 2 / 2 * u2 x - ρ * u x) hLm hLl hp ρ h
    · exact (intervalIntegrable_path (f := fun x => σ ^ 2 / 2 * u2 x - ρ * u x) hLm hLl hp ρ h).symm
  have hlimR : Tendsto (fun m : ℕ =>
      ∫ ω, a ω * (∫ r in (((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))..
          (((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ)), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) ∂P)
      atTop (𝓝 (∫ ω, a ω * (∫ r in (τ₁ ω : ℝ)..(τ₂ ω), exp (-ρ * r) *
        (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
          - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => ((T : ℝ) + 1) * (E * (((σ ^ 2 / 2 + |ρ|) * D) *
        (1 + (|Y ω| + 2 * |σ| * Mx ω))))) (fun m => ?_) ?_
      (fun m => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · have hBj := measurable_B_joint hBm hBc
      have hFm : Measurable (Function.uncurry fun ω r => exp (-ρ * r) *
          (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
            - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) :=
        (by fun_prop : Measurable fun p : Ω × ℝ => exp (-ρ * p.2)).mul
          (hLm.comp ((hYm.comp measurable_fst).add
            ((hBj.sub (hBτm.comp measurable_fst)).const_mul σ)))
      refine (ham.mul (measurable_interval_integral _ hFm _ _ (hkr m τ₁ hτ₁m) (hkr m τ₂ hτ₂m)
        ((T : ℝ) + 1) (fun ω => ht0 m _) (fun ω => ?_) (fun ω => htle m _ (h2T ω)))).aestronglyMeasurable
      have := dyIdx_mono m (h12 ω)
      gcongr
    · exact ((((integrable_const 1).add (hYi.abs.add (hMi.const_mul (2 * |σ|)))).const_mul
        _).const_mul E).const_mul _
    · rw [Real.norm_eq_abs, abs_mul]
      have hα := ht0 m (τ₁ ω)
      have hβ := htle m _ (h2T ω)
      have hαβ : ((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ) ≤
          ((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ) := by
        have := dyIdx_mono m (h12 ω); gcongr
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const (C := E *
        (((σ ^ 2 / 2 + |ρ|) * D) * (1 + (|Y ω| + 2 * |σ| * Mx ω))))
        (f := fun r => exp (-ρ * r) *
          (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
            - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))))
        (a := ((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))
        (b := ((dyIdx m (τ₂ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ)) (fun r hr => by
          rw [Set.uIoc_of_le hαβ] at hr
          have hr0 : 0 ≤ r := hα.trans hr.1.le
          have hrT : r ≤ (T : ℝ) + 1 := hr.2.trans hβ
          rw [Real.norm_eq_abs]
          refine term_bound (f := fun x => σ ^ 2 / 2 * u2 x - ρ * u x) hLl hr0 hrT ?_ (hBτ ω)
          refine hMb ω _ ?_
          rw [Real.toNNReal_le_iff_le_coe]
          exact_mod_cast hrT)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hαβ)] at hint
      calc |a ω| * |∫ r in _.._, _| ≤ 1 * (E * (((σ ^ 2 / 2 + |ρ|) * D) *
            (1 + (|Y ω| + 2 * |σ| * Mx ω))) * (((dyIdx m (τ₂ ω) : ℕ) : ℝ) *
              ((1 / 2 ^ m : ℝ≥0) : ℝ) - ((dyIdx m (τ₁ ω) : ℕ) : ℝ) * ((1 / 2 ^ m : ℝ≥0) : ℝ))) :=
            mul_le_mul (hab ω) hint (abs_nonneg _) zero_le_one
        _ ≤ 1 * (E * (((σ ^ 2 / 2 + |ρ|) * D) * (1 + (|Y ω| + 2 * |σ| * Mx ω))) *
              ((T : ℝ) + 1)) := by
            have hC : 0 ≤ E * (((σ ^ 2 / 2 + |ρ|) * D) * (1 + (|Y ω| + 2 * |σ| * Mx ω))) := by
              have := (abs_nonneg _).trans (hBτ ω)
              positivity
            gcongr
            linarith
        _ = _ := by ring
    · have hc := intervalIntegral.continuous_primitive (hii ω) 0
      have e : ∀ x y : ℝ, (∫ r in x..y, exp (-ρ * r) *
          (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
            - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) =
          (∫ r in (0:ℝ)..y, exp (-ρ * r) *
            (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
              - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω)))) -
          ∫ r in (0:ℝ)..x, exp (-ρ * r) *
            (σ ^ 2 / 2 * u2 (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))
              - ρ * u (Y ω + σ * (B r.toNNReal ω - B (τ₁ ω) ω))) := fun x y =>
        (intervalIntegral.integral_interval_sub_left (hii ω 0 y) (hii ω 0 x)).symm
      have h1 := tendsto_const_nhds (x := a ω) |>.mul
        (((hc.tendsto _).comp (tendsto_dyIdx_real (τ₂ ω))).sub
          ((hc.tendsto _).comp (tendsto_dyIdx_real (τ₁ ω))))
      rw [e (τ₁ ω) (τ₂ ω)]
      exact h1.congr fun m => congrArg (fun z => a ω * z) (e _ _).symm
  have hfun := funext G
  rw [hfun] at hlimL
  exact tendsto_nhds_unique hlimL hlimR


-- ===== from scratch/probe/2b17c77f_path.lean =====


open ImpulseGames.LinearGame

/-! ## Part D1: pathwise facts about the stage construction -/

lemma exitTime_ge (X : ℝ≥0 → ℝ) (τ : ENNReal) (O : Set ℝ) : τ ≤ exitTime X τ O :=
  le_iInf₂ fun _ hs => hs.1.le

lemma mem_of_lt_exitTime {X : ℝ≥0 → ℝ} {τ : ENNReal} {O : Set ℝ} {s : ℝ≥0}
    (h1 : τ < s) (h2 : (s : ENNReal) < exitTime X τ O) : X s ∈ O := by
  by_contra hX
  exact absurd (iInf₂_le (f := fun (s : ℝ≥0) (_ : τ < (s : ENNReal) ∧ X s ∉ O) => (s : ENNReal))
    s ⟨h1, hX⟩) (not_le.2 h2)

/-- Two paths agreeing after `τ` have the same exit times. -/
lemma exitTime_congr {X X' : ℝ≥0 → ℝ} {τ : ENNReal} {O : Set ℝ}
    (h : ∀ s : ℝ≥0, τ < s → X s = X' s) : exitTime X τ O = exitTime X' τ O := by
  unfold exitTime
  refine iInf_congr fun s => ?_
  by_cases hs : τ < (s : ENNReal)
  · rw [h s hs]
  · simp [hs]

/-- At a finite exit time of an open set, a continuous path is outside the set. -/
lemma exitTime_not_mem {X : ℝ≥0 → ℝ} (hX : Continuous X) {τ : ENNReal} {O : Set ℝ}
    (hO : IsOpen O) (h : exitTime X τ O < ⊤) : X (exitTime X τ O).toNNReal ∉ O := by
  set α := exitTime X τ O with hαdef
  have hα : ((α.toNNReal : ℝ≥0) : ENNReal) = α := ENNReal.coe_toNNReal h.ne
  have hex : ∀ n : ℕ, ∃ s : ℝ≥0, (τ < (s : ENNReal) ∧ X s ∉ O) ∧
      (s : ENNReal) < α + ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) := by
    intro n
    have hlt : α < α + ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) :=
      ENNReal.lt_add_right h.ne (by simp)
    rw [hαdef] at hlt
    conv_lhs at hlt => rw [exitTime]
    obtain ⟨s, hs⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hs1, hs2⟩ := iInf_lt_iff.1 hs
    exact ⟨s, hs1, hs2⟩
  choose s hs using hex
  have hge : ∀ n, α ≤ (s n : ENNReal) := fun n =>
    iInf₂_le (f := fun (s : ℝ≥0) (_ : τ < (s : ENNReal) ∧ X s ∉ O) => (s : ENNReal)) (s n) (hs n).1
  have hlo : ∀ n, α.toNNReal ≤ s n := fun n => by
    have := (ENNReal.toNNReal_le_toNNReal h.ne ENNReal.coe_ne_top).2 (hge n)
    rwa [ENNReal.toNNReal_coe] at this
  have hhi : ∀ n, s n ≤ α.toNNReal + 1 / ((n : ℝ≥0) + 1) := by
    intro n
    have := (hs n).2
    rw [← hα, ← ENNReal.coe_add, ENNReal.coe_lt_coe] at this
    exact this.le
  have hlim : Tendsto s atTop (𝓝 α.toNNReal) := by
    rw [← NNReal.tendsto_coe]
    have h0 : Tendsto (fun n : ℕ => ((α.toNNReal : ℝ≥0) : ℝ) + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (α.toNNReal : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add ((α.toNNReal : ℝ≥0) : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => ?_)
      (fun n => ?_)
    · exact_mod_cast hlo n
    · have := hhi n
      rw [← NNReal.coe_le_coe] at this
      push_cast at this
      exact this
  intro hmem
  have hc : X α.toNNReal ∈ Oᶜ :=
    hO.isClosed_compl.mem_of_tendsto ((hX.tendsto _).comp hlim)
      (Eventually.of_forall fun n => (hs n).1.2)
  exact hc hmem

section Stage
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

lemma stage_zero : stage M φ₁ φ₂ x w 0 =
    { τ := 0, m := .one, δ := 0, x := x, X := fun s => x + M.σ * (w s - w 0) } := rfl

lemma stage_succ_τ (k : ℕ) : (stage M φ₁ φ₂ x w (k + 1)).τ =
    min (exitTime (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ φ₁.C)
      (exitTime (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ φ₂.C) := rfl

lemma stage_succ_m (k : ℕ) : (stage M φ₁ φ₂ x w (k + 1)).m =
    if exitTime (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ φ₁.C ≤
      exitTime (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ φ₂.C then .one else .two := rfl

lemma stage_succ_δ (k : ℕ) : (stage M φ₁ φ₂ x w (k + 1)).δ =
    if (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤ then
      (match (stage M φ₁ φ₂ x w (k + 1)).m with
        | .one => φ₁.ξ ((stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal)
        | .two => φ₂.ξ ((stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal))
    else 0 := rfl

lemma stage_succ_x (k : ℕ) : (stage M φ₁ φ₂ x w (k + 1)).x =
    if (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤ then
      (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal
        + (stage M φ₁ φ₂ x w (k + 1)).δ
    else 0 := rfl

lemma stage_succ_X (k : ℕ) (s : ℝ≥0) : (stage M φ₁ φ₂ x w (k + 1)).X s =
    if (s : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ then (stage M φ₁ φ₂ x w k).X s
    else (stage M φ₁ φ₂ x w (k + 1)).x +
      M.σ * (w s - w (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal) := rfl

lemma stage_tau_mono (k : ℕ) : (stage M φ₁ φ₂ x w k).τ ≤ (stage M φ₁ φ₂ x w (k + 1)).τ := by
  rw [stage_succ_τ]
  exact le_min (exitTime_ge _ _ _) (exitTime_ge _ _ _)

lemma stage_tau_monotone : Monotone fun k => (stage M φ₁ φ₂ x w k).τ :=
  monotone_nat_of_le_succ stage_tau_mono

/-- After its restart time, stage `k` is the free process started at `xₖ`. -/
lemma stage_X_after (k : ℕ) (s : ℝ≥0) (hs : (stage M φ₁ φ₂ x w k).τ ≤ s) :
    (stage M φ₁ φ₂ x w k).X s = (stage M φ₁ φ₂ x w k).x +
      M.σ * (w s - w (stage M φ₁ φ₂ x w k).τ.toNNReal) := by
  rcases k with _ | k
  · simp [stage_zero]
  · rw [stage_succ_X, if_neg (not_lt.2 hs)]

lemma stage_X_before (k : ℕ) (s : ℝ≥0) (hs : (s : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ) :
    (stage M φ₁ φ₂ x w (k + 1)).X s = (stage M φ₁ φ₂ x w k).X s := by
  rw [stage_succ_X, if_pos hs]

/-- The free process of stage `k`. -/
noncomputable def freeX (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (k : ℕ) (s : ℝ≥0) : ℝ :=
  (stage M φ₁ φ₂ x w k).x + M.σ * (w s - w (stage M φ₁ φ₂ x w k).τ.toNNReal)

lemma continuous_freeX (hw : Continuous w) (k : ℕ) : Continuous (freeX M φ₁ φ₂ x w k) := by
  unfold freeX
  fun_prop

lemma exitTime_stage_eq (k : ℕ) (O : Set ℝ) :
    exitTime (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ O =
      exitTime (freeX M φ₁ φ₂ x w k) (stage M φ₁ φ₂ x w k).τ O :=
  exitTime_congr fun s hs => stage_X_after k s hs.le

/-- Between interventions the state stays in both continuation regions. -/
lemma stage_mem_C (k : ℕ) (s : ℝ≥0) (h1 : (stage M φ₁ φ₂ x w k).τ < s)
    (h2 : (s : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ) :
    (stage M φ₁ φ₂ x w k).X s ∈ φ₁.C ∧ (stage M φ₁ φ₂ x w k).X s ∈ φ₂.C := by
  rw [stage_succ_τ, lt_min_iff] at h2
  exact ⟨mem_of_lt_exitTime h1 h2.1, mem_of_lt_exitTime h1 h2.2⟩

/-- The pre-intervention state at a finite intervention time lies outside the intervening
player's continuation region. -/
lemma stage_pre_not_mem (hw : Continuous w) (k : ℕ)
    (hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤) :
    ((stage M φ₁ φ₂ x w (k + 1)).m = .one →
      freeX M φ₁ φ₂ x w k (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal ∉ φ₁.C) ∧
    ((stage M φ₁ φ₂ x w (k + 1)).m = .two →
      freeX M φ₁ φ₂ x w k (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal ∉ φ₂.C) := by
  have hc := continuous_freeX (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) hw k
  rw [stage_succ_m]
  rw [stage_succ_τ] at hτ ⊢
  rw [exitTime_stage_eq, exitTime_stage_eq] at hτ ⊢
  constructor
  · intro hm
    split_ifs at hm with h
    rw [min_eq_left h] at hτ ⊢
    exact exitTime_not_mem hc φ₁.isOpen_C hτ
  · intro hm
    split_ifs at hm with h
    push_neg at h
    rw [min_eq_right h.le] at hτ ⊢
    exact exitTime_not_mem hc φ₂.isOpen_C hτ

end Stage


-- ===== from scratch/probe/2b17c77f_meas.lean =====


open ImpulseGames.LinearGame

/-! ## Part D2: optional-time measurability of exit times and stage data -/

/-- Stopped value at an `ENNReal`-valued optional time. -/
lemma meas_stoppedE {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ENNReal)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[nat B hBm t] {ω | τ ω < t}) (t : ℝ≥0) :
    Measurable[nat B hBm t] fun ω => if τ ω < t then B (τ ω).toNNReal ω else 0 := by
  set τ'' : Ω → ℝ≥0 := fun ω => (min (τ ω) (t : ENNReal)).toNNReal with hτ''
  have hmin_ne : ∀ ω, min (τ ω) (t : ENNReal) ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hlt : ∀ ω (s : ℝ≥0), τ'' ω < s ↔ min (τ ω) (t : ENNReal) < s := fun ω s => by
    simp only [hτ'']
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (hmin_ne ω)]
  have h1 : ∀ s : ℝ≥0, MeasurableSet[nat B hBm s] {ω | τ'' ω < s} := by
    intro s
    by_cases hs : s ≤ t
    · have e : {ω | τ'' ω < s} = {ω | τ ω < s} := by
        ext ω
        simp only [Set.mem_setOf_eq, hlt, min_lt_iff]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd (ENNReal.coe_lt_coe.1 h) (not_lt.2 hs)
        · exact Or.inl
      rw [e]; exact hτ s
    · push_neg at hs
      have e : {ω | τ'' ω < s} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hlt]
        exact lt_of_le_of_lt (min_le_right _ _) (ENNReal.coe_lt_coe.2 hs)
      rw [e]; exact MeasurableSet.univ
  have h2 := meas_stopped hBm hBc τ'' h1 t
  have e : (fun ω => if τ ω < t then B (τ ω).toNNReal ω else 0) =
      fun ω => if τ'' ω < t then B (τ'' ω) ω else 0 := by
    funext ω
    by_cases h : τ ω < t
    · have h' : τ'' ω < t := (hlt ω t).2 (lt_of_le_of_lt (min_le_left _ _) h)
      rw [if_pos h, if_pos h']
      simp only [hτ'', min_eq_left h.le]
    · have h' : ¬ τ'' ω < t := fun h' => by
        rw [hlt, min_lt_iff] at h'
        rcases h' with h' | h'
        · exact h h'
        · exact lt_irrefl _ h'
      rw [if_neg h, if_neg h']
  rw [e]
  exact h2

/-- Pathwise characterisation of `exitTime < t` through rational times (`O` open, `Oᶜ ≠ ∅`). -/
lemma exitTime_lt_iff {X : ℝ≥0 → ℝ} (hX : Continuous X) {O : Set ℝ} (hO : IsOpen O)
    (hne : (Oᶜ).Nonempty) (a : ENNReal) (t : ℝ≥0) :
    exitTime X a O < t ↔ ∃ n : ℕ, ∀ j : ℕ, ∃ q : ℚ,
      (1 / ((n : ℝ≥0) + 1)) < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal + 1 / ((n : ℝ≥0) + 1) < t ∧
      a < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) ∧
      Metric.infDist (X (q : ℝ).toNNReal) Oᶜ < 1 / ((j : ℝ) + 1) := by
  have hg : Continuous fun s => Metric.infDist (X s) Oᶜ :=
    (Metric.continuous_infDist_pt _).comp hX
  have hzero : ∀ s, Metric.infDist (X s) Oᶜ = 0 ↔ X s ∉ O := fun s => by
    rw [← Metric.mem_closure_iff_infDist_zero hne, hO.isClosed_compl.closure_eq]
    rfl
  constructor
  · intro h
    unfold exitTime at h
    obtain ⟨s, hs⟩ := iInf_lt_iff.1 h
    obtain ⟨⟨has, hXs⟩, hst⟩ := iInf_lt_iff.1 hs
    have hst' : s < t := ENNReal.coe_lt_coe.1 hst
    have hatop : a ≠ ⊤ := ne_top_of_lt has
    set a' := a.toNNReal with ha'
    have has' : a' < s := by
      rw [← ENNReal.coe_lt_coe, ha', ENNReal.coe_toNNReal hatop]; exact has
    -- a gap `ε` on both sides
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 3 / ((n : ℝ) + 1) < min ((s : ℝ) - a') ((t : ℝ) - s) := by
      have hpos : 0 < min ((s : ℝ) - a') ((t : ℝ) - s) := lt_min (by
        have := NNReal.coe_lt_coe.2 has'; linarith) (by have := NNReal.coe_lt_coe.2 hst'; linarith)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < min ((s : ℝ) - a') ((t : ℝ) - s) / 3)
      refine ⟨n, ?_⟩
      have : 3 / ((n : ℝ) + 1) = 3 * (1 / ((n : ℝ) + 1)) := by ring
      rw [this]; linarith
    refine ⟨n, fun j => ?_⟩
    have hgs : Metric.infDist (X s) Oᶜ = 0 := (hzero s).2 hXs
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.1 hg s (1 / ((j : ℝ) + 1)) (by positivity)
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) - min δ ε < s by
      have := lt_min hδ hε0; linarith)
    have hmin1 := min_le_left δ ε
    have hmin2 := min_le_right δ ε
    have hm1 : min ((s : ℝ) - a') ((t : ℝ) - s) ≤ (s : ℝ) - a' := min_le_left _ _
    have hm2 : min ((s : ℝ) - a') ((t : ℝ) - s) ≤ (t : ℝ) - s := min_le_right _ _
    have hq0 : (0 : ℝ) ≤ q := by
      have : (0 : ℝ) ≤ a' := NNReal.coe_nonneg _
      have h3 : 3 / ((n : ℝ) + 1) = 3 * ε := by rw [hε]; ring
      linarith
    have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have h3 : 3 / ((n : ℝ) + 1) = 3 * ε := by rw [hε]; ring
    have hεc : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) = ε := by rw [hε]; push_cast; ring
    refine ⟨q, ?_, ?_, ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, hqc, hεc]
      have : (0 : ℝ) ≤ a' := NNReal.coe_nonneg _
      linarith
    · rw [← NNReal.coe_lt_coe]
      push_cast
      rw [hqc]
      have : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) = ε := hεc
      push_cast at this
      rw [this]
      linarith
    · rw [← ENNReal.coe_toNNReal hatop, ENNReal.coe_lt_coe, ← ha', ← NNReal.coe_lt_coe,
        NNReal.coe_sub (by rw [← NNReal.coe_le_coe, hqc, hεc]; linarith), hqc, hεc]
      linarith
    · have hd : dist ((q : ℝ).toNNReal) s < δ := by
        rw [NNReal.dist_eq, hqc, abs_lt]
        constructor <;> linarith
      have := hδg _ hd
      rw [Real.dist_eq, hgs, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at this
      exact this
  · rintro ⟨n, hn⟩
    choose q hq1 hq2 hq3 hq4 using hn
    set ε : ℝ≥0 := 1 / ((n : ℝ≥0) + 1) with hε
    have hatop : a ≠ ⊤ := ne_top_of_lt (hq3 0)
    set a' := a.toNNReal with ha'
    have hlow : ∀ j, a' + ε ≤ (q j : ℝ).toNNReal := by
      intro j
      have h := hq3 j
      rw [← ENNReal.coe_toNNReal hatop, ENNReal.coe_lt_coe, ← ha'] at h
      exact (lt_tsub_iff_right.1 h).le
    have hup : ∀ j, (q j : ℝ).toNNReal ≤ t - ε := fun j =>
      le_tsub_of_add_le_right (hq2 j).le
    obtain ⟨s, hs, φ, hφ, hlim⟩ := (isCompact_Icc (a := a' + ε) (b := t - ε)).tendsto_subseq
      (x := fun j => (q j : ℝ).toNNReal) fun j => ⟨hlow j, hup j⟩
    have hgs : Metric.infDist (X s) Oᶜ = 0 := by
      have hl := ((hg.tendsto s).comp hlim)
      have hl0 : Tendsto (fun j => Metric.infDist (X (q (φ j) : ℝ).toNNReal) Oᶜ) atTop (𝓝 0) := by
        refine squeeze_zero (fun j => Metric.infDist_nonneg) (fun j => (hq4 (φ j)).le) ?_
        exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
      exact tendsto_nhds_unique hl hl0
    have hXs := (hzero s).1 hgs
    have hε0 : 0 < ε := by rw [hε]; positivity
    have has : a < s := by
      rw [← ENNReal.coe_toNNReal hatop, ENNReal.coe_lt_coe, ← ha']
      exact lt_of_lt_of_le (lt_add_of_pos_right _ hε0) hs.1
    have hst : s < t := by
      have ht0 : 0 < t := lt_of_le_of_lt zero_le (hq2 0)
      exact lt_of_le_of_lt hs.2 (tsub_lt_self ht0 hε0)
    refine lt_of_le_of_lt (iInf₂_le (f := fun (s : ℝ≥0) (_ : a < (s : ENNReal) ∧ X s ∉ O) =>
      (s : ENNReal)) s ⟨has, hXs⟩) (ENNReal.coe_lt_coe.2 hst)

/-- Exit times of open sets by continuous processes restarted at an optional time are optional. -/
lemma exit_optional {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ENNReal) (hτ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | τ ω < t})
    (Xf : Ω → ℝ≥0 → ℝ) (hXc : ∀ ω, Continuous (Xf ω))
    (hXm : ∀ s : ℝ≥0, Measurable[𝓕 s] fun ω => if τ ω < s then Xf ω s else 0)
    {O : Set ℝ} (hO : IsOpen O) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | exitTime (Xf ω) (τ ω) O < t} := by
  classical
  by_cases hne : (Oᶜ).Nonempty
  swap
  · have hall : ∀ y, y ∈ O := by
      intro y; by_contra hy; exact hne ⟨y, hy⟩
    have htop : ∀ ω, exitTime (Xf ω) (τ ω) O = ⊤ := by
      intro ω; unfold exitTime; simp [hall]
    have e : {ω | exitTime (Xf ω) (τ ω) O < t} = ∅ := by
      ext ω; simp [htop ω]
    rw [e]; exact @MeasurableSet.empty _ (𝓕 t)
  have e : {ω | exitTime (Xf ω) (τ ω) O < t} = ⋃ n : ℕ, ⋂ j : ℕ, ⋃ q : ℚ,
      {ω | (1 / ((n : ℝ≥0) + 1)) < (q : ℝ).toNNReal ∧
        (q : ℝ).toNNReal + 1 / ((n : ℝ≥0) + 1) < t ∧
        τ ω < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) ∧
        Metric.infDist (if τ ω < (q : ℝ).toNNReal then Xf ω (q : ℝ).toNNReal else 0) Oᶜ
          < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [exitTime_lt_iff (hXc ω) hO hne]
    have hq : ∀ q : ℚ, ∀ n : ℕ, τ ω < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) →
        τ ω < ((q : ℝ).toNNReal : ENNReal) := fun q n h =>
      lt_of_lt_of_le h (ENNReal.coe_le_coe.2 tsub_le_self)
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, fun j => ?_⟩
      obtain ⟨q, h1, h2, h3, h4⟩ := hn j
      exact ⟨q, h1, h2, h3, by rw [if_pos (hq q n h3)]; exact h4⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, fun j => ?_⟩
      obtain ⟨q, h1, h2, h3, h4⟩ := hn j
      exact ⟨q, h1, h2, h3, by rw [if_pos (hq q n h3)] at h4; exact h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_
  by_cases hd : (1 / ((n : ℝ≥0) + 1)) < (q : ℝ).toNNReal ∧
      (q : ℝ).toNNReal + 1 / ((n : ℝ≥0) + 1) < t
  · have htq : (q : ℝ).toNNReal ≤ t := le_trans le_self_add hd.2.le
    have e2 : {ω | (1 / ((n : ℝ≥0) + 1)) < (q : ℝ).toNNReal ∧
        (q : ℝ).toNNReal + 1 / ((n : ℝ≥0) + 1) < t ∧
        τ ω < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) ∧
        Metric.infDist (if τ ω < (q : ℝ).toNNReal then Xf ω (q : ℝ).toNNReal else 0) Oᶜ
          < 1 / ((j : ℝ) + 1)} =
        {ω | τ ω < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal)} ∩
        {ω | Metric.infDist (if τ ω < (q : ℝ).toNNReal then Xf ω (q : ℝ).toNNReal else 0) Oᶜ
          < 1 / ((j : ℝ) + 1)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hd.1, hd.2, true_and]
    rw [e2]
    exact ((𝓕.mono (tsub_le_self.trans htq)) _ (hτ _)).inter ((𝓕.mono htq) _
      (measurableSet_lt ((Metric.continuous_infDist_pt _).measurable.comp (hXm _))
        measurable_const))
  · have e2 : {ω | (1 / ((n : ℝ≥0) + 1)) < (q : ℝ).toNNReal ∧
        (q : ℝ).toNNReal + 1 / ((n : ℝ≥0) + 1) < t ∧
        τ ω < (((q : ℝ).toNNReal - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ENNReal) ∧
        Metric.infDist (if τ ω < (q : ℝ).toNNReal then Xf ω (q : ℝ).toNNReal else 0) Oᶜ
          < 1 / ((j : ℝ) + 1)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hd ⟨h.1, h.2.1⟩
    rw [e2]
    exact @MeasurableSet.empty _ (𝓕 t)

/-- Who intervenes first is decided at the intervention time. -/
lemma first_optional {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (α₁ α₂ : Ω → ENNReal) (h₁ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | α₁ ω < t})
    (h₂ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | α₂ ω < t}) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | min (α₁ ω) (α₂ ω) < t ∧ α₁ ω ≤ α₂ ω} := by
  have e : {ω | min (α₁ ω) (α₂ ω) < t ∧ α₁ ω ≤ α₂ ω} = {ω | α₁ ω < t} \
      ⋃ (q : ℚ) (_ : (q : ℝ).toNNReal < t),
        ({ω | α₂ ω < (q : ℝ).toNNReal} \ {ω | α₁ ω < (q : ℝ).toNNReal}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion, not_exists, not_and, not_not]
    constructor
    · rintro ⟨hmin, hle⟩
      refine ⟨lt_of_le_of_lt (le_of_eq (min_eq_left hle).symm) hmin, fun q _ hq2 => ?_⟩
      exact lt_of_le_of_lt hle hq2
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_lt (min_le_left _ _) h1, ?_⟩
      by_contra hlt
      push_neg at hlt
      obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      have := h2 q (ENNReal.coe_lt_coe.1 (lt_trans hq2 h1)) hq1
      exact lt_irrefl _ (lt_trans this hq2)
  rw [e]
  refine (h₁ t).diff (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
  exact (𝓕.mono hq.le _ (h₂ _)).diff (𝓕.mono hq.le _ (h₁ _))


-- ===== from scratch/probe/2b17c77f_meas2.lean =====


open ImpulseGames.LinearGame

/-- **Stage data are optional / adapted** (induction on the stage): `{τₖ < t} ∈ 𝓕ₜ` and
`1{τₖ < t} xₖ` is `𝓕ₜ`-measurable, for any pair of strategies. -/
theorem stage_optional {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (k : ℕ) :
    (∀ t : ℝ≥0, MeasurableSet[nat B hBm t]
      {ω | (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t}) ∧
    (∀ t : ℝ≥0, Measurable[nat B hBm t] fun ω =>
      if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t then (stage M φ₁ φ₂ x (fun s => B s ω) k).x
      else 0) := by
  classical
  have hBn : ∀ s, Measurable[nat B hBm s] (B s) := fun s =>
    (Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) s).measurable
  induction k with
  | zero =>
    refine ⟨fun t => ?_, fun t => ?_⟩
    · by_cases h : (0 : ENNReal) < t
      · have e : {ω | (stage M φ₁ φ₂ x (fun s => B s ω) 0).τ < t} = Set.univ := by
          ext ω; simp [stage_zero, h]
        rw [e]; exact @MeasurableSet.univ _ (nat B hBm t)
      · have e : {ω | (stage M φ₁ φ₂ x (fun s => B s ω) 0).τ < t} = ∅ := by
          ext ω; simp [stage_zero, h]
        rw [e]; exact @MeasurableSet.empty _ (nat B hBm t)
    · simp only [stage_zero]
      by_cases h : (0 : ENNReal) < t
      · simp only [h, if_true]
        exact @measurable_const _ _ _ (nat B hBm t) _
      · simp only [h, if_false]
        exact @measurable_const _ _ _ (nat B hBm t) _
  | succ k ih =>
    obtain ⟨hτk, hxk⟩ := ih
    set Xf : Ω → ℝ≥0 → ℝ := fun ω => freeX M φ₁ φ₂ x (fun s => B s ω) k with hXf
    have hXc : ∀ ω, Continuous (Xf ω) := fun ω => continuous_freeX (hBc ω) k
    have hXm : ∀ s : ℝ≥0, Measurable[nat B hBm s] fun ω =>
        if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < s then Xf ω s else 0 := by
      intro s
      have e : (fun ω => if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < s then Xf ω s else 0) =
          fun ω => (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < s then
              (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) + M.σ *
            ((if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < s then B s ω else 0) -
              (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < s then
                B (stage M φ₁ φ₂ x (fun s => B s ω) k).τ.toNNReal ω else 0)) := by
        funext ω
        simp only [hXf, freeX]
        split_ifs <;> ring
      rw [e]
      exact (hxk s).add (measurable_const.mul ((Measurable.ite (hτk s) (hBn s)
        measurable_const).sub (meas_stoppedE hBm hBc _ hτk s)))
    have hα : ∀ (O : Set ℝ), IsOpen O → ∀ t : ℝ≥0, MeasurableSet[nat B hBm t]
        {ω | exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ O < t} :=
      fun O hO t => exit_optional (nat B hBm) _ hτk Xf hXc hXm hO t
    have hτe : ∀ ω, (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ =
        min (exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₁.C)
          (exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₂.C) := fun ω => by
      rw [stage_succ_τ, exitTime_stage_eq, exitTime_stage_eq]
    have hτ1 : ∀ t : ℝ≥0, MeasurableSet[nat B hBm t]
        {ω | (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t} := by
      intro t
      have e : {ω | (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t} =
          {ω | exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₁.C < t} ∪
          {ω | exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₂.C < t} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_union, hτe ω, min_lt_iff]
      rw [e]
      exact (hα _ φ₁.isOpen_C t).union (hα _ φ₂.isOpen_C t)
    refine ⟨hτ1, fun t => ?_⟩
    -- the pre-intervention state, cut off at `t`
    set Pt : Ω → ℝ := fun ω => if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then
      Xf ω (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ.toNNReal else 0 with hPt
    have hPm : Measurable[nat B hBm t] Pt := by
      have e : Pt = fun ω =>
          (if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then (1 : ℝ) else 0) *
            (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t then
              (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) + M.σ *
          ((if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then
              B (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ.toNNReal ω else 0) -
            (if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then (1 : ℝ) else 0) *
            (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t then
              B (stage M φ₁ φ₂ x (fun s => B s ω) k).τ.toNNReal ω else 0)) := by
        funext ω
        simp only [hPt, hXf, freeX]
        by_cases h : (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t
        · have hk : (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t :=
            lt_of_le_of_lt (stage_tau_mono k) h
          rw [if_pos h, if_pos h, if_pos h, if_pos hk, if_pos hk]
          ring
        · rw [if_neg h, if_neg h, if_neg h]
          ring
      rw [e]
      exact ((Measurable.ite (hτ1 t) measurable_const measurable_const).mul (hxk t)).add
        (measurable_const.mul ((meas_stoppedE hBm hBc _ hτ1 t).sub
          ((Measurable.ite (hτ1 t) measurable_const measurable_const).mul
            (meas_stoppedE hBm hBc _ hτk t))))
    set A : Set Ω := {ω | min (exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₁.C)
        (exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₂.C) < t ∧
      exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₁.C ≤
        exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₂.C} with hA
    have hAm : MeasurableSet[nat B hBm t] A :=
      first_optional (nat B hBm) _ _ (hα _ φ₁.isOpen_C) (hα _ φ₂.isOpen_C) t
    have e : (fun ω => if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then
        (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).x else 0) = fun ω =>
        if (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t then
          Pt ω + (if ω ∈ A then φ₁.ξ (Pt ω) else φ₂.ξ (Pt ω)) else 0 := by
      funext ω
      by_cases h : (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < t
      · have htop : (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ < ⊤ :=
          lt_trans h ENNReal.coe_lt_top
        have hpre : (stage M φ₁ φ₂ x (fun s => B s ω) k).X
            (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ.toNNReal =
            Xf ω (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ.toNNReal :=
          stage_X_after k _ (by rw [ENNReal.coe_toNNReal htop.ne]; exact stage_tau_mono k)
        have hPω : Pt ω = Xf ω (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ.toNNReal := by
          simp only [hPt]; rw [if_pos h]
        rw [if_pos h, if_pos h, stage_succ_x, if_pos htop, stage_succ_δ, if_pos htop, hpre, hPω]
        rw [stage_succ_m, exitTime_stage_eq, exitTime_stage_eq]
        by_cases hc : exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₁.C ≤
            exitTime (Xf ω) (stage M φ₁ φ₂ x (fun s => B s ω) k).τ φ₂.C
        · have hAω : ω ∈ A := ⟨by rw [← hτe ω]; exact h, hc⟩
          rw [if_pos hc, if_pos hAω]
        · have hAω : ω ∉ A := fun hω => hc hω.2
          rw [if_neg hc, if_neg hAω]
      · rw [if_neg h, if_neg h]
    rw [e]
    exact Measurable.ite (hτ1 t) (hPm.add (Measurable.ite hAm
      (φ₁.continuous_ξ.measurable.comp hPm) (φ₂.continuous_ξ.measurable.comp hPm)))
      measurable_const

/-- Strict comparison of optional times, before `t`. -/
lemma lt_optional {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (α β : Ω → ENNReal) (hα : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | α ω < t})
    (hβ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | β ω < t}) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | α ω < β ω ∧ α ω < t} := by
  have e : {ω | α ω < β ω ∧ α ω < t} = ⋃ (q : ℚ) (_ : (q : ℝ).toNNReal < t),
      ({ω | α ω < (q : ℝ).toNNReal} \ {ω | β ω < (q : ℝ).toNNReal}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_min h1 h2)
      exact ⟨q, ENNReal.coe_lt_coe.1 (lt_of_lt_of_le hq2 (min_le_right _ _)), hq1,
        (lt_of_lt_of_le hq2 (min_le_left _ _)).le⟩
    · rintro ⟨q, hqt, hq1, hq2⟩
      exact ⟨lt_of_lt_of_le hq1 hq2, lt_trans hq1 (ENNReal.coe_lt_coe.2 hqt)⟩
  rw [e]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
    (𝓕.mono hq.le _ (hα _)).diff (𝓕.mono hq.le _ (hβ _))

/-- Truncating an optional time at a deterministic level keeps it optional. -/
lemma trunc_optional {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ENNReal) (hτ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | τ ω < t}) (T : ℝ≥0)
    (t : ℝ≥0) : MeasurableSet[𝓕 t] {ω | (min (τ ω) (T : ENNReal)).toNNReal < t} := by
  have hmin_ne : ∀ ω, min (τ ω) (T : ENNReal) ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hlt : ∀ ω, (min (τ ω) (T : ENNReal)).toNNReal < t ↔ min (τ ω) (T : ENNReal) < t :=
    fun ω => by rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (hmin_ne ω)]
  by_cases hs : t ≤ T
  · have e : {ω | (min (τ ω) (T : ENNReal)).toNNReal < t} = {ω | τ ω < t} := by
      ext ω
      simp only [Set.mem_setOf_eq, hlt, min_lt_iff]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd (ENNReal.coe_lt_coe.1 h) (not_lt.2 hs)
      · exact Or.inl
    rw [e]; exact hτ t
  · push_neg at hs
    have e : {ω | (min (τ ω) (T : ENNReal)).toNNReal < t} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hlt]
      exact lt_of_le_of_lt (min_le_right _ _) (ENNReal.coe_lt_coe.2 hs)
    rw [e]; exact @MeasurableSet.univ _ (𝓕 t)


-- ===== from scratch/probe/2b17c77f_path2.lean =====


open ImpulseGames.LinearGame

/-! ## Part D1b: the controlled process between interventions -/

section Ctrl
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

/-- Later stages do not change the past before their own restart time. -/
lemma stage_X_stable (k : ℕ) (s : ℝ≥0) (h2 : (s : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ) :
    ∀ j, k ≤ j → (stage M φ₁ φ₂ x w j).X s = (stage M φ₁ φ₂ x w k).X s := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
    have hτ : (stage M φ₁ φ₂ x w (k + 1)).τ ≤ (stage M φ₁ φ₂ x w (j + 1)).τ :=
      stage_tau_monotone (by omega)
    rw [stage_X_before j s (lt_of_lt_of_le h2 hτ), ih]

lemma le_kbar (k : ℕ) (h : (stage M φ₁ φ₂ x w k).τ < ⊤) : (k : ℕ∞) ≤ kbar M φ₁ φ₂ x w :=
  le_sSup ⟨k, h, rfl⟩

/-- **The controlled process is the stage-`k` process on `[τₖ, τₖ₊₁)`.** -/
lemma ctrlX_eq_stage (k : ℕ) (s : ℝ≥0) (h1 : (stage M φ₁ φ₂ x w k).τ ≤ s)
    (h2 : (s : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ) :
    ctrlX M φ₁ φ₂ x w s = (stage M φ₁ φ₂ x w k).X s := by
  have hk : (k : ℕ∞) ≤ kbar M φ₁ φ₂ x w := le_kbar k (lt_of_le_of_lt h1 ENNReal.coe_lt_top)
  have hst := stage_X_stable (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) k s h2
  unfold ctrlX
  split_ifs with hK
  · apply hst
    have : ((kbar M φ₁ φ₂ x w).toNat : ℕ∞) = kbar M φ₁ φ₂ x w := ENat.coe_toNat hK.ne
    rw [← this] at hk
    exact_mod_cast hk
  · have ht : Tendsto (fun j => (stage M φ₁ φ₂ x w j).X s) atTop
        (𝓝 ((stage M φ₁ φ₂ x w k).X s)) :=
      tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨k, fun j hj => (hst j hj).symm⟩)
    exact ht.limUnder_eq

end Ctrl


-- ===== from scratch/probe/2b17c77f_sd.lean =====


open ImpulseGames.LinearGame

/-! ## Part D2b: Dynkin's formula on one stage of the controlled game, truncated at `T` -/

/-- **Stage Dynkin formula.** With `σ₁ = τₖ ∧ T`, `σ₂ = τₖ₊₁ ∧ T` and the start
`Y = xₖ 1{τₖ < τₖ₊₁, τₖ < T}` (non-transient stages started before `T`). -/
theorem stage_dynkin {u u1 u2 : ℝ → ℝ} {S : Set ℝ} {C K D : ℝ} (M : Model) (hσ : M.σ ≠ 0)
    (hR : Reg u u1 u2 S C K)
    (hl0 : ∀ x, |u x| ≤ D * (1 + |x|)) (hl2 : ∀ x, |u2 x| ≤ D * (1 + |x|))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (k T : ℕ)
    (hYi : Integrable (fun ω => if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
        (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
        (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
          (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) P) :
    ∫ ω, (exp (-M.ρ * ((min (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ((T : ℝ≥0) : ENNReal)).toNNReal
            : ℝ)) *
          u ((if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
              (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
              (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
                (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) + M.σ *
            (B (min (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ((T : ℝ≥0) : ENNReal)).toNNReal ω
              - B (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal ω))
        - exp (-M.ρ * ((min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal
            : ℝ)) *
          u (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
              (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
              (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
                (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0)) ∂P =
      ∫ ω, (∫ r in ((min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal
            : ℝ)..((min (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ
              ((T : ℝ≥0) : ENNReal)).toNNReal : ℝ),
          exp (-M.ρ * r) *
          (M.σ ^ 2 / 2 * u2 ((if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
              (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
              (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
                (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) + M.σ * (B r.toNNReal ω -
              B (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal ω))
            - M.ρ * u ((if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
              (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
              (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
                (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) + M.σ * (B r.toNNReal ω -
              B (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal ω))))
        ∂P := by
  classical
  obtain ⟨hτk, hxk⟩ := stage_optional hBm hBc M φ₁ φ₂ x k
  obtain ⟨hτk1, -⟩ := stage_optional hBm hBc M φ₁ φ₂ x (k + 1)
  have hT := trunc_optional (nat B hBm) _ hτk (T : ℝ≥0)
  have hT1 := trunc_optional (nat B hBm) _ hτk1 (T : ℝ≥0)
  have hmin_ne : ∀ (a : ENNReal), min a ((T : ℝ≥0) : ENNReal) ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have h12 : ∀ ω, (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal ≤
      (min (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ((T : ℝ≥0) : ENNReal)).toNNReal :=
    fun ω => ENNReal.toNNReal_mono (hmin_ne _) (min_le_min_right _ (stage_tau_mono k))
  have h2T : ∀ ω, (min (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ
      ((T : ℝ≥0) : ENNReal)).toNNReal ≤ ((T : ℕ) : ℝ≥0) := fun ω => by
    have := ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_right
      (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ((T : ℝ≥0) : ENNReal))
    simpa using this
  have hlt : ∀ ω (t : ℝ≥0),
      (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal < t ↔
      min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal) < t := fun ω t => by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (hmin_ne _)]
  have ha : ∀ t : ℝ≥0, Measurable[nat B hBm t] fun ω =>
      if (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal < t then
        (1 : ℝ) else 0 := fun t =>
    Measurable.ite (hT t) measurable_const measurable_const
  have hY : ∀ t : ℝ≥0, Measurable[nat B hBm t] fun ω =>
      if (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal < t then
        (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
            (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
            (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
          (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) else 0 := by
    intro t
    set t' : ℝ≥0 := min t (T : ℝ≥0) with ht'
    have e : (fun ω =>
        if (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal < t then
          (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
              (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
              (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
            (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) else 0) = fun ω =>
        if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
            (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
            (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t' then
          (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < t' then
            (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) else 0 := by
      funext ω
      have hc : ((t' : ℝ≥0) : ENNReal) = min (t : ENNReal) ((T : ℝ≥0) : ENNReal) := by
        rw [ht', ENNReal.coe_min]
      simp only [hlt, hc, min_lt_iff, lt_min_iff]
      by_cases ha : (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (t : ENNReal) <;>
      by_cases hb : (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < ((T : ℝ≥0) : ENNReal) <;>
      by_cases hd : (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
        (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ <;>
      by_cases hT : ((T : ℝ≥0) : ENNReal) < (t : ENNReal) <;>
      simp only [ha, hb, hd, hT, true_or, or_true, true_and, and_true, false_and, and_false,
        or_false, false_or, if_true, if_false] <;>
      first
        | rfl
        | exact absurd (lt_trans hb hT) ha
    rw [e]
    have hle : nat B hBm t' ≤ nat B hBm t := (nat B hBm).mono (min_le_left _ _)
    exact (Measurable.ite (lt_optional (nat B hBm) _ _ hτk hτk1 t') (hxk t')
      measurable_const).mono hle le_rfl
  have hY' : ∀ t : ℝ≥0, Measurable[nat B hBm t] fun ω =>
      if (min (stage M φ₁ φ₂ x (fun s => B s ω) k).τ ((T : ℝ≥0) : ENNReal)).toNNReal < t then
        (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ <
            (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
            (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ℝ≥0) then
          (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) else 0 := hY
  have h := opt_dynkin hR hσ hl0 hl2 hB hBm hBc M.ρ T _ _ h12 h2T hT hT1
    (fun _ => (1 : ℝ)) _ ha (fun _ => by simp) hY' hYi
  simp only [one_mul] at h
  exact h


-- ===== from scratch/probe/2b17c77f_d1b.lean =====


open ImpulseGames.LinearGame

/-! ## Part D1b: interventions, reindexing of the player sums, accumulation of stages -/

section D1b
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

lemma valid_iff (p : ℕ → Prop) (k : ℕ) :
    ((k + 1 : ℕ) : ℕ∞) ≤ {l | p l}.encard ↔
      ∀ hf : (Set.ofPred p).Finite, k < Finset.card hf.toFinset := by
  rcases (Set.ofPred p).finite_or_infinite with hf | hf
  · have he : {l | p l}.encard = (Finset.card hf.toFinset : ℕ∞) :=
      Set.Finite.encard_eq_coe_toFinset_card hf
    rw [he]
    constructor
    · intro h _
      have : k + 1 ≤ Finset.card hf.toFinset := by exact_mod_cast h
      omega
    · intro h
      have := h hf
      exact_mod_cast (show k + 1 ≤ Finset.card hf.toFinset by omega)
  · have he : {l | p l}.encard = ⊤ := Set.encard_eq_top_iff.2 hf
    rw [he]
    exact ⟨fun _ hf' => absurd hf' hf, fun _ => le_top⟩

lemma tauP_succ (i : Player) (k : ℕ) : tauP M φ₁ φ₂ x w i (k + 1) =
    if ((k + 1 : ℕ) : ℕ∞) ≤ kbarP M φ₁ φ₂ x w i then
      (stage M φ₁ φ₂ x w (Nat.nth (intervenes M φ₁ φ₂ x w i) k)).τ else ⊤ := by
  simp only [tauP, etaIdx, Nat.add_sub_cancel]

lemma deltaP_succ (i : Player) (k : ℕ) : deltaP M φ₁ φ₂ x w i (k + 1) =
    if ((k + 1 : ℕ) : ℕ∞) ≤ kbarP M φ₁ φ₂ x w i then
      (stage M φ₁ φ₂ x w (Nat.nth (intervenes M φ₁ φ₂ x w i) k)).δ else 0 := by
  simp only [deltaP, etaIdx, Nat.add_sub_cancel]

/-- **Reindexing.** A sum over the interventions of player `i` written with `τ_{i,k}, δ_{i,k}`
equals the sum over the stages at which player `i` intervenes. -/
lemma valid_iff_kbarP (i : Player) (k : ℕ) :
    ((k + 1 : ℕ) : ℕ∞) ≤ kbarP M φ₁ φ₂ x w i ↔
      ∀ hf : (Set.ofPred (intervenes M φ₁ φ₂ x w i)).Finite, k < Finset.card hf.toFinset :=
  valid_iff _ k

open Classical in
theorem tsum_tauP (i : Player) (F : ENNReal → ℝ → ℝ) (hF : F ⊤ 0 = 0) :
    ∑' k : ℕ, F (tauP M φ₁ φ₂ x w i (k + 1)) (deltaP M φ₁ φ₂ x w i (k + 1)) =
      ∑' l : ℕ, if intervenes M φ₁ φ₂ x w i l then
        F (stage M φ₁ φ₂ x w l).τ (stage M φ₁ φ₂ x w l).δ else 0 := by
  set p := intervenes M φ₁ φ₂ x w i with hp
  set g : ℕ → ℝ := fun k => F (tauP M φ₁ φ₂ x w i (k + 1)) (deltaP M φ₁ φ₂ x w i (k + 1))
    with hg
  set f : ℕ → ℝ := fun l => if p l then
    F (stage M φ₁ φ₂ x w l).τ (stage M φ₁ φ₂ x w l).δ else 0 with hfdef
  have hvalid : ∀ k, g k ≠ 0 → ∀ hf : (Set.ofPred p).Finite, k < Finset.card hf.toFinset := by
    intro k hk
    rw [hp, ← valid_iff_kbarP]
    by_contra hc
    apply hk
    simp only [hg]
    rw [tauP_succ, deltaP_succ, if_neg hc, if_neg hc, hF]
  have hgval : ∀ k, (∀ hf : (Set.ofPred p).Finite, k < Finset.card hf.toFinset) →
      g k = f (Nat.nth p k) := by
    intro k hk
    have hk' := (valid_iff_kbarP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i k).2 hk
    simp only [hg, hfdef]
    rw [tauP_succ, deltaP_succ, if_pos hk', if_pos hk', if_pos (Nat.nth_mem k hk)]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij (fun k : Function.support g => Nat.nth p k.1) ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only at hab
    have hva := hvalid a ha
    have hvb := hvalid b hb
    rcases (Set.ofPred p).finite_or_infinite with hfin | hinf
    · exact Subtype.ext (Nat.nth_injOn hfin (hva hfin) (hvb hfin) hab)
    · exact Subtype.ext ((Nat.nth_strictMono hinf).injective hab)
  · intro l hl
    have hpl : p l := by
      by_contra hc
      exact hl (by simp only [hfdef, if_neg hc])
    obtain ⟨n, hn, hnl⟩ := Nat.exists_lt_card_nth_eq hpl
    refine ⟨⟨n, ?_⟩, hnl⟩
    show g n ≠ 0
    rw [hgval n hn, hnl]
    exact hl
  · rintro ⟨k, hk⟩
    exact (hgval k (hvalid k hk)).symm

/-- Every finite stage time `l ≥ 1` is an intervention of one of the two players. -/
lemma intervenes_or (l : ℕ) (hl : 1 ≤ l) (h : (stage M φ₁ φ₂ x w l).τ < ⊤) :
    intervenes M φ₁ φ₂ x w .one l ∨ intervenes M φ₁ φ₂ x w .two l := by
  rcases hm : (stage M φ₁ φ₂ x w l).m with _ | _
  · exact Or.inl ⟨hl, h, hm⟩
  · exact Or.inr ⟨hl, h, hm⟩

/-- **No accumulation of stages.** If both players' intervention times tend to `∞`, so do the
stage times. -/
theorem stage_tau_tendsto
    (h : ∀ i, Tendsto (fun k => tauP M φ₁ φ₂ x w i k) atTop (𝓝 ⊤)) :
    Tendsto (fun K => (stage M φ₁ φ₂ x w K).τ) atTop (𝓝 ⊤) := by
  classical
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro T
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hle : ∀ K, (stage M φ₁ φ₂ x w K).τ ≤ T := by
    intro K
    obtain ⟨K', hK', hK'T⟩ := Filter.frequently_atTop.1 hne K
    exact (stage_tau_monotone hK').trans (not_lt.1 hK'T)
  have hfin : ∀ K, (stage M φ₁ φ₂ x w K).τ < ⊤ := fun K =>
    lt_of_le_of_lt (hle K) ENNReal.coe_lt_top
  have hinf : ({l | intervenes M φ₁ φ₂ x w .one l} ∪
      {l | intervenes M φ₁ φ₂ x w .two l}).Infinite := by
    refine Set.Infinite.mono (s := Set.Ici 1) ?_ (Set.Ici_infinite 1)
    intro l hl
    exact intervenes_or l hl (hfin l)
  have key : ∀ i : Player, ({l | intervenes M φ₁ φ₂ x w i l}).Infinite → False := by
    intro i hi
    have hall : ∀ k, tauP M φ₁ φ₂ x w i (k + 1) ≤ T := by
      intro k
      rw [tauP_succ, kbarP, Set.encard_eq_top_iff.2 hi, if_pos le_top]
      exact hle _
    obtain ⟨k, hk⟩ := ((h i).eventually (lt_mem_nhds (ENNReal.coe_lt_top (r := T)))).exists_forall_of_atTop
    exact absurd (hall k) (not_le.2 (hk (k + 1) (Nat.le_succ k)))
  rcases Set.infinite_union.1 hinf with h1 | h2
  · exact key _ h1
  · exact key _ h2

end D1b


-- ===== from scratch/probe/2b17c77f_d1c.lean =====


open ImpulseGames.LinearGame

/-! ## Part D1c: summability transfer for the reindexing -/

section D1c
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

open Classical in
theorem hasSum_tauP_iff (i : Player) (F : ENNReal → ℝ → ℝ) (hF : F ⊤ 0 = 0) :
    ∀ a : ℝ, HasSum (fun l : ℕ => if intervenes M φ₁ φ₂ x w i l then
        F (stage M φ₁ φ₂ x w l).τ (stage M φ₁ φ₂ x w l).δ else 0) a ↔
      HasSum (fun k : ℕ => F (tauP M φ₁ φ₂ x w i (k + 1)) (deltaP M φ₁ φ₂ x w i (k + 1))) a := by
  intro a
  set p := intervenes M φ₁ φ₂ x w i with hp
  set g : ℕ → ℝ := fun k => F (tauP M φ₁ φ₂ x w i (k + 1)) (deltaP M φ₁ φ₂ x w i (k + 1))
    with hg
  set f : ℕ → ℝ := fun l => if p l then
    F (stage M φ₁ φ₂ x w l).τ (stage M φ₁ φ₂ x w l).δ else 0 with hfdef
  have hvalid : ∀ k, g k ≠ 0 → ∀ hf : (Set.ofPred p).Finite, k < Finset.card hf.toFinset := by
    intro k hk
    rw [hp, ← valid_iff_kbarP]
    by_contra hc
    apply hk
    simp only [hg]
    rw [tauP_succ, deltaP_succ, if_neg hc, if_neg hc, hF]
  have hgval : ∀ k, (∀ hf : (Set.ofPred p).Finite, k < Finset.card hf.toFinset) →
      g k = f (Nat.nth p k) := by
    intro k hk
    have hk' := (valid_iff_kbarP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i k).2 hk
    simp only [hg, hfdef]
    rw [tauP_succ, deltaP_succ, if_pos hk', if_pos hk', if_pos (Nat.nth_mem k hk)]
  refine hasSum_iff_hasSum_of_ne_zero_bij (fun k : Function.support g => Nat.nth p k.1) ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only at hab
    have hva := hvalid a ha
    have hvb := hvalid b hb
    rcases (Set.ofPred p).finite_or_infinite with hfin | hinf
    · exact Subtype.ext (Nat.nth_injOn hfin (hva hfin) (hvb hfin) hab)
    · exact Subtype.ext ((Nat.nth_strictMono hinf).injective hab)
  · intro l hl
    have hpl : p l := by
      by_contra hc
      exact hl (by simp only [hfdef, if_neg hc])
    obtain ⟨n, hn, hnl⟩ := Nat.exists_lt_card_nth_eq hpl
    refine ⟨⟨n, ?_⟩, hnl⟩
    show g n ≠ 0
    rw [hgval n hn, hnl]
    exact hl
  · rintro ⟨k, hk⟩
    exact (hgval k (hvalid k hk)).symm

open Classical in
theorem summable_tauP_iff (i : Player) (F : ENNReal → ℝ → ℝ) (hF : F ⊤ 0 = 0) :
    Summable (fun k : ℕ => F (tauP M φ₁ φ₂ x w i (k + 1)) (deltaP M φ₁ φ₂ x w i (k + 1))) ↔
      Summable (fun l : ℕ => if intervenes M φ₁ φ₂ x w i l then
        F (stage M φ₁ φ₂ x w l).τ (stage M φ₁ φ₂ x w l).δ else 0) :=
  ⟨fun ⟨a, h⟩ => ⟨a, (hasSum_tauP_iff i F hF a).2 h⟩,
    fun ⟨a, h⟩ => ⟨a, (hasSum_tauP_iff i F hF a).1 h⟩⟩

end D1c


-- ===== from scratch/probe/2b17c77f_fat.lean =====


/-! ## Part F: Fatou's lemma with an integrable lower bound (real-valued form) -/

theorem fatou_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : ℕ → Ω → ℝ} {f H : Ω → ℝ} {c : ℝ}
    (hU : ∀ n, Integrable (U n) P) (hH : Integrable H P) (hf : Integrable f P)
    (hlow : ∀ n, ∀ᵐ ω ∂P, -H ω ≤ U n ω)
    (hlim : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f ω - ε ≤ U n ω)
    (hb : ∀ n, ∫ ω, U n ω ∂P ≤ c) : ∫ ω, f ω ∂P ≤ c := by
  classical
  have hcH : 0 ≤ c + ∫ ω, H ω ∂P := by
    have h1 : ∫ ω, -H ω ∂P ≤ ∫ ω, U 0 ω ∂P := integral_mono_ae hH.neg (hU 0) (hlow 0)
    rw [integral_neg] at h1
    linarith [hb 0]
  set V : ℕ → Ω → ℝ := fun n ω => U n ω + H ω with hVdef
  have hV : ∀ n, Integrable (V n) P := fun n => (hU n).add hH
  have hV0 : ∀ n, 0 ≤ᵐ[P] V n := fun n => (hlow n).mono fun ω h => by
    simp only [hVdef, Pi.zero_apply]
    linarith
  have hVb : ∀ n, ∫⁻ ω, ENNReal.ofReal (V n ω) ∂P ≤ ENNReal.ofReal (c + ∫ ω, H ω ∂P) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hV n) (hV0 n)]
    apply ENNReal.ofReal_le_ofReal
    simp only [hVdef]
    rw [integral_add (hU n) hH]
    linarith [hb n]
  set g : Ω → ℝ := fun ω => f ω + H ω with hgdef
  have hg : Integrable g P := hf.add hH
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (g ω) ≤
      Filter.liminf (fun n => ENNReal.ofReal (V n ω)) atTop := by
    filter_upwards [hlim] with ω hω
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hev : ∀ᶠ n in atTop, ENNReal.ofReal (g ω) - (ε : ENNReal) ≤ ENNReal.ofReal (V n ω) := by
      filter_upwards [hω ε (by exact_mod_cast hε)] with n hn
      rw [tsub_le_iff_right]
      calc ENNReal.ofReal (g ω) ≤ ENNReal.ofReal (V n ω + ε) := by
            apply ENNReal.ofReal_le_ofReal
            simp only [hgdef, hVdef]
            linarith
        _ ≤ ENNReal.ofReal (V n ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (V n ω) + (ε : ENNReal) := by rw [ENNReal.ofReal_coe_nnreal]
    have := Filter.le_liminf_of_le (f := atTop) (u := fun n => ENNReal.ofReal (V n ω)) (by isBoundedDefault) hev
    exact tsub_le_iff_right.1 this
  have hlint : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal (c + ∫ ω, H ω ∂P) := by
    calc ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
        ≤ ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal (V n ω)) atTop ∂P := lintegral_mono_ae hpt
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (V n ω) ∂P) atTop :=
          lintegral_liminf_le' fun n => (hV n).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (c + ∫ ω, H ω ∂P) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hVb)
  have hgle : ∫ ω, g ω ∂P ≤ c + ∫ ω, H ω ∂P := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
    have h1 := ENNReal.toReal_le_of_le_ofReal hcH hlint
    have h2 : 0 ≤ (∫⁻ ω, ENNReal.ofReal (-g ω) ∂P).toReal := ENNReal.toReal_nonneg
    linarith
  have : ∫ ω, g ω ∂P = ∫ ω, f ω ∂P + ∫ ω, H ω ∂P := integral_add hf hH
  linarith


-- ===== from scratch/probe/2b17c77f_tele.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3a: the pathwise telescoping identity over one stage -/

section Tele
variable (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ) (T : ℝ≥0)

/-- `σₖ = τₖ ∧ T`. -/
noncomputable def sg (k : ℕ) : ℝ≥0 := (min (stage M φ₁ φ₂ x w k).τ (T : ENNReal)).toNNReal

/-- The start `Y = xₖ 1{τₖ < τₖ₊₁, τₖ < T}` of the Dynkin step on stage `k`. -/
noncomputable def Ys (k : ℕ) : ℝ :=
  if (stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ ∧
      (stage M φ₁ φ₂ x w k).τ < (T : ENNReal) then (stage M φ₁ φ₂ x w k).x else 0

/-- The left side of the stage Dynkin formula. -/
noncomputable def Dl (u : ℝ → ℝ) (k : ℕ) : ℝ :=
  exp (-M.ρ * (sg M φ₁ φ₂ x w T (k + 1) : ℝ)) *
      u (Ys M φ₁ φ₂ x w T k + M.σ * (w (sg M φ₁ φ₂ x w T (k + 1)) - w (sg M φ₁ φ₂ x w T k)))
    - exp (-M.ρ * (sg M φ₁ φ₂ x w T k : ℝ)) * u (Ys M φ₁ φ₂ x w T k)

/-- The state at `σₖ`: the restart point `xₖ` if `τₖ ≤ T`, else `X_T`. -/
noncomputable def St (k : ℕ) : ℝ :=
  if (stage M φ₁ φ₂ x w k).τ ≤ (T : ENNReal) then (stage M φ₁ φ₂ x w k).x
  else ctrlX M φ₁ φ₂ x w T

noncomputable def Gk (V : ℝ → ℝ) (k : ℕ) : ℝ :=
  exp (-M.ρ * (sg M φ₁ φ₂ x w T k : ℝ)) * V (St M φ₁ φ₂ x w T k)

/-- The payoff to player `i` of an intervention of player `m` with impulse `δ`. -/
noncomputable def payI (i m : Player) (δ : ℝ) : ℝ := if m = i then cost M δ else gain M δ

noncomputable def Pay (i : Player) (k : ℕ) : ℝ :=
  if (stage M φ₁ φ₂ x w k).τ ≤ (T : ENNReal) then
    exp (-M.ρ * (stage M φ₁ φ₂ x w k).τ.toReal) *
      payI M i (stage M φ₁ φ₂ x w k).m (stage M φ₁ φ₂ x w k).δ
  else 0

/-- The intervention slack `e^{-ρτₖ₊₁}(V(pre) - V(xₖ₊₁) - pay)` (if `τₖ₊₁ ≤ T`). -/
noncomputable def slack (V : ℝ → ℝ) (i : Player) (k : ℕ) : ℝ :=
  if (stage M φ₁ φ₂ x w (k + 1)).τ ≤ (T : ENNReal) then
    exp (-M.ρ * (stage M φ₁ φ₂ x w (k + 1)).τ.toReal) *
      (V ((stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal)
        - V (stage M φ₁ φ₂ x w (k + 1)).x
        - payI M i (stage M φ₁ φ₂ x w (k + 1)).m (stage M φ₁ φ₂ x w (k + 1)).δ)
  else 0

end Tele

section TeleL
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}

lemma sg_of_le' {k : ℕ} (h : (stage M φ₁ φ₂ x w k).τ ≤ T) :
    sg M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).τ.toNNReal := by
  simp only [sg, min_eq_left h]

lemma sg_of_ge {k : ℕ} (h : (T : ENNReal) ≤ (stage M φ₁ φ₂ x w k).τ) :
    sg M φ₁ φ₂ x w T k = T := by
  simp only [sg, min_eq_right h, ENNReal.toNNReal_coe]

/-- On a non-transient stage, the stage process on `[τₖ, τₖ₊₁]` lies in the closure of
`C₁ ∩ C₂`. -/
lemma stage_mem_closure (hw : Continuous w) (k : ℕ)
    (hk : (stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ) (s : ℝ≥0)
    (h1 : (stage M φ₁ φ₂ x w k).τ ≤ s) (h2 : (s : ENNReal) ≤ (stage M φ₁ φ₂ x w (k + 1)).τ) :
    (stage M φ₁ φ₂ x w k).X s ∈ closure (φ₁.C ∩ φ₂.C) := by
  have hafin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
    ENNReal.coe_toNNReal hafin
  have has : (stage M φ₁ φ₂ x w k).τ.toNNReal ≤ s := by
    rw [← ENNReal.coe_le_coe, haa]; exact h1
  obtain ⟨b', hab, hsb, hsub⟩ : ∃ b' : ℝ≥0, (stage M φ₁ φ₂ x w k).τ.toNNReal < b' ∧ s ≤ b' ∧
      ∀ r : ℝ≥0, r < b' → (r : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ := by
    by_cases hbt : (stage M φ₁ φ₂ x w (k + 1)).τ = ⊤
    · refine ⟨s + 1, lt_of_le_of_lt has (lt_add_one s), (lt_add_one s).le, fun r _ => ?_⟩
      rw [hbt]; exact ENNReal.coe_lt_top
    · refine ⟨(stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal,
        (ENNReal.toNNReal_lt_toNNReal hafin hbt).2 hk, ENNReal.le_toNNReal_of_coe_le h2 hbt,
        fun r hr => ?_⟩
      rw [← ENNReal.coe_toNNReal hbt]; exact ENNReal.coe_lt_coe.2 hr
  have hcl : s ∈ closure (Set.Ioo (stage M φ₁ φ₂ x w k).τ.toNNReal b') := by
    rw [closure_Ioo hab.ne]
    exact ⟨has, hsb⟩
  have hmaps : Set.MapsTo (freeX M φ₁ φ₂ x w k) (Set.Ioo (stage M φ₁ φ₂ x w k).τ.toNNReal b')
      (φ₁.C ∩ φ₂.C) := by
    intro r hr
    have hr1 : (stage M φ₁ φ₂ x w k).τ < (r : ENNReal) := by
      rw [← haa]; exact ENNReal.coe_lt_coe.2 hr.1
    have hmem := stage_mem_C k r hr1 (hsub r hr.2)
    rw [stage_X_after k r hr1.le] at hmem
    exact hmem
  have := map_mem_closure (continuous_freeX hw k) hcl hmaps
  rw [stage_X_after k s h1]
  exact this

/-- **Stage identity.** `Gₖ - Gₖ₊₁ - Payₖ₊₁ = -Δₖ + slackₖ`, provided `u = V` on the closure
of `C₁ ∩ C₂`. -/
theorem stage_identity (hw : Continuous w) {u V : ℝ → ℝ}
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y) (i : Player) (k : ℕ) :
    Gk M φ₁ φ₂ x w T V k - Gk M φ₁ φ₂ x w T V (k + 1) - Pay M φ₁ φ₂ x w T i (k + 1) =
      -Dl M φ₁ φ₂ x w T u k + slack M φ₁ φ₂ x w T V i k := by
  have hmono := stage_tau_mono (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) k
  rcases lt_or_ge (T : ENNReal) (stage M φ₁ φ₂ x w k).τ with hTa | haT
  · have hTb := lt_of_lt_of_le hTa hmono
    have h0 : sg M φ₁ φ₂ x w T k = T := sg_of_ge hTa.le
    have h1 : sg M φ₁ φ₂ x w T (k + 1) = T := sg_of_ge hTb.le
    simp only [Gk, Dl, Pay, slack, St, Ys, h0, h1, not_le.2 hTa, not_le.2 hTb,
      not_lt.2 hTa.le, and_false, ↓reduceIte, sub_self, mul_zero, add_zero, zero_add, neg_zero]
  · have hafin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top haT
    have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
      ENNReal.coe_toNNReal hafin
    have h0 : sg M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).τ.toNNReal := sg_of_le' haT
    have hxk : (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ.toNNReal =
        (stage M φ₁ φ₂ x w k).x := by
      rw [stage_X_after k _ haa.ge]; simp
    rcases eq_or_lt_of_le hmono with hab | hab
    · -- transient stage `τₖ = τₖ₊₁ ≤ T`
      have hbT : (stage M φ₁ φ₂ x w (k + 1)).τ ≤ T := hab ▸ haT
      have h1 : sg M φ₁ φ₂ x w T (k + 1) = (stage M φ₁ φ₂ x w k).τ.toNNReal := by
        rw [sg_of_le' hbT, ← hab]
      have hpre : (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal =
          (stage M φ₁ φ₂ x w k).x := by
        rw [← hab, hxk]
      have hnot : ¬ ((stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ) := by
        rw [hab]; exact lt_irrefl _
      have hr : (stage M φ₁ φ₂ x w (k + 1)).τ.toReal = (stage M φ₁ φ₂ x w k).τ.toReal := by
        rw [hab]
      simp only [Gk, Dl, Pay, slack, St, Ys, h0, h1, haT, hbT, hnot, false_and, ↓reduceIte,
        hpre, hr, sub_self, mul_zero, add_zero, ENNReal.coe_toNNReal_eq_toReal]
      ring
    · have hxkC : (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w k).τ.toNNReal ∈
          closure (φ₁.C ∩ φ₂.C) :=
        stage_mem_closure hw k hab _ haa.ge (by rw [haa]; exact hab.le)
      have e2 := hVu _ hxkC
      rw [hxk] at e2
      rcases le_or_gt (stage M φ₁ φ₂ x w (k + 1)).τ T with hbT | hTb
      · have hbfin : (stage M φ₁ φ₂ x w (k + 1)).τ ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.coe_ne_top hbT
        have hbb : (((stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal : ℝ≥0) : ENNReal) =
            (stage M φ₁ φ₂ x w (k + 1)).τ := ENNReal.coe_toNNReal hbfin
        have h1 : sg M φ₁ φ₂ x w T (k + 1) = (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal :=
          sg_of_le' hbT
        have haT' : (stage M φ₁ φ₂ x w k).τ < T := lt_of_lt_of_le hab hbT
        have hpre : (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal =
            (stage M φ₁ φ₂ x w k).x + M.σ * (w (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal
              - w (stage M φ₁ φ₂ x w k).τ.toNNReal) :=
          stage_X_after k _ (by rw [hbb]; exact hab.le)
        have hpreC := stage_mem_closure hw k hab (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal
          (by rw [hbb]; exact hab.le) hbb.le
        have e1 := hVu _ hpreC
        rw [hpre] at e1
        simp only [Gk, Dl, Pay, slack, St, Ys, h0, h1, haT, hbT, hab, haT', and_self,
          ↓reduceIte, hpre, e1, e2, ENNReal.coe_toNNReal_eq_toReal]
        ring
      · have h1 : sg M φ₁ φ₂ x w T (k + 1) = T := sg_of_ge hTb.le
        have hctrl : ctrlX M φ₁ φ₂ x w T = (stage M φ₁ φ₂ x w k).X T :=
          ctrlX_eq_stage k T haT hTb
        have hXT : (stage M φ₁ φ₂ x w k).X T = (stage M φ₁ φ₂ x w k).x +
            M.σ * (w T - w (stage M φ₁ φ₂ x w k).τ.toNNReal) := stage_X_after k T haT
        have hXTC := stage_mem_closure hw k hab T haT hTb.le
        have e1 := hVu _ hXTC
        rw [hXT] at e1
        rcases eq_or_lt_of_le haT with haeq | haT'
        · have hTT : (stage M φ₁ φ₂ x w k).τ.toNNReal = T := by rw [haeq]; simp
          have hnot : ¬ ((stage M φ₁ φ₂ x w k).τ < T) := by rw [haeq]; exact lt_irrefl _
          simp only [Gk, Dl, Pay, slack, St, Ys, h0, h1, haT, not_le.2 hTb, hnot, and_false,
            ↓reduceIte, hctrl, hXT, hTT, sub_self, mul_zero, add_zero, neg_zero]
        · simp only [Gk, Dl, Pay, slack, St, Ys, h0, h1, haT, not_le.2 hTb, hab, haT', and_self,
            ↓reduceIte, hctrl, hXT, e1, e2, ENNReal.coe_toNNReal_eq_toReal]
          ring

end TeleL


-- ===== from scratch/probe/2b17c77f_tele2.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3b: summing the stage identity; the running integral -/

/-- The running-payoff integral over stage `k` (frozen-start form, as in the Dynkin formula). -/
noncomputable def Rk (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (T : ℝ≥0) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ r in (sg M φ₁ φ₂ x w T k : ℝ)..(sg M φ₁ φ₂ x w T (k + 1) : ℝ),
    exp (-M.ρ * r) * f (Ys M φ₁ φ₂ x w T k + M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k)))

section Tele2
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}

lemma sg_zero : sg M φ₁ φ₂ x w T 0 = 0 := by
  simp [sg, stage_zero]

lemma Gk_zero (V : ℝ → ℝ) : Gk M φ₁ φ₂ x w T V 0 = V x := by
  simp [Gk, St, sg_zero, stage_zero]

lemma sg_mono (k : ℕ) : sg M φ₁ φ₂ x w T k ≤ sg M φ₁ φ₂ x w T (k + 1) := by
  unfold sg
  exact ENNReal.toNNReal_mono (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    (min_le_min_right _ (stage_tau_mono k))

lemma sg_le_T (k : ℕ) : sg M φ₁ φ₂ x w T k ≤ T := by
  unfold sg
  have := ENNReal.toNNReal_mono ENNReal.coe_ne_top
    (min_le_right (stage M φ₁ φ₂ x w k).τ (T : ENNReal))
  simpa using this

/-- **Telescoped identity.** `V x + Σ_{k<K} Δₖ = G_K + Σ_{k<K} Payₖ₊₁ + Σ_{k<K} slackₖ`. -/
theorem tele_sum (hw : Continuous w) {u V : ℝ → ℝ}
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y) (i : Player) (K : ℕ) :
    V x + ∑ k ∈ Finset.range K, Dl M φ₁ φ₂ x w T u k =
      Gk M φ₁ φ₂ x w T V K + ∑ k ∈ Finset.range K, Pay M φ₁ φ₂ x w T i (k + 1)
        + ∑ k ∈ Finset.range K, slack M φ₁ φ₂ x w T V i k := by
  induction K with
  | zero => simp [Gk_zero]
  | succ K ih =>
    have h := stage_identity (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := T) hw hVu i K
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- On stage `k` the frozen-start integrand is the running payoff of the controlled process. -/
lemma Rk_eq (hw : Continuous w) {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    Rk M φ₁ φ₂ x w T f k =
      ∫ r in (sg M φ₁ φ₂ x w T k : ℝ)..(sg M φ₁ φ₂ x w T (k + 1) : ℝ),
        exp (-M.ρ * r) * f (ctrlX M φ₁ φ₂ x w r.toNNReal) ∧
    IntervalIntegrable (fun r : ℝ => exp (-M.ρ * r) * f (ctrlX M φ₁ φ₂ x w r.toNNReal))
      MeasureTheory.volume (sg M φ₁ φ₂ x w T k : ℝ) (sg M φ₁ φ₂ x w T (k + 1) : ℝ) := by
  rcases eq_or_lt_of_le (sg_mono (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := T) k)
    with heq | hlt
  · refine ⟨?_, ?_⟩
    · simp only [Rk, heq, intervalIntegral.integral_same]
    · rw [heq]
  · -- non-degenerate: `τₖ < τₖ₊₁` and `τₖ < T`
    have hkT : (stage M φ₁ φ₂ x w k).τ < T := by
      by_contra h
      have h0 : sg M φ₁ φ₂ x w T k = T := sg_of_ge (not_lt.1 h)
      have := sg_le_T (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := T) (k + 1)
      rw [h0] at hlt
      exact absurd hlt (not_lt.2 this)
    have hafin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_lt hkT
    have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
      ENNReal.coe_toNNReal hafin
    have h0 : sg M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).τ.toNNReal := sg_of_le' hkT.le
    have hsg1 : ((sg M φ₁ φ₂ x w T (k + 1) : ℝ≥0) : ENNReal) ≤ (stage M φ₁ φ₂ x w (k + 1)).τ := by
      unfold sg
      rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
      exact min_le_left _ _
    have hkk : (stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ := by
      by_contra h
      have hb : (stage M φ₁ φ₂ x w (k + 1)).τ = (stage M φ₁ φ₂ x w k).τ :=
        le_antisymm (not_lt.1 h) (stage_tau_mono k)
      have : sg M φ₁ φ₂ x w T (k + 1) = sg M φ₁ φ₂ x w T k := by simp only [sg, hb]
      rw [this] at hlt
      exact lt_irrefl _ hlt
    have hYs : Ys M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).x := by
      simp only [Ys, hkk, hkT, and_self, ↓reduceIte]
    have heqOn : Set.EqOn
        (fun r : ℝ => exp (-M.ρ * r) * f (Ys M φ₁ φ₂ x w T k +
          M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k))))
        (fun r : ℝ => exp (-M.ρ * r) * f (ctrlX M φ₁ φ₂ x w r.toNNReal))
        (Set.Ioo (sg M φ₁ φ₂ x w T k : ℝ) (sg M φ₁ φ₂ x w T (k + 1) : ℝ)) := by
      intro r hr
      have hr0 : (0 : ℝ) ≤ r := le_trans (NNReal.coe_nonneg _) hr.1.le
      have h1 : (stage M φ₁ φ₂ x w k).τ ≤ (r.toNNReal : ENNReal) := by
        rw [← haa, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0, ← h0]
        exact hr.1.le
      have h2 : (r.toNNReal : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ := by
        refine lt_of_lt_of_le ?_ hsg1
        rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
        exact hr.2
      simp only
      rw [ctrlX_eq_stage k _ h1 h2, stage_X_after k _ h1, hYs, h0]
    have hcont : Continuous (fun r : ℝ => exp (-M.ρ * r) * f (Ys M φ₁ φ₂ x w T k +
        M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k)))) := by
      have : Continuous (fun r : ℝ => w r.toNNReal) := hw.comp continuous_real_toNNReal
      fun_prop
    have hle' : (sg M φ₁ φ₂ x w T k : ℝ) ≤ (sg M φ₁ φ₂ x w T (k + 1) : ℝ) :=
      NNReal.coe_le_coe.2 hlt.le
    refine ⟨?_, ?_⟩
    · unfold Rk
      rw [intervalIntegral.integral_of_le hle', intervalIntegral.integral_of_le hle',
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo heqOn
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle']
      exact ((hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self).congr_fun heqOn
        measurableSet_Ioo

/-- **Running integral.** `Σ_{k<K} Rₖ = ∫₀^{σ_K} e^{-ρr} f(X_r) dr`. -/
theorem run_sum (hw : Continuous w) {f : ℝ → ℝ} (hf : Continuous f) (K : ℕ) :
    ∑ k ∈ Finset.range K, Rk M φ₁ φ₂ x w T f k =
      ∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w T K : ℝ),
        exp (-M.ρ * r) * f (ctrlX M φ₁ φ₂ x w r.toNNReal) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun r : ℝ => exp (-M.ρ * r) * f (ctrlX M φ₁ φ₂ x w r.toNNReal))
    (μ := MeasureTheory.volume) (a := fun k => (sg M φ₁ φ₂ x w T k : ℝ)) (n := K)
    (fun k _ => (Rk_eq hw hf k).2)
  simp only [sg_zero, NNReal.coe_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => (Rk_eq hw hf k).1

end Tele2


-- ===== from scratch/probe/2b17c77f_gen.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3c: the generator inequality along a non-transient stage -/

/-- The right side of the stage Dynkin formula. -/
noncomputable def Dyn (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (T : ℝ≥0) (u u2 : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ r in (sg M φ₁ φ₂ x w T k : ℝ)..(sg M φ₁ φ₂ x w T (k + 1) : ℝ),
    exp (-M.ρ * r) *
      (M.σ ^ 2 / 2 * u2 (Ys M φ₁ φ₂ x w T k + M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k)))
        - M.ρ * u (Ys M φ₁ φ₂ x w T k + M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k))))

section Gen
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}

/-- A non-degenerate stage interval `σₖ < σₖ₊₁` is a genuine stage started before `T`, and the
frozen-start process is the stage process on it. -/
lemma nondeg (k : ℕ) (hlt : sg M φ₁ φ₂ x w T k < sg M φ₁ φ₂ x w T (k + 1)) :
    ∀ r ∈ Set.Ioo (sg M φ₁ φ₂ x w T k : ℝ) (sg M φ₁ φ₂ x w T (k + 1) : ℝ),
      (stage M φ₁ φ₂ x w k).τ < (r.toNNReal : ENNReal) ∧
      (r.toNNReal : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ ∧
      Ys M φ₁ φ₂ x w T k + M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k)) =
        (stage M φ₁ φ₂ x w k).X r.toNNReal := by
  have hkT : (stage M φ₁ φ₂ x w k).τ < T := by
    by_contra h
    have h0 : sg M φ₁ φ₂ x w T k = T := sg_of_ge (not_lt.1 h)
    have := sg_le_T (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := T) (k + 1)
    rw [h0] at hlt
    exact absurd hlt (not_lt.2 this)
  have hafin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_lt hkT
  have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
    ENNReal.coe_toNNReal hafin
  have h0 : sg M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).τ.toNNReal := sg_of_le' hkT.le
  have hsg1 : ((sg M φ₁ φ₂ x w T (k + 1) : ℝ≥0) : ENNReal) ≤ (stage M φ₁ φ₂ x w (k + 1)).τ := by
    unfold sg
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  have hkk : (stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ := by
    by_contra h
    have hb : (stage M φ₁ φ₂ x w (k + 1)).τ = (stage M φ₁ φ₂ x w k).τ :=
      le_antisymm (not_lt.1 h) (stage_tau_mono k)
    have : sg M φ₁ φ₂ x w T (k + 1) = sg M φ₁ φ₂ x w T k := by simp only [sg, hb]
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hYs : Ys M φ₁ φ₂ x w T k = (stage M φ₁ φ₂ x w k).x := by
    simp only [Ys, hkk, hkT, and_self, ↓reduceIte]
  intro r hr
  have hr0 : (0 : ℝ) ≤ r := le_trans (NNReal.coe_nonneg _) hr.1.le
  have h1 : (stage M φ₁ φ₂ x w k).τ < (r.toNNReal : ENNReal) := by
    rw [← haa, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0, ← h0]
    exact hr.1
  have h2 : (r.toNNReal : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ := by
    refine lt_of_lt_of_le ?_ hsg1
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
    exact hr.2
  refine ⟨h1, h2, ?_⟩
  rw [stage_X_after k _ h1.le, hYs, h0]

/-- **Generator inequality.** If `σ²/2 u'' - ρu + f ≤ 0` on `C₁ ∩ C₂`, then along every stage
`Dynₖ + Rₖ ≤ 0`. -/
theorem gen_le (hw : Continuous w) {u u2 f : ℝ → ℝ} {D : ℝ}
    (hum : Measurable u) (hu : ∀ y, |u y| ≤ D * (1 + |y|))
    (hu2m : Measurable u2) (hu2 : ∀ y, |u2 y| ≤ D * (1 + |y|)) (hf : Continuous f)
    (hgen : ∀ y ∈ φ₁.C ∩ φ₂.C, M.σ ^ 2 / 2 * u2 y - M.ρ * u y + f y ≤ 0) (k : ℕ) :
    Dyn M φ₁ φ₂ x w T u u2 k + Rk M φ₁ φ₂ x w T f k ≤ 0 := by
  rcases eq_or_lt_of_le (sg_mono (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := T) k)
    with heq | hlt
  · simp only [Dyn, Rk, heq, intervalIntegral.integral_same, add_zero, le_refl]
  · have hle' : (sg M φ₁ φ₂ x w T k : ℝ) ≤ (sg M φ₁ φ₂ x w T (k + 1) : ℝ) :=
      NNReal.coe_le_coe.2 hlt.le
    have hD : 0 ≤ D := by
      have := hu 0
      have h1 : 0 ≤ D * (1 + |(0 : ℝ)|) := le_trans (abs_nonneg _) this
      simp at h1
      exact h1
    set p : ℝ → ℝ := fun r => Ys M φ₁ φ₂ x w T k + M.σ * (w r.toNNReal - w (sg M φ₁ φ₂ x w T k))
      with hpdef
    have hp : Continuous p := by
      have : Continuous (fun r : ℝ => w r.toNNReal) := hw.comp continuous_real_toNNReal
      simp only [hpdef]
      fun_prop
    have hLm : Measurable fun y => M.σ ^ 2 / 2 * u2 y - M.ρ * u y :=
      (hu2m.const_mul _).sub (hum.const_mul _)
    have hL : ∀ y, |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤ ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by
      intro y
      have h1 := hu y
      have h2 := hu2 y
      have hs : 0 ≤ M.σ ^ 2 / 2 := by positivity
      calc |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤ |M.σ ^ 2 / 2 * u2 y| + |M.ρ * u y| := abs_sub _ _
        _ = M.σ ^ 2 / 2 * |u2 y| + |M.ρ| * |u y| := by rw [abs_mul, abs_mul, abs_of_nonneg hs]
        _ ≤ M.σ ^ 2 / 2 * (D * (1 + |y|)) + |M.ρ| * (D * (1 + |y|)) := by
          gcongr
        _ = ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by ring
    have i1 : IntervalIntegrable (fun r => exp (-M.ρ * r) *
        (fun y => M.σ ^ 2 / 2 * u2 y - M.ρ * u y) (p r)) MeasureTheory.volume
        (sg M φ₁ φ₂ x w T k : ℝ) (sg M φ₁ φ₂ x w T (k + 1) : ℝ) :=
      intervalIntegrable_path hLm hL hp M.ρ hle'
    have i2 : IntervalIntegrable (fun r => exp (-M.ρ * r) * f (p r)) MeasureTheory.volume
        (sg M φ₁ φ₂ x w T k : ℝ) (sg M φ₁ φ₂ x w T (k + 1) : ℝ) :=
      (by fun_prop : Continuous fun r => exp (-M.ρ * r) * f (p r)).intervalIntegrable _ _
    have e : Dyn M φ₁ φ₂ x w T u u2 k + Rk M φ₁ φ₂ x w T f k =
        ∫ r in (sg M φ₁ φ₂ x w T k : ℝ)..(sg M φ₁ φ₂ x w T (k + 1) : ℝ),
          (exp (-M.ρ * r) * (fun y => M.σ ^ 2 / 2 * u2 y - M.ρ * u y) (p r)
            + exp (-M.ρ * r) * f (p r)) := by
      rw [intervalIntegral.integral_add i1 i2]
      rfl
    rw [e, intervalIntegral.integral_of_le hle', MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_nonpos measurableSet_Ioo fun r hr => ?_
    obtain ⟨h1, h2, h3⟩ := nondeg k hlt r hr
    have hmem := stage_mem_C k _ h1 h2
    have hg := hgen _ hmem
    simp only [hpdef]
    rw [h3, ← mul_add]
    exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le hg

end Gen


-- ===== from scratch/probe/2b17c77f_bnd.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3d: pathwise bounds -- the jumps, the slack, and a lower bound for `Gₖ` -/

section Bnd
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}

/-- On a non-transient stage, the stage process on `[τₖ, τₖ₊₁]` stays in any closed set that
contains it on `]τₖ, τₖ₊₁[`. -/
lemma stage_mem_closed (hw : Continuous w) (k : ℕ)
    (hk : (stage M φ₁ φ₂ x w k).τ < (stage M φ₁ φ₂ x w (k + 1)).τ) {F : Set ℝ} (hF : IsClosed F)
    (hin : ∀ r : ℝ≥0, (stage M φ₁ φ₂ x w k).τ < r → (r : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ →
      (stage M φ₁ φ₂ x w k).X r ∈ F) (s : ℝ≥0)
    (h1 : (stage M φ₁ φ₂ x w k).τ ≤ s) (h2 : (s : ENNReal) ≤ (stage M φ₁ φ₂ x w (k + 1)).τ) :
    (stage M φ₁ φ₂ x w k).X s ∈ F := by
  have hafin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
    ENNReal.coe_toNNReal hafin
  have has : (stage M φ₁ φ₂ x w k).τ.toNNReal ≤ s := by
    rw [← ENNReal.coe_le_coe, haa]; exact h1
  obtain ⟨b', hab, hsb, hsub⟩ : ∃ b' : ℝ≥0, (stage M φ₁ φ₂ x w k).τ.toNNReal < b' ∧ s ≤ b' ∧
      ∀ r : ℝ≥0, r < b' → (r : ENNReal) < (stage M φ₁ φ₂ x w (k + 1)).τ := by
    by_cases hbt : (stage M φ₁ φ₂ x w (k + 1)).τ = ⊤
    · refine ⟨s + 1, lt_of_le_of_lt has (lt_add_one s), (lt_add_one s).le, fun r _ => ?_⟩
      rw [hbt]; exact ENNReal.coe_lt_top
    · refine ⟨(stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal,
        (ENNReal.toNNReal_lt_toNNReal hafin hbt).2 hk, ENNReal.le_toNNReal_of_coe_le h2 hbt,
        fun r hr => ?_⟩
      rw [← ENNReal.coe_toNNReal hbt]; exact ENNReal.coe_lt_coe.2 hr
  have hcl : s ∈ closure (Set.Ioo (stage M φ₁ φ₂ x w k).τ.toNNReal b') := by
    rw [closure_Ioo hab.ne]
    exact ⟨has, hsb⟩
  have hmaps : Set.MapsTo (freeX M φ₁ φ₂ x w k) (Set.Ioo (stage M φ₁ φ₂ x w k).τ.toNNReal b') F := by
    intro r hr
    have hr1 : (stage M φ₁ φ₂ x w k).τ < (r : ENNReal) := by
      rw [← haa]; exact ENNReal.coe_lt_coe.2 hr.1
    have hmem := hin r hr1 (hsub r hr.2)
    rw [stage_X_after k r hr1.le] at hmem
    exact hmem
  have := map_mem_closure (continuous_freeX hw k) hcl hmaps
  rw [hF.closure_eq] at this
  rw [stage_X_after k s h1]
  exact this

/-- **The jump at a finite stage time.** -/
lemma jump_facts (hw : Continuous w) (k : ℕ) (hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤) :
    (stage M φ₁ φ₂ x w (k + 1)).x = (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal
        + (stage M φ₁ φ₂ x w (k + 1)).δ ∧
    (((stage M φ₁ φ₂ x w (k + 1)).m = .one ∧
        (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal ∉ φ₁.C ∧
        (stage M φ₁ φ₂ x w (k + 1)).δ =
          φ₁.ξ ((stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal)) ∨
      ((stage M φ₁ φ₂ x w (k + 1)).m = .two ∧
        (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal ∉ φ₂.C ∧
        (stage M φ₁ φ₂ x w (k + 1)).δ =
          φ₂.ξ ((stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal))) := by
  have hle : (stage M φ₁ φ₂ x w k).τ ≤
      (((stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal : ℝ≥0) : ENNReal) := by
    rw [ENNReal.coe_toNNReal hτ.ne]; exact stage_tau_mono k
  have hpre : freeX M φ₁ φ₂ x w k (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal =
      (stage M φ₁ φ₂ x w k).X (stage M φ₁ φ₂ x w (k + 1)).τ.toNNReal := by
    rw [stage_X_after k _ hle]; rfl
  obtain ⟨h1, h2⟩ := stage_pre_not_mem (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) hw k hτ
  refine ⟨by rw [stage_succ_x, if_pos hτ], ?_⟩
  rcases hm : (stage M φ₁ φ₂ x w (k + 1)).m with _ | _
  · left
    refine ⟨rfl, by rw [← hpre]; exact h1 hm, ?_⟩
    rw [stage_succ_δ, if_pos hτ, hm]
  · right
    refine ⟨rfl, by rw [← hpre]; exact h2 hm, ?_⟩
    rw [stage_succ_δ, if_pos hτ, hm]

/-- **The intervention slack is nonnegative** under the jump inequalities of the QVI. -/
lemma slack_nonneg (hw : Continuous w) {V : ℝ → ℝ} (i : Player)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) ≤ V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) ≤ V y) (k : ℕ) :
    0 ≤ slack M φ₁ φ₂ x w T V i k := by
  unfold slack
  split_ifs with hT
  · have hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤ := lt_of_le_of_lt hT ENNReal.coe_lt_top
    obtain ⟨hx, hm⟩ := jump_facts hw k hτ
    apply mul_nonneg (exp_pos _).le
    rw [hx]
    rcases hm with ⟨hm, hC, hδ⟩ | ⟨hm, hC, hδ⟩
    · rw [hm, hδ]; linarith [hJ1 _ hC]
    · rw [hm, hδ]; linarith [hJ2 _ hC]
  · exact le_refl 0

/-- **Lower bound for the restart points** through a function `ℓ` that the jumps do not
decrease, given a bound `S` for the controlled process. -/
lemma ell_bound (hw : Continuous w) {ℓ : ℝ → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S) (hℓ : ∀ y, -(D * (1 + |y|)) ≤ ℓ y)
    (hJ1 : ∀ y, y ∉ φ₁.C → ℓ y ≤ ℓ (y + φ₁.ξ y))
    (hJ2 : ∀ y, y ∉ φ₂.C → ℓ y ≤ ℓ (y + φ₂.ξ y)) :
    ∀ n, (stage M φ₁ φ₂ x w n).τ < ⊤ → -(D * (1 + |x| + S)) ≤ ℓ (stage M φ₁ φ₂ x w n).x := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  intro n
  induction n with
  | zero =>
    intro _
    have := hℓ x
    simp only [stage_zero]
    nlinarith
  | succ n ih =>
    intro hτ
    obtain ⟨hx, hm⟩ := jump_facts hw n hτ
    set pre := (stage M φ₁ φ₂ x w n).X (stage M φ₁ φ₂ x w (n + 1)).τ.toNNReal with hpre
    have hstep : ℓ pre ≤ ℓ (stage M φ₁ φ₂ x w (n + 1)).x := by
      rw [hx]
      rcases hm with ⟨_, hC, hδ⟩ | ⟨_, hC, hδ⟩
      · rw [hδ]; exact hJ1 _ hC
      · rw [hδ]; exact hJ2 _ hC
    have hle : (stage M φ₁ φ₂ x w n).τ ≤
        (((stage M φ₁ φ₂ x w (n + 1)).τ.toNNReal : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_toNNReal hτ.ne]; exact stage_tau_mono n
    rcases eq_or_lt_of_le (stage_tau_mono (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) n)
      with hab | hab
    · -- transient: `pre = xₙ`
      have hfin : (stage M φ₁ φ₂ x w n).τ < ⊤ := hab ▸ hτ
      have hpx : pre = (stage M φ₁ φ₂ x w n).x := by
        rw [hpre, ← hab, stage_X_after n _ (by rw [ENNReal.coe_toNNReal hfin.ne])]
        simp
      have := ih hfin
      rw [hpx] at hstep
      linarith
    · -- non-transient: `|pre| ≤ S`
      have hF : IsClosed {y : ℝ | |y| ≤ S} := isClosed_le continuous_abs continuous_const
      have hmem : pre ∈ {y : ℝ | |y| ≤ S} := by
        refine stage_mem_closed hw n hab hF (fun r h1 h2 => ?_) _ hle
          (by rw [ENNReal.coe_toNNReal hτ.ne])
        show |(stage M φ₁ φ₂ x w n).X r| ≤ S
        rw [← ctrlX_eq_stage n r h1.le h2]
        exact hS r
      have h1 := hℓ pre
      have h2 : |pre| ≤ S := hmem
      have h3 : D * (1 + |pre|) ≤ D * (1 + |x| + S) := by
        apply mul_le_mul_of_nonneg_left _ hD
        linarith [abs_nonneg x]
      linarith

/-- **Lower bound for `Gₖ`.** -/
lemma Gk_lower (hw : Continuous w) {V ℓ : ℝ → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S) (hVℓ : ∀ y, ℓ y ≤ V y)
    (hℓ : ∀ y, -(D * (1 + |y|)) ≤ ℓ y)
    (hJ1 : ∀ y, y ∉ φ₁.C → ℓ y ≤ ℓ (y + φ₁.ξ y))
    (hJ2 : ∀ y, y ∉ φ₂.C → ℓ y ≤ ℓ (y + φ₂.ξ y)) (K : ℕ) :
    -(exp (-M.ρ * (sg M φ₁ φ₂ x w T K : ℝ)) * (D * (1 + |x| + S))) ≤ Gk M φ₁ φ₂ x w T V K := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have hb : -(D * (1 + |x| + S)) ≤ V (St M φ₁ φ₂ x w T K) := by
    unfold St
    split_ifs with hK
    · exact le_trans (ell_bound hw hD hS hℓ hJ1 hJ2 K (lt_of_le_of_lt hK ENNReal.coe_lt_top))
        (hVℓ _)
    · have h1 := hℓ (ctrlX M φ₁ φ₂ x w T)
      have h2 := hS T
      have h3 : D * (1 + |ctrlX M φ₁ φ₂ x w T|) ≤ D * (1 + |x| + S) := by
        apply mul_le_mul_of_nonneg_left _ hD
        linarith [abs_nonneg x]
      linarith [hVℓ (ctrlX M φ₁ φ₂ x w T)]
  unfold Gk
  have he := (exp_pos (-M.ρ * (sg M φ₁ φ₂ x w T K : ℝ))).le
  nlinarith

end Bnd


-- ===== from scratch/probe/2b17c77f_int.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3e: measurability and integrability of the stage quantities in `ω` -/

section Int
variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
  (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
  (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)

include hBm hBc in
lemma sg_meas (T : ℝ≥0) (k : ℕ) : Measurable fun ω => sg M φ₁ φ₂ x (fun s => B s ω) T k := by
  obtain ⟨hτk, -⟩ := stage_optional hBm hBc M φ₁ φ₂ x k
  have hT := trunc_optional (nat B hBm) _ hτk T
  exact measurable_of_Iio fun t => (nat B hBm).le t _ (hT t)

include hBm hBc in
lemma Ys_meas (T : ℝ≥0) (k : ℕ) : Measurable fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) T k := by
  classical
  obtain ⟨hτk, hxk⟩ := stage_optional hBm hBc M φ₁ φ₂ x k
  obtain ⟨hτk1, -⟩ := stage_optional hBm hBc M φ₁ φ₂ x (k + 1)
  have e : (fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) T k) = fun ω =>
      if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (stage M φ₁ φ₂ x (fun s => B s ω) (k + 1)).τ ∧
          (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ENNReal) then
        (if (stage M φ₁ φ₂ x (fun s => B s ω) k).τ < (T : ENNReal) then
          (stage M φ₁ φ₂ x (fun s => B s ω) k).x else 0) else 0 := by
    funext ω
    unfold Ys
    split_ifs with h1 h2 <;> first | rfl | exact absurd h1.2 h2
  rw [e]
  exact (Measurable.ite (lt_optional (nat B hBm) _ _ hτk hτk1 T) (hxk T) measurable_const).mono
    ((nat B hBm).le T) le_rfl

/-- `|Ys| ≤ S` when `S` bounds the controlled process. -/
lemma Ys_bound {w : ℝ≥0 → ℝ} {S : ℝ} (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S) (T : ℝ≥0) (k : ℕ) :
    |Ys M φ₁ φ₂ x w T k| ≤ S := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  unfold Ys
  split_ifs with h
  · have hfin : (stage M φ₁ φ₂ x w k).τ ≠ ⊤ := ne_top_of_lt h.2
    have haa : (((stage M φ₁ φ₂ x w k).τ.toNNReal : ℝ≥0) : ENNReal) = (stage M φ₁ φ₂ x w k).τ :=
      ENNReal.coe_toNNReal hfin
    have hc := ctrlX_eq_stage (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) k _ haa.ge
      (by rw [haa]; exact h.1)
    rw [stage_X_after k _ haa.ge] at hc
    simp only [sub_self, mul_zero, add_zero] at hc
    rw [← hc]
    exact hS _
  · simpa using hS0

include hBm hBc in
/-- **Integrability of a stage integral** `ω ↦ ∫_{σₖ}^{σₖ₊₁} e^{-ρr} g(Y + σ(B_r - B_{σₖ})) dr`. -/
lemma stage_int_integrable {P : Measure Ω} [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    {g : ℝ → ℝ} (hgm : Measurable g) {D : ℝ} (hg : ∀ y, |g y| ≤ D * (1 + |y|)) (T : ℕ) (k : ℕ)
    (hYi : Integrable (fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) T k) P) :
    Integrable (fun ω => ∫ r in (sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ)..
        (sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ),
      exp (-M.ρ * r) * g (Ys M φ₁ φ₂ x (fun s => B s ω) T k +
        M.σ * (B r.toNNReal ω - B (sg M φ₁ φ₂ x (fun s => B s ω) T k) ω))) P := by
  have hD := lin_C0 hg
  obtain ⟨Mx, hMm, hMi, hMb⟩ := exists_sup_bm hB hBm hBc T
  have hs0 := sg_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) k
  have hs1 := sg_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) (k + 1)
  have hYm := Ys_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) k
  have hBs := measurable_B_at hBm hBc hs0
  have hJ := measurable_B_joint hBm hBc
  have hmeas : Measurable fun ω => ∫ r in (sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ)..
      (sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ),
      exp (-M.ρ * r) * g (Ys M φ₁ φ₂ x (fun s => B s ω) T k +
        M.σ * (B r.toNNReal ω - B (sg M φ₁ φ₂ x (fun s => B s ω) T k) ω)) := by
    refine measurable_interval_integral (fun ω r => exp (-M.ρ * r) *
      g (Ys M φ₁ φ₂ x (fun s => B s ω) T k +
        M.σ * (B r.toNNReal ω - B (sg M φ₁ φ₂ x (fun s => B s ω) T k) ω))) ?_ _ _
      (measurable_coe_nnreal_real.comp hs0) (measurable_coe_nnreal_real.comp hs1) (T : ℝ)
      (fun ω => NNReal.coe_nonneg _) (fun ω => NNReal.coe_le_coe.2 (sg_mono k))
      (fun ω => by exact_mod_cast sg_le_T (k + 1))
    have h1 : Measurable fun p : Ω × ℝ => exp (-M.ρ * p.2) :=
      Real.measurable_exp.comp (measurable_const.mul measurable_snd)
    have h2 : Measurable fun p : Ω × ℝ => Ys M φ₁ φ₂ x (fun s => B s p.1) T k +
        M.σ * (B p.2.toNNReal p.1 - B (sg M φ₁ φ₂ x (fun s => B s p.1) T k) p.1) :=
      (hYm.comp measurable_fst).add (measurable_const.mul (hJ.sub (hBs.comp measurable_fst)))
    exact h1.mul (hgm.comp h2)
  refine Integrable.mono' (g := fun ω => (T : ℝ) * (exp (|M.ρ| * T) *
    (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω))))) ?_
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  · refine Integrable.const_mul (Integrable.const_mul (Integrable.const_mul ?_ _) _) _
    exact (integrable_const 1).add (hYi.abs.add (hMi.const_mul _))
  · rw [Real.norm_eq_abs]
    have hb : ∀ r ∈ Set.uIoc (sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ)
        (sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ),
        ‖exp (-M.ρ * r) * g (Ys M φ₁ φ₂ x (fun s => B s ω) T k +
          M.σ * (B r.toNNReal ω - B (sg M φ₁ φ₂ x (fun s => B s ω) T k) ω))‖ ≤
        exp (|M.ρ| * T) * (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω))) := by
      intro r hr
      rw [Set.uIoc_of_le (NNReal.coe_le_coe.2 (sg_mono k))] at hr
      have hr0 : 0 ≤ r := le_trans (NNReal.coe_nonneg _) hr.1.le
      have hrT : r ≤ T := le_trans hr.2 (by exact_mod_cast sg_le_T (k + 1))
      rw [Real.norm_eq_abs]
      refine term_bound hg hr0 hrT (hMb ω _ ?_) (hMb ω _ ?_)
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact_mod_cast hrT
      · have := sg_le_T (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := fun s => B s ω)
          (T := (T : ℝ≥0)) k
        exact_mod_cast this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have hlen : |(sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ) -
        (sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ)| ≤ T := by
      have a1 : (sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ) ≤ sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) :=
        NNReal.coe_le_coe.2 (sg_mono k)
      have a2 : (sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ) ≤ T := by
        exact_mod_cast sg_le_T (k + 1)
      rw [abs_of_nonneg (by linarith)]
      linarith [NNReal.coe_nonneg (sg M φ₁ φ₂ x (fun s => B s ω) T k)]
    have hC : 0 ≤ exp (|M.ρ| * T) *
        (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω))) := by
      have : 0 ≤ Mx ω := le_trans (abs_nonneg _) (hMb ω 0 (by positivity))
      positivity
    nlinarith

include hBm hBc in
/-- **Integrability of the Dynkin left side.** -/
lemma Dl_integrable {P : Measure Ω} [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    {u : ℝ → ℝ} (huc : Continuous u) {D : ℝ} (hu : ∀ y, |u y| ≤ D * (1 + |y|)) (T : ℕ) (k : ℕ)
    (hYi : Integrable (fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) T k) P) :
    Integrable (fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) T u k) P := by
  have hD := lin_C0 hu
  obtain ⟨Mx, hMm, hMi, hMb⟩ := exists_sup_bm hB hBm hBc T
  have hs0 := sg_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) k
  have hs1 := sg_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) (k + 1)
  have hYm := Ys_meas hBm hBc M φ₁ φ₂ x (T : ℝ≥0) k
  have hmeas : Measurable fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) T u k := by
    unfold Dl
    have hb1 := measurable_B_at hBm hBc hs1
    have hb0 := measurable_B_at hBm hBc hs0
    exact ((Real.measurable_exp.comp (measurable_const.mul
      (measurable_coe_nnreal_real.comp hs1))).mul (huc.measurable.comp
        (hYm.add (measurable_const.mul (hb1.sub hb0))))).sub
      ((Real.measurable_exp.comp (measurable_const.mul
        (measurable_coe_nnreal_real.comp hs0))).mul (huc.measurable.comp hYm))
  refine Integrable.mono' (g := fun ω => exp (|M.ρ| * T) *
    (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω))) +
      exp (|M.ρ| * T) * (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω)))) ?_
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  · have h : Integrable (fun ω => exp (|M.ρ| * T) *
        (D * (1 + (|Ys M φ₁ φ₂ x (fun s => B s ω) T k| + 2 * |M.σ| * Mx ω)))) P :=
      Integrable.const_mul (Integrable.const_mul
        ((integrable_const 1).add (hYi.abs.add (hMi.const_mul _))) _) _
    exact h.add h
  · rw [Real.norm_eq_abs]
    unfold Dl
    have hT1 : ((sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1) : ℝ≥0) : ℝ) ≤ T := by
      exact_mod_cast sg_le_T (k + 1)
    have hT0 : ((sg M φ₁ φ₂ x (fun s => B s ω) T k : ℝ≥0) : ℝ) ≤ T := by
      exact_mod_cast sg_le_T k
    have hM1 : |B (sg M φ₁ φ₂ x (fun s => B s ω) T (k + 1)) ω| ≤ Mx ω :=
      hMb ω _ (by exact_mod_cast sg_le_T (k + 1))
    have hM0 : |B (sg M φ₁ φ₂ x (fun s => B s ω) T k) ω| ≤ Mx ω :=
      hMb ω _ (by exact_mod_cast sg_le_T k)
    have t1 := term_bound hu (NNReal.coe_nonneg _) hT1 hM1 hM0
      (ρ := M.ρ) (σ := M.σ) (y := Ys M φ₁ φ₂ x (fun s => B s ω) T k)
    have t2 := term_bound hu (NNReal.coe_nonneg _) hT0 hM0 hM0
      (ρ := M.ρ) (σ := M.σ) (y := Ys M φ₁ φ₂ x (fun s => B s ω) T k)
    simp only [sub_self, mul_zero, add_zero] at t2
    calc _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add t1 t2

end Int


-- ===== from scratch/probe/2b17c77f_lim.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3f: the intervention sums and the limit `n → ∞` along one path -/

open Classical in
/-- Own interventions of player `i` at stage `l`: `e^{-ρτ_l} cost(δ_l)`. -/
noncomputable def aI (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (i : Player) (l : ℕ) : ℝ :=
  if intervenes M φ₁ φ₂ x w i l then
    disc M (stage M φ₁ φ₂ x w l).τ * cost M (stage M φ₁ φ₂ x w l).δ else 0

open Classical in
/-- Opponent interventions at stage `l`: `e^{-ρτ_l} gain(δ_l)`. -/
noncomputable def bI (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (i : Player) (l : ℕ) : ℝ :=
  if intervenes M φ₁ φ₂ x w i.other l then
    disc M (stage M φ₁ φ₂ x w l).τ * gain M (stage M φ₁ φ₂ x w l).δ else 0

section Lim
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

lemma disc_top : disc M ⊤ = 0 := by simp [disc]

lemma other_ne (i : Player) : i.other ≠ i := by cases i <;> decide

lemma eq_other_of_ne {i m : Player} (h : m ≠ i) : m = i.other := by
  cases i <;> cases m <;> first | rfl | exact absurd rfl h

/-- `Pay` in terms of `aI, bI` (for `l ≥ 1`). -/
lemma pay_eq (T : ℝ≥0) (i : Player) {l : ℕ} (hl : 1 ≤ l) :
    Pay M φ₁ φ₂ x w T i l = if (stage M φ₁ φ₂ x w l).τ ≤ (T : ENNReal) then
      aI M φ₁ φ₂ x w i l + bI M φ₁ φ₂ x w i l else 0 := by
  classical
  unfold Pay
  split_ifs with hT
  · have hτ : (stage M φ₁ φ₂ x w l).τ < ⊤ := lt_of_le_of_lt hT ENNReal.coe_lt_top
    have hd : disc M (stage M φ₁ φ₂ x w l).τ = exp (-M.ρ * (stage M φ₁ φ₂ x w l).τ.toReal) := by
      simp [disc, hτ]
    unfold aI bI intervenes payI
    by_cases hm : (stage M φ₁ φ₂ x w l).m = i
    · have hne : (stage M φ₁ φ₂ x w l).m ≠ i.other := by rw [hm]; exact (other_ne i).symm
      simp [hl, hτ, hm, hd, hne, other_ne i, (other_ne i).symm]
    · have ho := eq_other_of_ne hm
      simp [hl, hτ, hm, hd, ho, other_ne i]
  · rfl

lemma aI_nonpos (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (i : Player) (l : ℕ) :
    aI M φ₁ φ₂ x w i l ≤ 0 := by
  unfold aI
  split_ifs
  · have h1 : 0 ≤ disc M (stage M φ₁ φ₂ x w l).τ := by
      unfold disc; split_ifs <;> first | exact (exp_pos _).le | exact le_refl 0
    have h2 : cost M (stage M φ₁ φ₂ x w l).δ ≤ 0 := by
      unfold cost; nlinarith [abs_nonneg (stage M φ₁ φ₂ x w l).δ]
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  · exact le_refl 0

lemma bI_nonneg (hc : 0 ≤ M.ct) (hl : 0 ≤ M.lamt) (i : Player) (l : ℕ) :
    0 ≤ bI M φ₁ φ₂ x w i l := by
  unfold bI
  split_ifs
  · have h1 : 0 ≤ disc M (stage M φ₁ φ₂ x w l).τ := by
      unfold disc; split_ifs <;> first | exact (exp_pos _).le | exact le_refl 0
    have h2 : 0 ≤ gain M (stage M φ₁ φ₂ x w l).δ := by
      unfold gain; nlinarith [abs_nonneg (stage M φ₁ φ₂ x w l).δ]
    exact mul_nonneg h1 h2
  · exact le_refl 0

lemma aI_zero (i : Player) : aI M φ₁ φ₂ x w i 0 = 0 := by
  unfold aI; rw [if_neg]; intro h; exact absurd h.1 (by norm_num)

lemma bI_zero (i : Player) : bI M φ₁ φ₂ x w i 0 = 0 := by
  unfold bI; rw [if_neg]; intro h; exact absurd h.1 (by norm_num)

/-- The cost series in `aI` form. -/
lemma tsum_aI (i : Player) :
    ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) * cost M (deltaP M φ₁ φ₂ x w i (k + 1)) =
      ∑' l : ℕ, aI M φ₁ φ₂ x w i l := by
  classical
  have := tsum_tauP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i
    (fun τ δ => disc M τ * cost M δ) (by simp [disc_top])
  rw [this]
  unfold aI
  congr 1

lemma tsum_bI (i : Player) :
    ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
        gain M (deltaP M φ₁ φ₂ x w i.other (k + 1)) =
      ∑' l : ℕ, bI M φ₁ φ₂ x w i l := by
  classical
  have := tsum_tauP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i.other
    (fun τ δ => disc M τ * gain M δ) (by simp [disc_top])
  rw [this]
  unfold bI
  congr 1

lemma summable_aI (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (i : Player)
    (h : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|) :
    Summable fun l => aI M φ₁ φ₂ x w i l := by
  classical
  have h2 := (summable_tauP_iff (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i
    (fun τ δ => disc M τ * |cost M δ|) (by simp [disc_top])).1 h
  refine (h2.neg).congr fun l => ?_
  unfold aI
  split_ifs
  · have : cost M (stage M φ₁ φ₂ x w l).δ ≤ 0 := by
      unfold cost; nlinarith [abs_nonneg (stage M φ₁ φ₂ x w l).δ]
    rw [abs_of_nonpos this]; ring
  · simp

lemma summable_bI (hc : 0 ≤ M.ct) (hl : 0 ≤ M.lamt) (i : Player)
    (h : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
      |gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))|) :
    Summable fun l => bI M φ₁ φ₂ x w i l := by
  classical
  have h2 := (summable_tauP_iff (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i.other
    (fun τ δ => disc M τ * |gain M δ|) (by simp [disc_top])).1 h
  refine h2.congr fun l => ?_
  unfold bI
  split_ifs
  · have : 0 ≤ gain M (stage M φ₁ φ₂ x w l).δ := by
      unfold gain; nlinarith [abs_nonneg (stage M φ₁ φ₂ x w l).δ]
    rw [abs_of_nonneg this]
  · rfl

/-- `Σ'aI = -Σ' e^{-ρτ}|cost|` (the integrable cost series of `InPhi`). -/
lemma tsum_aI_eq_neg (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (i : Player) :
    ∑' l : ℕ, aI M φ₁ φ₂ x w i l = -∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))| := by
  rw [← tsum_aI, ← tsum_neg]
  congr 1
  funext k
  have : cost M (deltaP M φ₁ φ₂ x w i (k + 1)) ≤ 0 := by
    unfold cost; nlinarith [abs_nonneg (deltaP M φ₁ φ₂ x w i (k + 1))]
  rw [abs_of_nonpos this]; ring

/-- **Lower bound for the intervention sums.** -/
lemma pay_sum_lower (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt)
    (T : ℝ≥0) (i : Player) (ha : Summable fun l => aI M φ₁ φ₂ x w i l) (n : ℕ) :
    ∑' l : ℕ, aI M φ₁ φ₂ x w i l ≤ ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w T i (k + 1) := by
  have hpt : ∀ k, aI M φ₁ φ₂ x w i (k + 1) ≤ Pay M φ₁ φ₂ x w T i (k + 1) := by
    intro k
    rw [pay_eq T i (Nat.le_add_left 1 k)]
    split_ifs
    · linarith [bI_nonneg (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) hct hlt i (k + 1)]
    · exact aI_nonpos hc hl i (k + 1)
  have hs1 : Summable fun k => aI M φ₁ φ₂ x w i (k + 1) := (summable_nat_add_iff 1).2 ha
  rw [ha.tsum_eq_zero_add, aI_zero, zero_add]
  calc ∑' k, aI M φ₁ φ₂ x w i (k + 1) ≤ ∑ k ∈ Finset.range n, aI M φ₁ φ₂ x w i (k + 1) := by
        rw [← Summable.sum_add_tsum_nat_add n hs1]
        have : ∑' k, aI M φ₁ φ₂ x w i (k + n + 1) ≤ 0 :=
          tsum_nonpos fun k => aI_nonpos hc hl i (k + n + 1)
        linarith
    _ ≤ _ := Finset.sum_le_sum fun k _ => hpt k

/-- **Limit of the intervention sums** with `T = n`. -/
lemma pay_sum_tendsto (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt) (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam)
    (i : Player) (ha : Summable fun l => aI M φ₁ φ₂ x w i l)
    (hb : Summable fun l => bI M φ₁ φ₂ x w i l) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1)) atTop
      (𝓝 (∑' l, aI M φ₁ φ₂ x w i l + ∑' l, bI M φ₁ φ₂ x w i l)) := by
  classical
  set F : ℕ → ℕ → ℝ := fun n k => if k < n then Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1) else 0
    with hF
  set g : ℕ → ℝ := fun k => aI M φ₁ φ₂ x w i (k + 1) + bI M φ₁ φ₂ x w i (k + 1) with hg
  have hs1 : Summable fun k => aI M φ₁ φ₂ x w i (k + 1) := (summable_nat_add_iff 1).2 ha
  have hs2 : Summable fun k => bI M φ₁ φ₂ x w i (k + 1) := (summable_nat_add_iff 1).2 hb
  have hsum : ∀ n, ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1) = ∑' k, F n k := by
    intro n
    rw [(hasSum_sum_of_ne_finset_zero (s := Finset.range n) (f := F n) ?_).tsum_eq]
    · exact Finset.sum_congr rfl fun k hk => by
        simp only [hF, if_pos (Finset.mem_range.1 hk)]
    · intro k hk
      simp only [hF, if_neg (fun h => hk (Finset.mem_range.2 h))]
  have hlim : ∑' l, aI M φ₁ φ₂ x w i l + ∑' l, bI M φ₁ φ₂ x w i l = ∑' k, g k := by
    rw [ha.tsum_eq_zero_add, hb.tsum_eq_zero_add, aI_zero, bI_zero, zero_add, zero_add,
      hg, hs1.tsum_add hs2]
  simp only [hsum]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k =>
    |aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)|) (hs1.abs.add hs2.abs) ?_ ?_
  · intro k
    by_cases hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤
    · have hev : ∀ᶠ n : ℕ in atTop, F n k = g k := by
        obtain ⟨N, hN⟩ := exists_nat_ge (stage M φ₁ φ₂ x w (k + 1)).τ.toReal
        filter_upwards [eventually_ge_atTop (max N (k + 1))] with n hn
        have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans (le_max_right _ _) hn)
        have hτn : (stage M φ₁ φ₂ x w (k + 1)).τ ≤ ((n : ℝ≥0) : ENNReal) := by
          rw [← ENNReal.ofReal_toReal hτ.ne]
          have : (stage M φ₁ φ₂ x w (k + 1)).τ.toReal ≤ n :=
            le_trans hN (by exact_mod_cast le_trans (le_max_left _ _) hn)
          rw [show ((n : ℝ≥0) : ENNReal) = ENNReal.ofReal n by simp]
          exact ENNReal.ofReal_le_ofReal this
        simp only [hF, hg, if_pos hkn, pay_eq _ i (Nat.le_add_left 1 k), if_pos hτn]
      exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
    · have h0 : ∀ n : ℕ, F n k = 0 := by
        intro n
        simp only [hF]
        split_ifs
        · rw [pay_eq _ i (Nat.le_add_left 1 k), if_neg]
          intro h; exact hτ (lt_of_le_of_lt h ENNReal.coe_lt_top)
        · rfl
      have hg0 : g k = 0 := by
        simp only [hg, aI, bI, intervenes, hτ, false_and, and_false, ↓reduceIte, add_zero]
      rw [hg0]
      simp only [h0]
      exact tendsto_const_nhds
  · refine Eventually.of_forall fun n k => ?_
    simp only [hF, Real.norm_eq_abs]
    split_ifs
    · rw [pay_eq _ i (Nat.le_add_left 1 k)]
      split_ifs
      · exact abs_add_le _ _
      · simp only [abs_zero]; positivity
    · simp only [abs_zero]; positivity

/-- `σₙ = τₙ ∧ n → ∞`. -/
lemma sg_tendsto (h : ∀ j, Tendsto (fun k => tauP M φ₁ φ₂ x w j k) atTop (𝓝 ⊤)) :
    Tendsto (fun n : ℕ => (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) atTop atTop := by
  have hst := stage_tau_tendsto (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) h
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at hst
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [hst (N : ℝ≥0), eventually_ge_atTop N] with n h1 h2
  have hmin : ((N : ℝ≥0) : ENNReal) ≤ min (stage M φ₁ φ₂ x w n).τ ((n : ℝ≥0) : ENNReal) :=
    le_min h1.le (by exact_mod_cast h2)
  have : (N : ℝ≥0) ≤ sg M φ₁ φ₂ x w (n : ℝ≥0) n := by
    unfold sg
    exact ENNReal.le_toNNReal_of_coe_le hmin
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  calc b ≤ N := hN
    _ = ((N : ℝ≥0) : ℝ) := by simp
    _ ≤ _ := NNReal.coe_le_coe.2 this

end Lim


-- ===== from scratch/probe/2b17c77f_pb.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3g: the pathwise lower bound and limit for `Uₙ = V x + Σ_{k<n} (Δₖ + Rₖ)` -/

/-- `Uₙ` along one path, with `T = n`. -/
noncomputable def Up (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (i : Player) (u V : ℝ → ℝ) (n : ℕ) : ℝ :=
  V x + ∑ k ∈ Finset.range n, (Dl M φ₁ φ₂ x w (n : ℝ≥0) u k + Rk M φ₁ φ₂ x w (n : ℝ≥0) (runPay M i) k)

lemma continuous_runPay (M : Model) (i : Player) : Continuous (runPay M i) := by
  cases i
  · exact (continuous_id.sub continuous_const : Continuous fun y : ℝ => y - M.s₁)
  · exact (continuous_const.sub continuous_id : Continuous fun y : ℝ => M.s₂ - y)

lemma abs_interval_le_Ioi {g : ℝ → ℝ} (hg : MeasureTheory.IntegrableOn g (Set.Ioi 0)) {b : ℝ}
    (hb : 0 ≤ b) : |∫ r in (0 : ℝ)..b, g r| ≤ ∫ r in Set.Ioi (0 : ℝ), |g r| := by
  refine (intervalIntegral.abs_integral_le_integral_abs hb).trans ?_
  rw [intervalIntegral.integral_of_le hb]
  exact MeasureTheory.setIntegral_mono_set hg.abs
    (MeasureTheory.ae_of_all _ fun r => abs_nonneg _)
    (Set.Ioc_subset_Ioi_self.eventuallyLE)

section PB
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ}

theorem path_bounds (hw : Continuous w) (hρ : 0 < M.ρ) (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam)
    (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt) (i : Player) {u V ℓ : ℝ → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) ≤ V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) ≤ V y)
    (hVℓ : ∀ y, ℓ y ≤ V y) (hℓ : ∀ y, -(D * (1 + |y|)) ≤ ℓ y)
    (hℓ1 : ∀ y, y ∉ φ₁.C → ℓ y ≤ ℓ (y + φ₁.ξ y))
    (hℓ2 : ∀ y, y ∉ φ₂.C → ℓ y ≤ ℓ (y + φ₂.ξ y))
    (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S)
    (hrun : MeasureTheory.IntegrableOn
      (fun s : ℝ => exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)) (Set.Ioi 0))
    (hcs : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|)
    (hgs : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
      |gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))|)
    (htau : ∀ j, Tendsto (fun k => tauP M φ₁ φ₂ x w j k) atTop (𝓝 ⊤)) :
    (∀ n : ℕ, -((∫ s in Set.Ioi (0 : ℝ),
        |exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)|) +
        ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) * |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|
        + D * (1 + |x| + S)) ≤ Up M φ₁ φ₂ x w i u V n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, payoffPath M φ₁ φ₂ x w i - ε ≤ Up M φ₁ φ₂ x w i u V n) := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have hH1 : 0 ≤ D * (1 + |x| + S) := by positivity
  have ha := summable_aI hc hl i hcs
  have hb := summable_bI hct hlt i hgs
  -- the decomposition `Uₙ = Gₙ + ΣPay + Σslack + ∫₀^{σₙ}`
  have hdec : ∀ n : ℕ, Up M φ₁ φ₂ x w i u V n =
      Gk M φ₁ φ₂ x w (n : ℝ≥0) V n + ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1)
        + ∑ k ∈ Finset.range n, slack M φ₁ φ₂ x w (n : ℝ≥0) V i k
        + ∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
            exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal) := by
    intro n
    have h1 := tele_sum (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := (n : ℝ≥0))
      hw hVu i n
    have h2 := run_sum (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := (n : ℝ≥0))
      hw (continuous_runPay M i) n
    unfold Up
    rw [Finset.sum_add_distrib, h2, ← add_assoc, h1]
  have hslack : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, slack M φ₁ φ₂ x w (n : ℝ≥0) V i k :=
    fun n => Finset.sum_nonneg fun k _ => slack_nonneg hw i hJ1 hJ2 k
  have hG : ∀ n : ℕ, -(exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) * (D * (1 + |x| + S))) ≤
      Gk M φ₁ φ₂ x w (n : ℝ≥0) V n :=
    fun n => Gk_lower hw hD hS hVℓ hℓ hℓ1 hℓ2 n
  have hexp1 : ∀ n : ℕ, exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) ≤ 1 := fun n => by
    rw [Real.exp_le_one_iff]
    have := NNReal.coe_nonneg (sg M φ₁ φ₂ x w (n : ℝ≥0) n)
    nlinarith
  have hint : ∀ n : ℕ, |∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
      exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal)| ≤
      ∫ s in Set.Ioi (0 : ℝ), |exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)| :=
    fun n => abs_interval_le_Ioi hrun (NNReal.coe_nonneg _)
  have hpay : ∀ n : ℕ, -(∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|) ≤
      ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1) := fun n => by
    rw [← tsum_aI_eq_neg hc hl i]
    exact pay_sum_lower hc hl hct hlt _ i ha n
  refine ⟨fun n => ?_, fun ε hε => ?_⟩
  · rw [hdec n]
    have h1 := hG n
    have h2 := hexp1 n
    have h3 := hint n
    have h4 := hpay n
    have h5 := hslack n
    have h6 := neg_abs_le (∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
      exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal))
    have h7 : exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) * (D * (1 + |x| + S)) ≤
        D * (1 + |x| + S) := by
      nlinarith
    linarith
  · -- the limit
    have hsg := sg_tendsto (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) htau
    have hR : Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
        exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal)) atTop
        (𝓝 (runPath M φ₁ φ₂ x w i)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hrun hsg
    have hP := pay_sum_tendsto hct hlt hc hl i ha hb
    have hsum := hR.add hP
    have hpp : payoffPath M φ₁ φ₂ x w i = runPath M φ₁ φ₂ x w i +
        (∑' l, aI M φ₁ φ₂ x w i l + ∑' l, bI M φ₁ φ₂ x w i l) := by
      unfold payoffPath
      rw [tsum_aI, tsum_bI]
      ring
    rw [← hpp] at hsum
    have hexp : Tendsto (fun n : ℕ => exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) *
        (D * (1 + |x| + S))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (Filter.Tendsto.neg_mul_atTop (by linarith : -M.ρ < 0)
          tendsto_const_nhds hsg)
      simpa using this.mul_const (D * (1 + |x| + S))
    have e1 := hsum.eventually (lt_mem_nhds (show payoffPath M φ₁ φ₂ x w i - ε / 2 <
      payoffPath M φ₁ φ₂ x w i by linarith))
    have e2 := hexp.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [e1, e2] with n h1 h2
    rw [hdec n]
    have := hG n
    have := hslack n
    linarith

end PB


-- ===== from scratch/probe/2b17c77f_d3.lean =====


open ImpulseGames.LinearGame

/-! ## Part D3: the verification inequality for an arbitrary admissible pair -/

lemma runPay_lin (M : Model) (i : Player) (y : ℝ) :
    |runPay M i y| ≤ (1 + |M.s₁| + |M.s₂|) * (1 + |y|) := by
  have h1 := abs_nonneg y
  have h2 := abs_nonneg M.s₁
  have h3 := abs_nonneg M.s₂
  cases i
  · have : |y - M.s₁| ≤ |y| + |M.s₁| := abs_sub _ _
    show |y - M.s₁| ≤ _
    nlinarith
  · have : |M.s₂ - y| ≤ |M.s₂| + |y| := abs_sub _ _
    show |M.s₂ - y| ≤ _
    nlinarith

/-- **Verification inequality (Step 1 of Theorem 3.3, linear game).** Let `u` be a regular
function equal to `V` on the closure of `C₁ ∩ C₂`, with `σ²/2 u'' - ρu + fᵢ ≤ 0` on `C₁ ∩ C₂`,
let the jumps of both players satisfy `V(y + ξ(y)) + payᵢ ≤ V(y)` off their continuation
regions, and let `ℓ ≤ V` be a linearly bounded function not decreased by the jumps. Then for an
admissible pair, `Jⁱ(x; φ₁, φ₂) ≤ V(x)`. -/
theorem deviation_le {u u1 u2 : ℝ → ℝ} {S₀ : Set ℝ} {C K D E : ℝ} (M : Model) (hσ : M.σ ≠ 0)
    (hρ : 0 < M.ρ) (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt)
    (hR : Reg u u1 u2 S₀ C K) (hl0 : ∀ y, |u y| ≤ D * (1 + |y|))
    (hl2 : ∀ y, |u2 y| ≤ D * (1 + |y|)) (hE : 0 ≤ E)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (i : Player) (V ℓ : ℝ → ℝ)
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y)
    (hgen : ∀ y ∈ φ₁.C ∩ φ₂.C, M.σ ^ 2 / 2 * u2 y - M.ρ * u y + runPay M i y ≤ 0)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) ≤ V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) ≤ V y)
    (hVℓ : ∀ y, ℓ y ≤ V y) (hℓ : ∀ y, -(E * (1 + |y|)) ≤ ℓ y)
    (hℓ1 : ∀ y, y ∉ φ₁.C → ℓ y ≤ ℓ (y + φ₁.ξ y))
    (hℓ2 : ∀ y, y ∉ φ₂.C → ℓ y ≤ ℓ (y + φ₂.ξ y))
    (hΦ : InPhi M P W x φ₁ φ₂) :
    J M P W x φ₁ φ₂ i ≤ V x := by
  classical
  obtain ⟨B, hBm, hBc, hWB, hBB⟩ := exists_good_version hW
  have hB : IsPreBrownianReal B P := hBB.toIsPreBrownianReal
  have hpath : ∀ᵐ ω ∂P, (fun t => W t ω) = (fun t => B t ω) := hWB.mono fun ω h => funext h
  -- the supremum of the controlled process
  set Sup : Ω → ENNReal := fun ω => ⨆ t : ℝ≥0,
    ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t| with hSupdef
  have hSm : AEMeasurable Sup P := hΦ.sup_aemeasurable
  have hSfin : ∫⁻ ω, Sup ω ∂P ≠ ⊤ := by
    have := hΦ.sup_moments 1
    simp only [pow_one] at this
    exact this.ne
  set S : Ω → ℝ := fun ω => (Sup ω).toReal with hSdef
  have hSi : Integrable S P := integrable_toReal_of_lintegral_ne_top hSm hSfin
  have hSlt : ∀ᵐ ω ∂P, Sup ω < ⊤ := ae_lt_top' hSm hSfin
  have hSb : ∀ᵐ ω ∂P, ∀ t, |ctrlX M φ₁ φ₂ x (fun t => B t ω) t| ≤ S ω := by
    filter_upwards [hSlt, hpath] with ω h hp t
    rw [← hp]
    have h1 : ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t| ≤ Sup ω :=
      le_iSup (fun t => ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t|) t
    have := ENNReal.toReal_mono h.ne h1
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  -- integrability of the stage quantities
  have hYi : ∀ n k : ℕ, Integrable (fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) k) P :=
    fun n k => hSi.mono' (Ys_meas hBm hBc M φ₁ φ₂ x _ k).aestronglyMeasurable
      (hSb.mono fun ω h => by rw [Real.norm_eq_abs]; exact Ys_bound M φ₁ φ₂ x h _ k)
  have hLm : Measurable fun y => M.σ ^ 2 / 2 * u2 y - M.ρ * u y :=
    (hR.m2.const_mul _).sub (hR.cont.measurable.const_mul _)
  have hL : ∀ y, |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤
      ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by
    intro y
    have h1 := hl0 y
    have h2 := hl2 y
    have hs : 0 ≤ M.σ ^ 2 / 2 := by positivity
    calc |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤ |M.σ ^ 2 / 2 * u2 y| + |M.ρ * u y| := abs_sub _ _
      _ = M.σ ^ 2 / 2 * |u2 y| + |M.ρ| * |u y| := by rw [abs_mul, abs_mul, abs_of_nonneg hs]
      _ ≤ M.σ ^ 2 / 2 * (D * (1 + |y|)) + |M.ρ| * (D * (1 + |y|)) := by gcongr
      _ = ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by ring
  have hDl : ∀ n k : ℕ, Integrable (fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k) P :=
    fun n k => Dl_integrable hBm hBc M φ₁ φ₂ x hB hR.cont hl0 n k (hYi n k)
  have hRk : ∀ n k : ℕ, Integrable (fun ω =>
      Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) P :=
    fun n k => stage_int_integrable hBm hBc M φ₁ φ₂ x hB (continuous_runPay M i).measurable
      (runPay_lin M i) n k (hYi n k)
  have hDyn : ∀ n k : ℕ, Integrable (fun ω =>
      Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k) P :=
    fun n k => stage_int_integrable hBm hBc M φ₁ φ₂ x hB hLm hL n k (hYi n k)
  have hEq : ∀ n k : ℕ, ∫ ω, Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k ∂P =
      ∫ ω, Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k ∂P :=
    fun n k => stage_dynkin M hσ hR hl0 hl2 hB hBm hBc φ₁ φ₂ x k n (hYi n k)
  have hstep : ∀ n k : ℕ, ∫ ω, (Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
      Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) ∂P ≤ 0 := by
    intro n k
    rw [integral_add (hDl n k) (hRk n k), hEq n k, ← integral_add (hDyn n k) (hRk n k)]
    exact integral_nonpos fun ω => gen_le (hBc ω) hR.cont.measurable hl0 hR.m2 hl2
      (continuous_runPay M i) hgen k
  have hsumi : ∀ n : ℕ, Integrable (fun ω => ∑ k ∈ Finset.range n,
      (Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
        Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k)) P :=
    fun n => integrable_finset_sum _ fun k _ => (hDl n k).add (hRk n k)
  have hUi : ∀ n : ℕ, Integrable (fun ω => Up M φ₁ φ₂ x (fun s => B s ω) i u V n) P :=
    fun n => (integrable_const (V x)).add (hsumi n)
  have hUb : ∀ n : ℕ, ∫ ω, Up M φ₁ φ₂ x (fun s => B s ω) i u V n ∂P ≤ V x := by
    intro n
    have hik : ∀ k : ℕ, Integrable (fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
        Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) P :=
      fun k => (hDl n k).add (hRk n k)
    unfold Up
    rw [integral_add (integrable_const _) (hsumi n),
      integral_finset_sum _ fun k _ => hik k]
    have hc1 : ∫ _ω, V x ∂P = V x := by simp
    rw [hc1]
    have := Finset.sum_nonpos fun k (_ : k ∈ Finset.range n) => hstep n k
    linarith
  -- the integrable lower bound
  set A : Ω → ℝ := fun ω => ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-M.ρ * s) * |runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal)| with hAdef
  have hAi : Integrable A P := hΦ.run_abs_integrable i
  set Cs : Ω → ℝ := fun ω => ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
    |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))| with hCsdef
  have hCi : Integrable Cs P := hΦ.cost_integrable i
  set H : Ω → ℝ := fun ω => A ω + Cs ω + E * (1 + |x| + S ω) with hHdef
  have hHi : Integrable H P :=
    (hAi.add hCi).add (((integrable_const (1 + |x|)).add hSi).const_mul E)
  -- the pathwise facts at good `ω`
  have hgood : ∀ᵐ ω ∂P, (fun t => W t ω) = (fun t => B t ω) ∧
      (∀ t, |ctrlX M φ₁ φ₂ x (fun t => B t ω) t| ≤ S ω) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => exp (-M.ρ * s) *
        runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal)) (Set.Ioi 0) ∧
      Summable (fun k : ℕ => disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
        |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|) ∧
      Summable (fun k : ℕ => disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) *
        |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1))|) ∧
      Tendsto (fun k : ℕ => tauP M φ₁ φ₂ x (fun t => W t ω) .one k) atTop (𝓝 ⊤) ∧
      Tendsto (fun k : ℕ => tauP M φ₁ φ₂ x (fun t => W t ω) .two k) atTop (𝓝 ⊤) := by
    filter_upwards [hpath, hSb, hΦ.run_integrableOn i, hΦ.cost_summable i,
      hΦ.gain_summable i.other, hΦ.tau_tendsto .one, hΦ.tau_tendsto .two]
      with ω h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hpb : ∀ᵐ ω ∂P, (∀ n : ℕ, -H ω ≤ Up M φ₁ φ₂ x (fun s => B s ω) i u V n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        payoffPath M φ₁ φ₂ x (fun t => W t ω) i - ε ≤ Up M φ₁ φ₂ x (fun s => B s ω) i u V n) := by
    filter_upwards [hgood] with ω ⟨hp, hS, hr, hcs, hgs, ht1, ht2⟩
    rw [hp] at hr hcs hgs ht1 ht2
    have htau : ∀ j, Tendsto (fun k => tauP M φ₁ φ₂ x (fun t => B t ω) j k) atTop (𝓝 ⊤) := by
      intro j; cases j
      · exact ht1
      · exact ht2
    have h := path_bounds (hBc ω) hρ hc hl hct hlt i hE hVu hJ1 hJ2 hVℓ hℓ hℓ1 hℓ2 hS hr hcs hgs
      htau
    have hA : A ω = ∫ s in Set.Ioi (0 : ℝ),
        |exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x (fun t => B t ω) s.toNNReal)| := by
      simp only [hAdef, hp]
      congr 1
      funext s
      rw [abs_mul, abs_of_pos (exp_pos _)]
    have hC : Cs ω = ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => B t ω) i (k + 1)) *
        |cost M (deltaP M φ₁ φ₂ x (fun t => B t ω) i (k + 1))| := by
      simp only [hCsdef, hp]
    refine ⟨fun n => ?_, fun ε hε => ?_⟩
    · have := h.1 n
      simp only [hHdef]
      rw [hA, hC]
      exact this
    · rw [hp]
      exact h.2 ε hε
  -- integrability of the payoff
  have hfi : Integrable (fun ω => payoffPath M φ₁ φ₂ x (fun t => W t ω) i) P := by
    have hrunI : Integrable (fun ω => runPath M φ₁ φ₂ x (fun t => W t ω) i) P := by
      refine hAi.mono' (hΦ.run_aestronglyMeasurable i) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      unfold runPath
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      simp only [hAdef]
      congr 1
      funext s
      rw [abs_mul, abs_of_pos (exp_pos _)]
    have hGi := hΦ.gain_integrable i.other
    refine ((hrunI.add hCi.neg).add hGi).congr (Eventually.of_forall fun ω => ?_)
    simp only [payoffPath, Pi.add_apply, Pi.neg_apply, hCsdef]
    have e1 : ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
        cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) =
        -∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
          |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))| := by
      rw [← tsum_neg]
      congr 1
      funext k
      have : cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) ≤ 0 := by
        unfold cost; nlinarith [abs_nonneg (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))]
      rw [abs_of_nonpos this]; ring
    have e2 : ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) *
        gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) =
        ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) *
          |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1))| := by
      congr 1
      funext k
      have : 0 ≤ gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) := by
        unfold gain; nlinarith [abs_nonneg (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1))]
      rw [abs_of_nonneg this]
    rw [e1, e2]
  exact fatou_le hUi hHi hfi (fun n => hpb.mono fun ω h => h.1 n) (hpb.mono fun ω h => h.2) hUb


-- ===== from scratch/probe/2b17c77f_d4.lean =====


open ImpulseGames.LinearGame

/-! ## Part D4: the payoff identity `Jⁱ = V(x)` when the QVI holds with equality along the pair -/

section D4p
variable {M : Model} {φ₁ : Strategy Z₁} {φ₂ : Strategy Z₂} {x : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}

lemma slack_zero (hw : Continuous w) {V : ℝ → ℝ} (i : Player)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) = V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) = V y) (k : ℕ) :
    slack M φ₁ φ₂ x w T V i k = 0 := by
  unfold slack
  split_ifs with hT
  · have hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤ := lt_of_le_of_lt hT ENNReal.coe_lt_top
    obtain ⟨hx, hm⟩ := jump_facts hw k hτ
    rw [hx]
    rcases hm with ⟨hm, hC, hδ⟩ | ⟨hm, hC, hδ⟩
    · rw [hm, hδ]
      have h := hJ1 _ hC
      rw [mul_eq_zero]; right; linarith
    · rw [hm, hδ]
      have h := hJ2 _ hC
      rw [mul_eq_zero]; right; linarith
  · rfl

lemma Gk_abs (hw : Continuous w) {V : ℝ → ℝ} {E E₀ S : ℝ} (hE : 0 ≤ E) (hE₀ : 0 ≤ E₀)
    (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S) (hVlin : ∀ y, |V y| ≤ E * (1 + |y|))
    (hp1 : ∀ y, y ∉ φ₁.C → |V (y + φ₁.ξ y)| ≤ E₀)
    (hp2 : ∀ y, y ∉ φ₂.C → |V (y + φ₂.ξ y)| ≤ E₀) (K : ℕ) :
    |Gk M φ₁ φ₂ x w T V K| ≤
      exp (-M.ρ * (sg M φ₁ φ₂ x w T K : ℝ)) * (E * (1 + |x|) + E₀ + E * (1 + S)) := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have h1 : 0 ≤ E * (1 + |x|) := by positivity
  have h2 : 0 ≤ E * (1 + S) := by positivity
  have hb : |V (St M φ₁ φ₂ x w T K)| ≤ E * (1 + |x|) + E₀ + E * (1 + S) := by
    unfold St
    split_ifs with hK
    · rcases K with _ | k
      · have : |V x| ≤ E * (1 + |x|) := hVlin x
        show |V x| ≤ _
        linarith
      · have hτ : (stage M φ₁ φ₂ x w (k + 1)).τ < ⊤ := lt_of_le_of_lt hK ENNReal.coe_lt_top
        obtain ⟨hx, hm⟩ := jump_facts hw k hτ
        rw [hx]
        rcases hm with ⟨_, hC, hδ⟩ | ⟨_, hC, hδ⟩
        · rw [hδ]; have := hp1 _ hC; linarith
        · rw [hδ]; have := hp2 _ hC; linarith
    · have a1 := hVlin (ctrlX M φ₁ φ₂ x w T)
      have a2 := hS T
      have a3 : E * (1 + |ctrlX M φ₁ φ₂ x w T|) ≤ E * (1 + S) :=
        mul_le_mul_of_nonneg_left (by linarith) hE
      linarith
  unfold Gk
  rw [abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_mul_of_nonneg_left hb (exp_pos _).le

lemma disc_nonneg (τ : ENNReal) : 0 ≤ disc M τ := by
  unfold disc; split_ifs <;> first | exact (exp_pos _).le | exact le_refl 0

lemma tsum_abs_aI (i : Player) :
    ∑' l : ℕ, |aI M φ₁ φ₂ x w i l| = ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))| := by
  classical
  rw [tsum_tauP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i
    (fun τ δ => disc M τ * |cost M δ|) (by simp [disc_top])]
  congr 1
  funext l
  unfold aI
  split_ifs
  · rw [abs_mul, abs_of_nonneg (disc_nonneg _)]
  · simp

lemma tsum_abs_bI (i : Player) :
    ∑' l : ℕ, |bI M φ₁ φ₂ x w i l| = ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
      |gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))| := by
  classical
  rw [tsum_tauP (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) i.other
    (fun τ δ => disc M τ * |gain M δ|) (by simp [disc_top])]
  congr 1
  funext l
  unfold bI
  split_ifs
  · rw [abs_mul, abs_of_nonneg (disc_nonneg _)]
  · simp

lemma pay_sum_abs (i : Player) (ha : Summable fun l => aI M φ₁ φ₂ x w i l)
    (hb : Summable fun l => bI M φ₁ φ₂ x w i l) (n : ℕ) :
    |∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w T i (k + 1)| ≤
      ∑' l, |aI M φ₁ φ₂ x w i l| + ∑' l, |bI M φ₁ φ₂ x w i l| := by
  have hpt : ∀ k, |Pay M φ₁ φ₂ x w T i (k + 1)| ≤
      |aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)| := by
    intro k
    rw [pay_eq T i (Nat.le_add_left 1 k)]
    split_ifs
    · exact abs_add_le _ _
    · simp only [abs_zero]; positivity
  have hs : Summable fun k => |aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)| :=
    ((summable_nat_add_iff 1).2 ha.abs).add ((summable_nat_add_iff 1).2 hb.abs)
  have htail : ∑ k ∈ Finset.range n, (|aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)|) ≤
      ∑' k, (|aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)|) := by
    rw [← Summable.sum_add_tsum_nat_add n hs]
    have : 0 ≤ ∑' k, (|aI M φ₁ φ₂ x w i (k + n + 1)| + |bI M φ₁ φ₂ x w i (k + n + 1)|) :=
      tsum_nonneg fun k => by positivity
    linarith
  have hsplit : ∑' k, (|aI M φ₁ φ₂ x w i (k + 1)| + |bI M φ₁ φ₂ x w i (k + 1)|) =
      ∑' l, |aI M φ₁ φ₂ x w i l| + ∑' l, |bI M φ₁ φ₂ x w i l| := by
    rw [ha.abs.tsum_eq_zero_add, hb.abs.tsum_eq_zero_add, aI_zero, bI_zero, abs_zero, zero_add,
      zero_add, ((summable_nat_add_iff 1).2 ha.abs).tsum_add ((summable_nat_add_iff 1).2 hb.abs)]
  calc |∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w T i (k + 1)|
      ≤ ∑ k ∈ Finset.range n, |Pay M φ₁ φ₂ x w T i (k + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun k _ => hpt k
    _ ≤ _ := htail
    _ = _ := hsplit

theorem path_eq (hw : Continuous w) (hρ : 0 < M.ρ) (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam)
    (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt) (i : Player) {u V : ℝ → ℝ} {E E₀ S : ℝ}
    (hE : 0 ≤ E) (hE₀ : 0 ≤ E₀)
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) = V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) = V y)
    (hVlin : ∀ y, |V y| ≤ E * (1 + |y|))
    (hp1 : ∀ y, y ∉ φ₁.C → |V (y + φ₁.ξ y)| ≤ E₀)
    (hp2 : ∀ y, y ∉ φ₂.C → |V (y + φ₂.ξ y)| ≤ E₀)
    (hS : ∀ t, |ctrlX M φ₁ φ₂ x w t| ≤ S)
    (hrun : MeasureTheory.IntegrableOn
      (fun s : ℝ => exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)) (Set.Ioi 0))
    (hcs : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i (k + 1)) *
      |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|)
    (hgs : Summable fun k : ℕ => disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
      |gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))|)
    (htau : ∀ j, Tendsto (fun k => tauP M φ₁ φ₂ x w j k) atTop (𝓝 ⊤)) :
    (∀ n : ℕ, |Up M φ₁ φ₂ x w i u V n| ≤ (∫ s in Set.Ioi (0 : ℝ),
        |exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)|) +
        (∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) * |cost M (deltaP M φ₁ φ₂ x w i (k + 1))|
          + ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i.other (k + 1)) *
            |gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))|)
        + (E * (1 + |x|) + E₀ + E * (1 + S))) ∧
    Tendsto (fun n => Up M φ₁ φ₂ x w i u V n) atTop (𝓝 (payoffPath M φ₁ φ₂ x w i)) := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have hH1 : 0 ≤ E * (1 + |x|) + E₀ + E * (1 + S) := by positivity
  have ha := summable_aI hc hl i hcs
  have hb := summable_bI hct hlt i hgs
  have hdec : ∀ n : ℕ, Up M φ₁ φ₂ x w i u V n =
      Gk M φ₁ φ₂ x w (n : ℝ≥0) V n + ∑ k ∈ Finset.range n, Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1)
        + ∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
            exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal) := by
    intro n
    have h1 := tele_sum (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := (n : ℝ≥0))
      hw hVu i n
    have h2 := run_sum (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) (T := (n : ℝ≥0))
      hw (continuous_runPay M i) n
    have h3 : ∑ k ∈ Finset.range n, slack M φ₁ φ₂ x w (n : ℝ≥0) V i k = 0 :=
      Finset.sum_eq_zero fun k _ => slack_zero hw i hJ1 hJ2 k
    unfold Up
    rw [Finset.sum_add_distrib, h2, ← add_assoc, h1, h3, add_zero]
  have hG : ∀ n : ℕ, |Gk M φ₁ φ₂ x w (n : ℝ≥0) V n| ≤
      exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) * (E * (1 + |x|) + E₀ + E * (1 + S)) :=
    fun n => Gk_abs hw hE hE₀ hS hVlin hp1 hp2 n
  have hexp1 : ∀ n : ℕ, exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) ≤ 1 := fun n => by
    rw [Real.exp_le_one_iff]
    have := NNReal.coe_nonneg (sg M φ₁ φ₂ x w (n : ℝ≥0) n)
    nlinarith
  refine ⟨fun n => ?_, ?_⟩
  · rw [hdec n]
    have h1 := hG n
    have h2 := hexp1 n
    have h3 := abs_interval_le_Ioi hrun (NNReal.coe_nonneg (sg M φ₁ φ₂ x w (n : ℝ≥0) n))
    have h4 := pay_sum_abs (T := (n : ℝ≥0)) i ha hb n
    rw [tsum_abs_aI, tsum_abs_bI] at h4
    have h5 : exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) *
        (E * (1 + |x|) + E₀ + E * (1 + S)) ≤ E * (1 + |x|) + E₀ + E * (1 + S) := by nlinarith
    calc _ ≤ |Gk M φ₁ φ₂ x w (n : ℝ≥0) V n + ∑ k ∈ Finset.range n,
            Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1)| + |∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
            exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal)| := abs_add_le _ _
      _ ≤ |Gk M φ₁ φ₂ x w (n : ℝ≥0) V n| + |∑ k ∈ Finset.range n,
            Pay M φ₁ φ₂ x w (n : ℝ≥0) i (k + 1)| + |∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
            exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  · have hsg := sg_tendsto (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (w := w) htau
    have hR : Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ),
        exp (-M.ρ * r) * runPay M i (ctrlX M φ₁ φ₂ x w r.toNNReal)) atTop
        (𝓝 (runPath M φ₁ φ₂ x w i)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hrun hsg
    have hP := pay_sum_tendsto hct hlt hc hl i ha hb
    have hexp : Tendsto (fun n : ℕ => exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ)) *
        (E * (1 + |x|) + E₀ + E * (1 + S))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => exp (-M.ρ * (sg M φ₁ φ₂ x w (n : ℝ≥0) n : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (Filter.Tendsto.neg_mul_atTop (by linarith : -M.ρ < 0)
          tendsto_const_nhds hsg)
      simpa using this.mul_const (E * (1 + |x|) + E₀ + E * (1 + S))
    have hG0 : Tendsto (fun n : ℕ => Gk M φ₁ φ₂ x w (n : ℝ≥0) V n) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hG n) hexp
    have hpp : payoffPath M φ₁ φ₂ x w i = 0 + (∑' l, aI M φ₁ φ₂ x w i l +
        ∑' l, bI M φ₁ φ₂ x w i l) + runPath M φ₁ φ₂ x w i := by
      unfold payoffPath
      rw [tsum_aI, tsum_bI]
      ring
    rw [hpp]
    have := (hG0.add hP).add hR
    refine this.congr fun n => ?_
    rw [hdec n]

end D4p


-- ===== from scratch/probe/2b17c77f_d4b.lean =====


open ImpulseGames.LinearGame

/-! ## Part D4b: the payoff identity in `ω` -/

/-- **Payoff identity (Step 2 of Theorem 3.3, linear game).** If the generator equation holds on
`C₁ ∩ C₂` and the jumps of both players satisfy `V(y + ξ(y)) + payᵢ = V(y)` with bounded
post-jump values, then for an admissible pair `Jⁱ(x; φ₁, φ₂) = V(x)`. -/
theorem payoff_eq {u u1 u2 : ℝ → ℝ} {S₀ : Set ℝ} {C K D E E₀ : ℝ} (M : Model) (hσ : M.σ ≠ 0)
    (hρ : 0 < M.ρ) (hc : 0 ≤ M.c) (hl : 0 ≤ M.lam) (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt)
    (hR : Reg u u1 u2 S₀ C K) (hl0 : ∀ y, |u y| ≤ D * (1 + |y|))
    (hl2 : ∀ y, |u2 y| ≤ D * (1 + |y|)) (hE : 0 ≤ E) (hE₀ : 0 ≤ E₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (i : Player) (V : ℝ → ℝ)
    (hVu : ∀ y ∈ closure (φ₁.C ∩ φ₂.C), u y = V y)
    (hgen : ∀ y ∈ φ₁.C ∩ φ₂.C, M.σ ^ 2 / 2 * u2 y - M.ρ * u y + runPay M i y = 0)
    (hJ1 : ∀ y, y ∉ φ₁.C → V (y + φ₁.ξ y) + payI M i .one (φ₁.ξ y) = V y)
    (hJ2 : ∀ y, y ∉ φ₂.C → V (y + φ₂.ξ y) + payI M i .two (φ₂.ξ y) = V y)
    (hVlin : ∀ y, |V y| ≤ E * (1 + |y|))
    (hp1 : ∀ y, y ∉ φ₁.C → |V (y + φ₁.ξ y)| ≤ E₀)
    (hp2 : ∀ y, y ∉ φ₂.C → |V (y + φ₂.ξ y)| ≤ E₀)
    (hΦ : InPhi M P W x φ₁ φ₂) :
    J M P W x φ₁ φ₂ i = V x := by
  classical
  obtain ⟨B, hBm, hBc, hWB, hBB⟩ := exists_good_version hW
  have hB : IsPreBrownianReal B P := hBB.toIsPreBrownianReal
  have hpath : ∀ᵐ ω ∂P, (fun t => W t ω) = (fun t => B t ω) := hWB.mono fun ω h => funext h
  -- the supremum of the controlled process
  set Sup : Ω → ENNReal := fun ω => ⨆ t : ℝ≥0,
    ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t| with hSupdef
  have hSm : AEMeasurable Sup P := hΦ.sup_aemeasurable
  have hSfin : ∫⁻ ω, Sup ω ∂P ≠ ⊤ := by
    have := hΦ.sup_moments 1
    simp only [pow_one] at this
    exact this.ne
  set S : Ω → ℝ := fun ω => (Sup ω).toReal with hSdef
  have hSi : Integrable S P := integrable_toReal_of_lintegral_ne_top hSm hSfin
  have hSlt : ∀ᵐ ω ∂P, Sup ω < ⊤ := ae_lt_top' hSm hSfin
  have hSb : ∀ᵐ ω ∂P, ∀ t, |ctrlX M φ₁ φ₂ x (fun t => B t ω) t| ≤ S ω := by
    filter_upwards [hSlt, hpath] with ω h hp t
    rw [← hp]
    have h1 : ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t| ≤ Sup ω :=
      le_iSup (fun t => ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t|) t
    have := ENNReal.toReal_mono h.ne h1
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  -- integrability of the stage quantities
  have hYi : ∀ n k : ℕ, Integrable (fun ω => Ys M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) k) P :=
    fun n k => hSi.mono' (Ys_meas hBm hBc M φ₁ φ₂ x _ k).aestronglyMeasurable
      (hSb.mono fun ω h => by rw [Real.norm_eq_abs]; exact Ys_bound M φ₁ φ₂ x h _ k)
  have hLm : Measurable fun y => M.σ ^ 2 / 2 * u2 y - M.ρ * u y :=
    (hR.m2.const_mul _).sub (hR.cont.measurable.const_mul _)
  have hL : ∀ y, |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤
      ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by
    intro y
    have h1 := hl0 y
    have h2 := hl2 y
    have hs : 0 ≤ M.σ ^ 2 / 2 := by positivity
    calc |M.σ ^ 2 / 2 * u2 y - M.ρ * u y| ≤ |M.σ ^ 2 / 2 * u2 y| + |M.ρ * u y| := abs_sub _ _
      _ = M.σ ^ 2 / 2 * |u2 y| + |M.ρ| * |u y| := by rw [abs_mul, abs_mul, abs_of_nonneg hs]
      _ ≤ M.σ ^ 2 / 2 * (D * (1 + |y|)) + |M.ρ| * (D * (1 + |y|)) := by gcongr
      _ = ((M.σ ^ 2 / 2 + |M.ρ|) * D) * (1 + |y|) := by ring
  have hDl : ∀ n k : ℕ, Integrable (fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k) P :=
    fun n k => Dl_integrable hBm hBc M φ₁ φ₂ x hB hR.cont hl0 n k (hYi n k)
  have hRk : ∀ n k : ℕ, Integrable (fun ω =>
      Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) P :=
    fun n k => stage_int_integrable hBm hBc M φ₁ φ₂ x hB (continuous_runPay M i).measurable
      (runPay_lin M i) n k (hYi n k)
  have hDyn : ∀ n k : ℕ, Integrable (fun ω =>
      Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k) P :=
    fun n k => stage_int_integrable hBm hBc M φ₁ φ₂ x hB hLm hL n k (hYi n k)
  have hEq : ∀ n k : ℕ, ∫ ω, Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k ∂P =
      ∫ ω, Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k ∂P :=
    fun n k => stage_dynkin M hσ hR hl0 hl2 hB hBm hBc φ₁ φ₂ x k n (hYi n k)
  have hz : ∀ n k : ℕ, ∀ ω, Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k +
      Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k = 0 := by
    intro n k ω
    have h1 := gen_le (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (T := (n : ℝ≥0)) (hBc ω) hR.cont.measurable hl0 hR.m2 hl2
      (continuous_runPay M i) (fun y hy => (hgen y hy).le) k
    have h2 := gen_le (M := M) (φ₁ := φ₁) (φ₂ := φ₂) (x := x) (T := (n : ℝ≥0)) (u := fun y => -u y) (u2 := fun y => -u2 y)
      (f := fun y => -runPay M i y) (hBc ω) hR.cont.measurable.neg
      (fun y => by rw [abs_neg]; exact hl0 y) hR.m2.neg (fun y => by rw [abs_neg]; exact hl2 y)
      (continuous_runPay M i).neg (fun y hy => by have := hgen y hy; linarith) k
    have e1 : Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (fun y => -u y) (fun y => -u2 y) k =
        -Dyn M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u u2 k := by
      unfold Dyn
      rw [← intervalIntegral.integral_neg]
      congr 1; funext r; ring
    have e2 : Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (fun y => -runPay M i y) k =
        -Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k := by
      unfold Rk
      rw [← intervalIntegral.integral_neg]
      congr 1; funext r; ring
    rw [e1, e2] at h2
    linarith
  have hstep : ∀ n k : ℕ, ∫ ω, (Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
      Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) ∂P = 0 := by
    intro n k
    rw [integral_add (hDl n k) (hRk n k), hEq n k, ← integral_add (hDyn n k) (hRk n k)]
    simp only [hz n k, integral_zero]
  have hsumi : ∀ n : ℕ, Integrable (fun ω => ∑ k ∈ Finset.range n,
      (Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
        Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k)) P :=
    fun n => integrable_finset_sum _ fun k _ => (hDl n k).add (hRk n k)
  have hUi : ∀ n : ℕ, Integrable (fun ω => Up M φ₁ φ₂ x (fun s => B s ω) i u V n) P :=
    fun n => (integrable_const (V x)).add (hsumi n)
  have hUb : ∀ n : ℕ, ∫ ω, Up M φ₁ φ₂ x (fun s => B s ω) i u V n ∂P = V x := by
    intro n
    have hik : ∀ k : ℕ, Integrable (fun ω => Dl M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) u k +
        Rk M φ₁ φ₂ x (fun s => B s ω) (n : ℝ≥0) (runPay M i) k) P :=
      fun k => (hDl n k).add (hRk n k)
    unfold Up
    rw [integral_add (integrable_const _) (hsumi n),
      integral_finset_sum _ fun k _ => hik k]
    have hc1 : ∫ _ω, V x ∂P = V x := by simp
    rw [hc1, Finset.sum_eq_zero fun k _ => hstep n k, add_zero]
  -- domination
  set A : Ω → ℝ := fun ω => ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-M.ρ * s) * |runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal)| with hAdef
  have hAi : Integrable A P := hΦ.run_abs_integrable i
  set Cs : Ω → ℝ := fun ω => ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
    |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))| with hCsdef
  have hCi : Integrable Cs P := hΦ.cost_integrable i
  set Gs : Ω → ℝ := fun ω => ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) *
    |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1))| with hGsdef
  have hGi : Integrable Gs P := hΦ.gain_integrable i.other
  set H : Ω → ℝ := fun ω => A ω + (Cs ω + Gs ω) + (E * (1 + |x|) + E₀ + E * (1 + S ω))
    with hHdef
  have hHi : Integrable H P :=
    (hAi.add (hCi.add hGi)).add ((integrable_const (E * (1 + |x|) + E₀ + E)).add
      (hSi.const_mul E) |>.congr (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring))
  have hgood : ∀ᵐ ω ∂P, (fun t => W t ω) = (fun t => B t ω) ∧
      (∀ t, |ctrlX M φ₁ φ₂ x (fun t => B t ω) t| ≤ S ω) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => exp (-M.ρ * s) *
        runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal)) (Set.Ioi 0) ∧
      Summable (fun k : ℕ => disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1)) *
        |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|) ∧
      Summable (fun k : ℕ => disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1)) *
        |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i.other (k + 1))|) ∧
      Tendsto (fun k : ℕ => tauP M φ₁ φ₂ x (fun t => W t ω) .one k) atTop (𝓝 ⊤) ∧
      Tendsto (fun k : ℕ => tauP M φ₁ φ₂ x (fun t => W t ω) .two k) atTop (𝓝 ⊤) := by
    filter_upwards [hpath, hSb, hΦ.run_integrableOn i, hΦ.cost_summable i,
      hΦ.gain_summable i.other, hΦ.tau_tendsto .one, hΦ.tau_tendsto .two]
      with ω h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hpb : ∀ᵐ ω ∂P, (∀ n : ℕ, ‖Up M φ₁ φ₂ x (fun s => B s ω) i u V n‖ ≤ H ω) ∧
      Tendsto (fun n => Up M φ₁ φ₂ x (fun s => B s ω) i u V n) atTop
        (𝓝 (payoffPath M φ₁ φ₂ x (fun t => W t ω) i)) := by
    filter_upwards [hgood] with ω ⟨hp, hS, hr, hcs, hgs, ht1, ht2⟩
    rw [hp] at hr hcs hgs ht1 ht2
    have htau : ∀ j, Tendsto (fun k => tauP M φ₁ φ₂ x (fun t => B t ω) j k) atTop (𝓝 ⊤) := by
      intro j; cases j
      · exact ht1
      · exact ht2
    have h := path_eq (hBc ω) hρ hc hl hct hlt i hE hE₀ hVu hJ1 hJ2 hVlin hp1 hp2 hS hr hcs hgs
      htau
    have hA : A ω = ∫ s in Set.Ioi (0 : ℝ),
        |exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x (fun t => B t ω) s.toNNReal)| := by
      simp only [hAdef, hp]
      congr 1
      funext s
      rw [abs_mul, abs_of_pos (exp_pos _)]
    refine ⟨fun n => ?_, ?_⟩
    · rw [Real.norm_eq_abs]
      have := h.1 n
      simp only [hHdef, hCsdef, hGsdef]
      rw [hA, hp]
      exact this
    · rw [hp]
      exact h.2
  have hT := MeasureTheory.tendsto_integral_of_dominated_convergence H
    (fun n => (hUi n).aestronglyMeasurable) hHi (fun n => hpb.mono fun ω h => h.1 n)
    (hpb.mono fun ω h => h.2)
  simp only [hUb] at hT
  exact (tendsto_nhds_unique hT tendsto_const_nhds)


-- ===== from scratch/probe/2b17c77f_ext.lean =====


/-! ## Part E1: the C¹ tangent-line extension of a smooth function off `[a, b]` -/

/-- Clamp to `[a, b]`. -/
noncomputable def cl (a b y : ℝ) : ℝ := max a (min y b)

/-- `φ` on `[a, b]`, continued by its tangent lines outside. -/
noncomputable def tExt (φ φ' : ℝ → ℝ) (a b : ℝ) (y : ℝ) : ℝ :=
  φ (cl a b y) + φ' (cl a b y) * (y - cl a b y)

noncomputable def tExt1 (φ' : ℝ → ℝ) (a b : ℝ) (y : ℝ) : ℝ := φ' (cl a b y)

noncomputable def tExt2 (φ'' : ℝ → ℝ) (a b : ℝ) (y : ℝ) : ℝ :=
  if y ≤ a then 0 else if y < b then φ'' y else 0

lemma continuous_cl (a b : ℝ) : Continuous (cl a b) := by
  unfold cl; fun_prop

lemma cl_of_le {a b y : ℝ} (hab : a ≤ b) (h : y ≤ a) : cl a b y = a := by
  unfold cl; rw [max_eq_left]; exact le_trans (min_le_left _ _) h

lemma cl_of_ge {a b y : ℝ} (hab : a ≤ b) (h : b ≤ y) : cl a b y = b := by
  unfold cl; rw [min_eq_right h, max_eq_right hab]

lemma cl_of_mem {a b y : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) : cl a b y = y := by
  unfold cl; rw [min_eq_left h2, max_eq_right h1]

lemma tExt_of_mem {φ φ' : ℝ → ℝ} {a b y : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) :
    tExt φ φ' a b y = φ y := by
  unfold tExt; rw [cl_of_mem h1 h2]; ring

lemma tExt_of_le {φ φ' : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (h : y ≤ a) :
    tExt φ φ' a b y = φ a + φ' a * (y - a) := by
  unfold tExt; rw [cl_of_le hab h]

lemma tExt_of_ge {φ φ' : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (h : b ≤ y) :
    tExt φ φ' a b y = φ b + φ' b * (y - b) := by
  unfold tExt; rw [cl_of_ge hab h]

lemma hasDerivAt_glue {f : ℝ → ℝ} {c d : ℝ} (hl : HasDerivWithinAt f d (Set.Iic c) c)
    (hr : HasDerivWithinAt f d (Set.Ici c) c) : HasDerivAt f d c := by
  have := hl.union hr
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

theorem tExt_reg {φ φ' φ'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hφ : ∀ y, HasDerivAt φ (φ' y) y) (hφ' : ∀ y, HasDerivAt φ' (φ'' y) y)
    (hc'' : Continuous φ'') :
    ∃ D : ℝ, Reg (tExt φ φ' a b) (tExt1 φ' a b) (tExt2 φ'' a b) {a, b} D 1 ∧
      (∀ y, |tExt φ φ' a b y| ≤ D * (1 + |y|)) ∧ (∀ y, |tExt2 φ'' a b y| ≤ D * (1 + |y|)) := by
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun y => (hφ y).continuousAt
  have hc' : Continuous φ' := continuous_iff_continuousAt.2 fun y => (hφ' y).continuousAt
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc'.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc''.continuousOn
  have hcl : ∀ y, cl a b y ∈ Set.Icc a b := fun y =>
    ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hC0' : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 a ⟨le_rfl, hab.le⟩)
  have hC1' : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 a ⟨le_rfl, hab.le⟩)
  have hC2' : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 a ⟨le_rfl, hab.le⟩)
  set D := C0 + C1 * (1 + |a| + |b|) + C2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hclb : ∀ y, |cl a b y| ≤ |a| + |b| := by
    intro y
    obtain ⟨h1, h2⟩ := hcl y
    rw [abs_le]
    constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
  have b0 : ∀ y, |tExt φ φ' a b y| ≤ D * (1 + |y|) := by
    intro y
    unfold tExt
    have e0 : |φ (cl a b y)| ≤ C0 := by have := hC0 _ (hcl y); rwa [Real.norm_eq_abs] at this
    have e1 : |φ' (cl a b y)| ≤ C1 := by have := hC1 _ (hcl y); rwa [Real.norm_eq_abs] at this
    have e2 : |y - cl a b y| ≤ |y| + (|a| + |b|) :=
      (abs_sub _ _).trans (by linarith [hclb y])
    calc |φ (cl a b y) + φ' (cl a b y) * (y - cl a b y)|
        ≤ |φ (cl a b y)| + |φ' (cl a b y)| * |y - cl a b y| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ C0 + C1 * (|y| + (|a| + |b|)) := by gcongr
      _ ≤ D * (1 + |y|) := by
          rw [hD]
          have h1 := mul_nonneg hC0' (abs_nonneg y)
          have h2 := mul_nonneg hC1' (mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b))
            (abs_nonneg y))
          have h3 := mul_nonneg hC2' (add_nonneg zero_le_one (abs_nonneg y))
          nlinarith [abs_nonneg a, abs_nonneg b]
  have b1 : ∀ y, |tExt1 φ' a b y| ≤ D * (1 + |y|) := by
    intro y
    have e1 : |φ' (cl a b y)| ≤ C1 := by have := hC1 _ (hcl y); rwa [Real.norm_eq_abs] at this
    unfold tExt1
    rw [hD]
    nlinarith [abs_nonneg y, abs_nonneg a, abs_nonneg b]
  have b2 : ∀ y, |tExt2 φ'' a b y| ≤ D * (1 + |y|) := by
    intro y
    unfold tExt2
    split_ifs with h1 h2
    · simp only [abs_zero]; positivity
    · have e2 : |φ'' y| ≤ C2 := by
        have := hC2 y ⟨(not_le.1 h1).le, h2.le⟩; rwa [Real.norm_eq_abs] at this
      rw [hD]
      nlinarith [abs_nonneg y, abs_nonneg a, abs_nonneg b]
    · simp only [abs_zero]; positivity
  have hexp : ∀ y, D * (1 + |y|) ≤ D * Real.exp (1 * |y|) := fun y => by
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (|y|)]) hD0
  refine ⟨D, ⟨?_, ?_, ?_, ?_, ?_, zero_le_one, fun y => (b0 y).trans (hexp y),
    fun y => (b1 y).trans (hexp y), fun y => (b2 y).trans (hexp y)⟩, b0, b2⟩
  · -- `HasDerivAt (tExt) (tExt1)`
    intro y
    have hlinA : ∀ z, HasDerivAt (fun z => φ a + φ' a * (z - a)) (φ' a) z := fun z => by
      simpa using ((hasDerivAt_id z).sub_const a).const_mul (φ' a) |>.const_add (φ a)
    have hlinB : ∀ z, HasDerivAt (fun z => φ b + φ' b * (z - b)) (φ' b) z := fun z => by
      simpa using ((hasDerivAt_id z).sub_const b).const_mul (φ' b) |>.const_add (φ b)
    unfold tExt1
    rcases lt_trichotomy y a with hya | hya | hya
    · rw [cl_of_le hab.le hya.le]
      refine (hlinA y).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hya] with z hz
      exact tExt_of_le hab.le (le_of_lt hz)
    · rw [hya, cl_of_le hab.le le_rfl]
      refine hasDerivAt_glue ?_ ?_
      · refine (hlinA a).hasDerivWithinAt.congr (fun z hz => tExt_of_le hab.le hz) ?_
        exact tExt_of_le hab.le le_rfl
      · refine ((hφ a).hasDerivWithinAt).congr_of_eventuallyEq ?_ (tExt_of_mem le_rfl hab.le)
        filter_upwards [inter_mem_nhdsWithin (Set.Ici a) (Iio_mem_nhds hab)] with z hz
        exact tExt_of_mem hz.1 (le_of_lt hz.2)
    · rcases lt_trichotomy y b with hyb | hyb | hyb
      · rw [cl_of_mem hya.le hyb.le]
        refine (hφ y).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hya hyb] with z hz
        exact tExt_of_mem hz.1.le hz.2.le
      · rw [hyb, cl_of_ge hab.le le_rfl]
        refine hasDerivAt_glue ?_ ?_
        · refine ((hφ b).hasDerivWithinAt).congr_of_eventuallyEq ?_ (tExt_of_mem hab.le le_rfl)
          filter_upwards [inter_mem_nhdsWithin (Set.Iic b) (Ioi_mem_nhds hab)] with z hz
          exact tExt_of_mem (le_of_lt hz.2) hz.1
        · refine (hlinB b).hasDerivWithinAt.congr (fun z hz => tExt_of_ge hab.le hz) ?_
          exact tExt_of_ge hab.le le_rfl
      · rw [cl_of_ge hab.le hyb.le]
        refine (hlinB y).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hyb] with z hz
        exact tExt_of_ge hab.le (le_of_lt hz)
  · exact hc'.comp (continuous_cl a b)
  · exact (Set.toFinite _).countable
  · intro y hy
    have hya : y ≠ a := fun h => hy (by simp [h])
    have hyb : y ≠ b := fun h => hy (by simp [h])
    unfold tExt1 tExt2
    rcases lt_or_gt_of_ne hya with h1 | h1
    · rw [if_pos h1.le]
      refine (hasDerivAt_const y (φ' a)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h1] with z hz
      rw [cl_of_le hab.le (le_of_lt hz)]
    · rw [if_neg (not_le.2 h1)]
      rcases lt_or_gt_of_ne hyb with h2 | h2
      · rw [if_pos h2]
        refine (hφ' y).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds h1 h2] with z hz
        rw [cl_of_mem hz.1.le hz.2.le]
      · rw [if_neg (not_lt.2 h2.le)]
        refine (hasDerivAt_const y (φ' b)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds h2] with z hz
        rw [cl_of_ge hab.le (le_of_lt hz)]
  · unfold tExt2
    exact Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Iio hc''.measurable measurable_const)


-- ===== from scratch/probe/2b17c77f_v1.lean =====


open ImpulseGames.LinearGame

/-! ## Part E2: the candidate `Ṽ₁` -- derivatives, ODE, convexity sign, extension facts -/

section V1
variable (M : Model) (ξ s : ℝ)

noncomputable def d1One (y : ℝ) : ℝ :=
  theta M * A M ξ s 1 1 * exp (theta M * y) - theta M * A M ξ s 1 2 * exp (-(theta M * y)) + 1 / M.ρ

noncomputable def d2One (y : ℝ) : ℝ :=
  theta M ^ 2 * (A M ξ s 1 1 * exp (theta M * y) + A M ξ s 1 2 * exp (-(theta M * y)))

lemma hasDerivAt_e1 (y : ℝ) :
    HasDerivAt (fun y => exp (theta M * y)) (exp (theta M * y) * theta M) y := by
  simpa using ((hasDerivAt_id' y).const_mul (theta M)).exp

lemma hasDerivAt_e2 (y : ℝ) :
    HasDerivAt (fun y => exp (-(theta M * y))) (exp (-(theta M * y)) * -theta M) y := by
  simpa using (((hasDerivAt_id' y).const_mul (theta M)).neg).exp

lemma hasDerivAt_phiOne (y : ℝ) : HasDerivAt (phiOne M ξ s) (d1One M ξ s y) y := by
  unfold phiOne phi1 d1One
  have h3 : HasDerivAt (fun y => (y - M.s₁) / M.ρ) (1 / M.ρ) y := by
    simpa using ((hasDerivAt_id' y).sub_const M.s₁).div_const M.ρ
  exact ((((hasDerivAt_e1 M y).const_mul (A M ξ s 1 1)).add
    ((hasDerivAt_e2 M y).const_mul (A M ξ s 1 2))).add h3).congr_deriv (by ring)

lemma hasDerivAt_d1One (y : ℝ) : HasDerivAt (d1One M ξ s) (d2One M ξ s y) y := by
  unfold d1One d2One
  exact ((((hasDerivAt_e1 M y).const_mul (theta M * A M ξ s 1 1)).sub
    ((hasDerivAt_e2 M y).const_mul (theta M * A M ξ s 1 2))).add_const (1 / M.ρ)).congr_deriv
    (by ring)

lemma continuous_d2One : Continuous (d2One M ξ s) := by
  unfold d2One; fun_prop

lemma deriv_phiOne (y : ℝ) : deriv (phiOne M ξ s) y = d1One M ξ s y :=
  (hasDerivAt_phiOne M ξ s y).deriv

lemma theta_sq (hσ : M.σ ≠ 0) (hρ : 0 < M.ρ) : M.σ ^ 2 / 2 * theta M ^ 2 = M.ρ := by
  unfold theta
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- `φ₁` solves `σ²/2 φ'' - ρφ + (y - s₁) = 0`. -/
lemma ode_one (hσ : M.σ ≠ 0) (hρ : 0 < M.ρ) (y : ℝ) :
    M.σ ^ 2 / 2 * d2One M ξ s y - M.ρ * phiOne M ξ s y + (y - M.s₁) = 0 := by
  have h := theta_sq M hσ hρ
  unfold d2One phiOne phi1
  have : M.σ ^ 2 / 2 * (theta M ^ 2 * (A M ξ s 1 1 * exp (theta M * y) +
      A M ξ s 1 2 * exp (-(theta M * y)))) =
      M.ρ * (A M ξ s 1 1 * exp (theta M * y) + A M ξ s 1 2 * exp (-(theta M * y))) := by
    rw [← h]; ring
  rw [this]
  field_simp
  ring

lemma A11_nonpos : A M ξ s 1 1 ≤ 0 := by
  unfold A
  have h0 : 0 ≤ Real.exp ((-1 : ℝ) ^ 1 * theta M * s) * Real.sqrt (eta M ^ 2 - ξ ^ 2) /
      (2 * theta M) := by
    have : 0 ≤ theta M := Real.sqrt_nonneg _
    positivity
  have h1 : (-1 : ℝ) ^ (1 + 1 + 1) * Real.sqrt (Gam M ξ + 1) - Real.sqrt (Gam M ξ) ≤ 0 := by
    norm_num
    have := Real.sqrt_nonneg (Gam M ξ + 1)
    have := Real.sqrt_nonneg (Gam M ξ)
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos h0 h1

lemma A12_nonneg : 0 ≤ A M ξ s 1 2 := by
  unfold A
  have h0 : 0 ≤ Real.exp ((-1 : ℝ) ^ 2 * theta M * s) * Real.sqrt (eta M ^ 2 - ξ ^ 2) /
      (2 * theta M) := by
    have : 0 ≤ theta M := Real.sqrt_nonneg _
    positivity
  have h1 : 0 ≤ (-1 : ℝ) ^ (1 + 2 + 1) * Real.sqrt (Gam M ξ + 1) - Real.sqrt (Gam M ξ) := by
    norm_num
    exact Real.sqrt_le_sqrt (by linarith)
  exact mul_nonneg h0 h1

lemma d2One_antitone : Antitone (d2One M ξ s) := by
  intro y z hyz
  unfold d2One
  have hθ : 0 ≤ theta M := Real.sqrt_nonneg _
  have h11 := A11_nonpos M ξ s
  have h12 := A12_nonneg M ξ s
  have e1 : exp (theta M * y) ≤ exp (theta M * z) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hyz hθ)
  have e2 : exp (-(theta M * z)) ≤ exp (-(theta M * y)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hyz hθ))
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonpos_left e1 h11, mul_le_mul_of_nonneg_left e2 h12]

/-- `φ₁''(x̄₁) ≥ 0`, from `φ₁'(x̄₁) = φ₁'(x₁*) = λ` (Rolle) and the antitonicity of `φ₁''`. -/
lemma d2One_nonneg_left {a p : ℝ} (hap : a < p) (ha : d1One M ξ s a = M.lam)
    (hp : d1One M ξ s p = M.lam) : 0 ≤ d2One M ξ s a := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hap
    (fun y _ => (hasDerivAt_d1One M ξ s y).continuousAt.continuousWithinAt) (ha.trans hp.symm)
    (fun y _ => hasDerivAt_d1One M ξ s y)
  rw [← hc0]
  exact d2One_antitone M ξ s hc.1.le

end V1



-- ===== from v1b =====


open ImpulseGames.LinearGame

/-! ## Part E3: `Ṽ₁` instance facts (from the pasting conditions (4.7), (4.8a-d)) -/

section V1b
variable (M : Model) (ξ s : ℝ)

lemma Vt1_left {y : ℝ} (hy : y ≤ xbar M ξ s 1) :
    Vt1 M ξ s y = phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - y) := by
  unfold Vt1; rw [if_pos hy]

lemma Vt1_mid {y : ℝ} (h1 : xbar M ξ s 1 < y) (h2 : y < xbar M ξ s 2) :
    Vt1 M ξ s y = phiOne M ξ s y := by
  unfold Vt1; rw [if_neg (not_le.2 h1), if_pos h2]

lemma Vt1_right {y : ℝ} (h1 : xbar M ξ s 1 < y) (h2 : xbar M ξ s 2 ≤ y) :
    Vt1 M ξ s y = phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (y - xstar M ξ s 2) := by
  unfold Vt1; rw [if_neg (not_le.2 h1), if_neg (not_lt.2 h2)]

/-- `u := tExt φ₁ φ₁' x̄₁ x̄₂` agrees with `Ṽ₁` on `]−∞, x̄₂]`. -/
lemma tExt_eq_Vt1 (hab : xbar M ξ s 1 < xbar M ξ s 2)
    (h8b : d1One M ξ s (xbar M ξ s 1) = M.lam)
    (h8c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h8d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2))
    {y : ℝ} (hy : y ≤ xbar M ξ s 2) :
    tExt (phiOne M ξ s) (d1One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y = Vt1 M ξ s y := by
  rcases le_or_gt y (xbar M ξ s 1) with h1 | h1
  · rw [tExt_of_le hab.le h1, Vt1_left M ξ s h1, h8b, h8c]; ring
  · rw [tExt_of_mem h1.le hy]
    rcases lt_or_eq_of_le hy with h2 | h2
    · rw [Vt1_mid M ξ s h1 h2]
    · rw [Vt1_right M ξ s h1 h2.ge, h2, h8d]

/-- The generator inequality for `u` on `]−∞, x̄₂[` (equality on `]x̄₁, x̄₂[`). -/
lemma gen_one_le (hσ : M.σ ≠ 0) (hρ : 0 < M.ρ) (hlr : 0 < 1 - M.lam * M.ρ)
    (hab : xbar M ξ s 1 < xbar M ξ s 2) (hap : xbar M ξ s 1 < xstar M ξ s 1)
    (h8a : d1One M ξ s (xstar M ξ s 1) = M.lam) (h8b : d1One M ξ s (xbar M ξ s 1) = M.lam)
    {y : ℝ} (hy : y < xbar M ξ s 2) :
    M.σ ^ 2 / 2 * tExt2 (d2One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y
      - M.ρ * tExt (phiOne M ξ s) (d1One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y
      + (y - M.s₁) ≤ 0 := by
  rcases le_or_gt y (xbar M ξ s 1) with h1 | h1
  · have e2 : tExt2 (d2One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y = 0 := by
      unfold tExt2; rw [if_pos h1]
    rw [e2, tExt_of_le hab.le h1, h8b]
    have hode := ode_one M ξ s hσ hρ (xbar M ξ s 1)
    have hd2 := d2One_nonneg_left M ξ s hap h8b h8a
    have e : M.σ ^ 2 / 2 * 0 - M.ρ * (phiOne M ξ s (xbar M ξ s 1) + M.lam * (y - xbar M ξ s 1))
        + (y - M.s₁) = -(M.σ ^ 2 / 2 * d2One M ξ s (xbar M ξ s 1))
          + (1 - M.lam * M.ρ) * (y - xbar M ξ s 1) := by
      linear_combination hode
    rw [e]
    have : 0 ≤ M.σ ^ 2 / 2 * d2One M ξ s (xbar M ξ s 1) := mul_nonneg (by positivity) hd2
    have : (1 - M.lam * M.ρ) * (y - xbar M ξ s 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlr.le (by linarith)
    linarith
  · have e2 : tExt2 (d2One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y = d2One M ξ s y := by
      unfold tExt2; rw [if_neg (not_le.2 h1), if_pos hy]
    rw [e2, tExt_of_mem h1.le hy.le]
    exact (ode_one M ξ s hσ hρ y).le

lemma gen_one_eq (hσ : M.σ ≠ 0) (hρ : 0 < M.ρ) {y : ℝ} (h1 : xbar M ξ s 1 < y)
    (hy : y < xbar M ξ s 2) :
    M.σ ^ 2 / 2 * tExt2 (d2One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y
      - M.ρ * tExt (phiOne M ξ s) (d1One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y
      + (y - M.s₁) = 0 := by
  have e2 : tExt2 (d2One M ξ s) (xbar M ξ s 1) (xbar M ξ s 2) y = d2One M ξ s y := by
    unfold tExt2; rw [if_neg (not_le.2 h1), if_pos hy]
  rw [e2, tExt_of_mem h1.le hy.le]
  exact ode_one M ξ s hσ hρ y

/-- Player 2's jump `y ↦ x₂*` (for `y ≥ x̄₂`) leaves `Ṽ₁ + ψ` unchanged. -/
lemma jump2_Vt1 (hq1 : xbar M ξ s 1 < xstar M ξ s 2) (hq2 : xstar M ξ s 2 < xbar M ξ s 2)
    {y : ℝ} (hy : xbar M ξ s 2 ≤ y) :
    Vt1 M ξ s (y + delta2 M ξ s y) + (M.ct + M.lamt * |delta2 M ξ s y|) = Vt1 M ξ s y := by
  have hd : delta2 M ξ s y = xstar M ξ s 2 - y := by
    unfold delta2; exact min_eq_left (by linarith)
  rw [hd, show y + (xstar M ξ s 2 - y) = xstar M ξ s 2 by ring, Vt1_mid M ξ s hq1 hq2,
    Vt1_right M ξ s (by linarith) hy, abs_of_nonpos (by linarith)]
  ring

/-- Player 1's own jump `y ↦ x₁*` (for `y ≤ x̄₁`) leaves `Ṽ₁ + φ` unchanged. -/
lemma jump1_Vt1 (hp1 : xbar M ξ s 1 < xstar M ξ s 1) (hp2 : xstar M ξ s 1 < xbar M ξ s 2)
    {y : ℝ} (hy : y ≤ xbar M ξ s 1) :
    Vt1 M ξ s (y + delta1 M ξ s y) + (-M.c - M.lam * |delta1 M ξ s y|) = Vt1 M ξ s y := by
  have hd : delta1 M ξ s y = xstar M ξ s 1 - y := by
    unfold delta1; exact max_eq_left (by linarith)
  rw [hd, show y + (xstar M ξ s 1 - y) = xstar M ξ s 1 by ring, Vt1_mid M ξ s hp1 hp2,
    Vt1_left M ξ s hy, abs_of_nonneg (by linarith)]
  ring

/-- A continuous lower barrier for `Ṽ₁`, nondecreasing, constant on `[x̄₁, ∞[`. -/
lemma Vt1_lower (hab : xbar M ξ s 1 < xbar M ξ s 2)
    (hp1 : xbar M ξ s 1 < xstar M ξ s 1) (hp2 : xstar M ξ s 1 < xbar M ξ s 2)
    (hq1 : xbar M ξ s 1 < xstar M ξ s 2) (hq2 : xstar M ξ s 2 < xbar M ξ s 2)
    (hl : 0 ≤ M.lam) (hct : 0 ≤ M.ct) (hlt : 0 ≤ M.lamt)
    (h8b : d1One M ξ s (xbar M ξ s 1) = M.lam)
    (h8c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h8d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ y, -C0 + M.lam * min 0 (y - xbar M ξ s 1) ≤ Vt1 M ξ s y := by
  have hc : Continuous (phiOne M ξ s) :=
    continuous_iff_continuousAt.2 fun y => (hasDerivAt_phiOne M ξ s y).continuousAt
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := xbar M ξ s 1) (b := xbar M ξ s 2)).exists_bound_of_continuousOn
    hc.continuousOn
  have hb : ∀ y ∈ Set.Icc (xbar M ξ s 1) (xbar M ξ s 2), -C0 ≤ phiOne M ξ s y := by
    intro y hy
    have := hC0 y hy
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (phiOne M ξ s y)]
  have hC0' : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 _ ⟨le_rfl, hab.le⟩)
  refine ⟨C0, hC0', fun y => ?_⟩
  rcases le_or_gt y (xbar M ξ s 1) with h1 | h1
  · rw [← tExt_eq_Vt1 M ξ s hab h8b h8c h8d (h1.trans hab.le), tExt_of_le hab.le h1, h8b,
      min_eq_right (by linarith)]
    have := hb _ ⟨le_rfl, hab.le⟩
    linarith
  · rw [min_eq_left (by linarith)]
    rcases lt_or_ge y (xbar M ξ s 2) with h2 | h2
    · rw [Vt1_mid M ξ s h1 h2]
      have := hb y ⟨h1.le, h2.le⟩
      linarith
    · rw [Vt1_right M ξ s h1 h2]
      have := hb _ ⟨hq1.le, hq2.le⟩
      have : 0 ≤ M.lamt * (y - xstar M ξ s 2) := mul_nonneg hlt (by linarith)
      linarith

/-- `Ṽ₁` has linear growth. -/
lemma Vt1_lin (hab : xbar M ξ s 1 < xbar M ξ s 2) (hl : 0 ≤ M.lam) (hlt : 0 ≤ M.lamt) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ y, |Vt1 M ξ s y| ≤ E * (1 + |y|) := by
  have hc : Continuous (phiOne M ξ s) :=
    continuous_iff_continuousAt.2 fun y => (hasDerivAt_phiOne M ξ s y).continuousAt
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := xbar M ξ s 1) (b := xbar M ξ s 2)).exists_bound_of_continuousOn
    hc.continuousOn
  have hC0' : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 _ ⟨le_rfl, hab.le⟩)
  set p := xstar M ξ s 1
  set q := xstar M ξ s 2
  set E := C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct|
    + M.lam * (1 + |p|) + M.lamt * (1 + |q|) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨E, hE0, fun y => ?_⟩
  have hy0 := abs_nonneg y
  have hEy : E ≤ E * (1 + |y|) := by nlinarith
  have hlp : |M.lam * (p - y)| ≤ M.lam * (1 + |p|) * (1 + |y|) := by
    rw [abs_mul, abs_of_nonneg hl]
    have : |p - y| ≤ (1 + |p|) * (1 + |y|) := by
      have := abs_sub p y; nlinarith [abs_nonneg p]
    calc M.lam * |p - y| ≤ M.lam * ((1 + |p|) * (1 + |y|)) := mul_le_mul_of_nonneg_left this hl
      _ = _ := by ring
  have hlq : |M.lamt * (y - q)| ≤ M.lamt * (1 + |q|) * (1 + |y|) := by
    rw [abs_mul, abs_of_nonneg hlt]
    have : |y - q| ≤ (1 + |q|) * (1 + |y|) := by
      have := abs_sub y q; nlinarith [abs_nonneg q]
    calc M.lamt * |y - q| ≤ M.lamt * ((1 + |q|) * (1 + |y|)) := mul_le_mul_of_nonneg_left this hlt
      _ = _ := by ring
  have hA : 0 ≤ (|phiOne M ξ s p| + |M.c| + C0 + |phiOne M ξ s q| + |M.ct| + M.lamt * (1 + |q|))
      * (1 + |y|) := by positivity
  have hB : 0 ≤ (C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct| + M.lam * (1 + |p|))
      * (1 + |y|) := by positivity
  rcases le_or_gt y (xbar M ξ s 1) with h1 | h1
  · rw [Vt1_left M ξ s h1]
    have := abs_sub (phiOne M ξ s p - M.c) (M.lam * (p - y))
    have := abs_sub (phiOne M ξ s p) M.c
    have e : E * (1 + |y|) = (C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct|
      + M.lamt * (1 + |q|)) * (1 + |y|) + M.lam * (1 + |p|) * (1 + |y|) := by rw [hE]; ring
    have : |phiOne M ξ s p| + |M.c| ≤ (C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct|
      + M.lamt * (1 + |q|)) * (1 + |y|) := by
      have h0 : 0 ≤ M.lamt * (1 + |q|) := by positivity
      nlinarith [abs_nonneg (phiOne M ξ s q), abs_nonneg M.ct]
    linarith
  · rcases lt_or_ge y (xbar M ξ s 2) with h2 | h2
    · rw [Vt1_mid M ξ s h1 h2]
      have := hC0 y ⟨h1.le, h2.le⟩
      rw [Real.norm_eq_abs] at this
      have : C0 ≤ E := by
        rw [hE]
        have := abs_nonneg (phiOne M ξ s p)
        have := abs_nonneg (phiOne M ξ s q)
        have := abs_nonneg M.c
        have := abs_nonneg M.ct
        have : 0 ≤ M.lam * (1 + |p|) := by positivity
        have : 0 ≤ M.lamt * (1 + |q|) := by positivity
        linarith
      linarith
    · rw [Vt1_right M ξ s h1 h2]
      have := abs_add_le (phiOne M ξ s q + M.ct) (M.lamt * (y - q))
      have := abs_add_le (phiOne M ξ s q) M.ct
      have e : E * (1 + |y|) = (C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct|
      + M.lam * (1 + |p|)) * (1 + |y|) + M.lamt * (1 + |q|) * (1 + |y|) := by rw [hE]; ring
      have : |phiOne M ξ s q| + |M.ct| ≤ (C0 + |phiOne M ξ s p| + |phiOne M ξ s q| + |M.c| + |M.ct|
        + M.lam * (1 + |p|)) * (1 + |y|) := by
        have h0 : 0 ≤ M.lam * (1 + |p|) := by positivity
        nlinarith [abs_nonneg (phiOne M ξ s p), abs_nonneg M.c]
      linarith

end V1b


-- ===== from pc =====


open ImpulseGames.LinearGame

/-! ## Part F0: shared helpers for the player verification parts -/

lemma closure_inter_Iio_sub {A : Set ℝ} {b y : ℝ} (hy : y ∈ closure (A ∩ Set.Iio b)) : y ≤ b := by
  have : y ∈ closure (Set.Iio b) := closure_mono Set.inter_subset_right hy
  rw [closure_Iio] at this
  exact this

lemma payI_self (M : Model) (i : Player) (δ : ℝ) : payI M i i δ = -M.c - M.lam * |δ| := by
  simp [payI, cost]

lemma payI_one_two (M : Model) (δ : ℝ) : payI M .one .two δ = M.ct + M.lamt * |δ| := by
  simp [payI, gain]

open ImpulseGames.LinearGame

/-! ## Part F1: player 1 -- no profitable deviation, and the equilibrium payoff -/

theorem player_one_dev (M : Model) (hM : M.Standing) (ξ s : ℝ)
    (ho1 : xbar M ξ s 1 < xstar M ξ s 1) (ho2 : xstar M ξ s 1 < xbar M ξ s 2)
    (ho3 : xbar M ξ s 1 < xstar M ξ s 2) (ho4 : xstar M ξ s 2 < xbar M ξ s 2)
    (h8a : d1One M ξ s (xstar M ξ s 1) = M.lam) (h8b : d1One M ξ s (xbar M ξ s 1) = M.lam)
    (h8c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h8d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2))
    (hqvi : ∀ y δ : ℝ, 0 ≤ δ → Vt1 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt1 M ξ s y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (x : ℝ) (ψ₁ : Strategy Z₁)
    (hΦ : InPhi M P W x ψ₁ (eqStrat2 M ξ s)) :
    J M P W x ψ₁ (eqStrat2 M ξ s) .one ≤ Vt1 M ξ s x := by
  have hσ : M.σ ≠ 0 := hM.σ_pos.ne'
  have hρ := hM.ρ_pos
  have hct := hM.ct_nonneg
  have hc : 0 ≤ M.c := hct.trans hM.ct_le_c
  have hlt := hM.lamt_nonneg
  have hl : 0 ≤ M.lam := hlt.trans hM.lamt_le_lam
  have hlr := hM.one_sub_lam_mul_ρ_pos
  have hab : xbar M ξ s 1 < xbar M ξ s 2 := ho1.trans ho2
  obtain ⟨D, hR, hl0, hl2⟩ := tExt_reg hab (hasDerivAt_phiOne M ξ s) (hasDerivAt_d1One M ξ s)
    (continuous_d2One M ξ s)
  obtain ⟨C0, hC0, hlow⟩ := Vt1_lower M ξ s hab ho1 ho2 ho3 ho4 hl hct hlt h8b h8c h8d
  set a := xbar M ξ s 1 with ha
  have hE : 0 ≤ C0 + M.lam * (1 + |a|) := by positivity
  refine deviation_le M hσ hρ hc hl hct hlt hR hl0 hl2 hE P W hW ψ₁ (eqStrat2 M ξ s) x .one
    (Vt1 M ξ s) (fun y => -C0 + M.lam * min 0 (y - a)) ?_ ?_ ?_ ?_ hlow ?_ ?_ ?_ hΦ
  · intro y hy
    exact tExt_eq_Vt1 M ξ s hab h8b h8c h8d (closure_inter_Iio_sub hy)
  · intro y hy
    exact gen_one_le M ξ s hσ hρ hlr hab ho1 h8a h8b hy.2
  · intro y _
    rw [payI_self]
    have h0 : 0 ≤ ψ₁.ξ y := by
      have := ψ₁.mem_Z y
      simpa [Z₁] using this
    have := hqvi y (ψ₁.ξ y) h0
    linarith
  · intro y hy
    have hy' : xbar M ξ s 2 ≤ y := not_lt.1 hy
    rw [payI_one_two]
    exact (jump2_Vt1 M ξ s ho3 ho4 hy').le
  · intro y
    have h1 : -(|y| + |a|) ≤ min 0 (y - a) :=
      le_min (by linarith [abs_nonneg y, abs_nonneg a]) (by linarith [neg_abs_le y, le_abs_self a])
    have h2 : M.lam * (-(|y| + |a|)) ≤ M.lam * min 0 (y - a) := mul_le_mul_of_nonneg_left h1 hl
    nlinarith [mul_nonneg hC0 (abs_nonneg y), mul_nonneg hl (mul_nonneg (abs_nonneg a) (abs_nonneg y)),
      mul_nonneg hl (abs_nonneg y)]
  · intro y _
    have h0 : 0 ≤ ψ₁.ξ y := by
      have := ψ₁.mem_Z y
      simpa [Z₁] using this
    have : min 0 (y - a) ≤ min 0 (y + ψ₁.ξ y - a) := min_le_min_left _ (by linarith)
    have := mul_le_mul_of_nonneg_left this hl
    show -C0 + M.lam * min 0 (y - a) ≤ -C0 + M.lam * min 0 (y + ψ₁.ξ y - a)
    linarith
  · intro y hy
    have hy' : xbar M ξ s 2 ≤ y := not_lt.1 hy
    have hd : (eqStrat2 M ξ s).ξ y = xstar M ξ s 2 - y := by
      show delta2 M ξ s y = _
      unfold delta2; exact min_eq_left (by linarith)
    show -C0 + M.lam * min 0 (y - a) ≤ -C0 + M.lam * min 0 (y + (eqStrat2 M ξ s).ξ y - a)
    rw [hd, min_eq_left (by linarith), min_eq_left (by linarith)]

theorem player_one_eq (M : Model) (hM : M.Standing) (ξ s : ℝ)
    (ho1 : xbar M ξ s 1 < xstar M ξ s 1) (ho2 : xstar M ξ s 1 < xbar M ξ s 2)
    (ho3 : xbar M ξ s 1 < xstar M ξ s 2) (ho4 : xstar M ξ s 2 < xbar M ξ s 2)
    (h8b : d1One M ξ s (xbar M ξ s 1) = M.lam)
    (h8c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h8d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (x : ℝ)
    (hΦ : InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s)) :
    J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .one = Vt1 M ξ s x := by
  have hσ : M.σ ≠ 0 := hM.σ_pos.ne'
  have hρ := hM.ρ_pos
  have hct := hM.ct_nonneg
  have hc : 0 ≤ M.c := hct.trans hM.ct_le_c
  have hlt := hM.lamt_nonneg
  have hl : 0 ≤ M.lam := hlt.trans hM.lamt_le_lam
  have hab : xbar M ξ s 1 < xbar M ξ s 2 := ho1.trans ho2
  obtain ⟨D, hR, hl0, hl2⟩ := tExt_reg hab (hasDerivAt_phiOne M ξ s) (hasDerivAt_d1One M ξ s)
    (continuous_d2One M ξ s)
  obtain ⟨E, hE, hlin⟩ := Vt1_lin M ξ s hab hl hlt
  have hE₀ : 0 ≤ |phiOne M ξ s (xstar M ξ s 1)| + |phiOne M ξ s (xstar M ξ s 2)| := by positivity
  refine payoff_eq M hσ hρ hc hl hct hlt hR hl0 hl2 hE hE₀ P W hW (eqStrat1 M ξ s)
    (eqStrat2 M ξ s) x .one (Vt1 M ξ s) ?_ ?_ ?_ ?_ hlin ?_ ?_ hΦ
  · intro y hy
    exact tExt_eq_Vt1 M ξ s hab h8b h8c h8d (closure_inter_Iio_sub hy)
  · intro y hy
    exact gen_one_eq M ξ s hσ hρ hy.1 hy.2
  · intro y hy
    have hy' : y ≤ xbar M ξ s 1 := not_lt.1 hy
    rw [payI_self]
    exact jump1_Vt1 M ξ s ho1 ho2 hy'
  · intro y hy
    have hy' : xbar M ξ s 2 ≤ y := not_lt.1 hy
    rw [payI_one_two]
    exact jump2_Vt1 M ξ s ho3 ho4 hy'
  · intro y hy
    have hy' : y ≤ xbar M ξ s 1 := not_lt.1 hy
    have hd : (eqStrat1 M ξ s).ξ y = xstar M ξ s 1 - y := by
      show delta1 M ξ s y = _
      unfold delta1; exact max_eq_left (by linarith)
    rw [hd, show y + (xstar M ξ s 1 - y) = xstar M ξ s 1 by ring, Vt1_mid M ξ s ho1 ho2]
    have := abs_nonneg (phiOne M ξ s (xstar M ξ s 2))
    linarith
  · intro y hy
    have hy' : xbar M ξ s 2 ≤ y := not_lt.1 hy
    have hd : (eqStrat2 M ξ s).ξ y = xstar M ξ s 2 - y := by
      show delta2 M ξ s y = _
      unfold delta2; exact min_eq_left (by linarith)
    rw [hd, show y + (xstar M ξ s 2 - y) = xstar M ξ s 2 by ring, Vt1_mid M ξ s ho3 ho4]
    have := abs_nonneg (phiOne M ξ s (xstar M ξ s 1))
    linarith


end P2b17

open ImpulseGames.LinearGame in
theorem solution (M : Model) (hM : M.Standing) (ξ s : ℝ)
    (h47a : xbar M ξ s 1 < xstar M ξ s 1 ∧ xstar M ξ s 1 < xbar M ξ s 2)
    (h47b : xbar M ξ s 1 < xstar M ξ s 2 ∧ xstar M ξ s 2 < xbar M ξ s 2)
    (h48a : deriv (phiOne M ξ s) (xstar M ξ s 1) = M.lam)
    (h48b : deriv (phiOne M ξ s) (xbar M ξ s 1) = M.lam)
    (h48c : phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1))
    (h48d : phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2))
    (hQVI : ∀ y δ : ℝ, 0 ≤ δ → Vt1 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt1 M ξ s y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (x : ℝ) :
    (∀ ψ₁ : Strategy Z₁, InPhi M P W x ψ₁ (eqStrat2 M ξ s) →
      J M P W x ψ₁ (eqStrat2 M ξ s) .one ≤ Vt1 M ξ s x) ∧
    (InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) →
      J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .one = Vt1 M ξ s x) := by
  rw [P2b17.deriv_phiOne] at h48a h48b
  exact ⟨fun ψ₁ hΦ => P2b17.player_one_dev M hM ξ s h47a.1 h47a.2 h47b.1 h47b.2 h48a h48b h48c h48d
      hQVI P W hW x ψ₁ hΦ,
    fun hΦ => P2b17.player_one_eq M hM ξ s h47a.1 h47a.2 h47b.1 h47b.2 h48b h48c h48d P W hW x hΦ⟩
