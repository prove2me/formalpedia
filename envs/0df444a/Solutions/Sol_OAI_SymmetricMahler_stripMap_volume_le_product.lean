-- Prove2me | solution 1 for OAI.SymmetricMahler.stripMap_volume_le_product
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:50:47.784257+00:00
-- url     : https://prove2.me/submissions/c42f1733-31f1-46e9-b81d-16250ec10305

import Mathlib
import Definitions.Def_MahlerConjecture
import Definitions.Def_OAISMh000

section
-- module Solutions.OAIS_Mahler.Compat
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiniteStrips
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional algebra for the finite-strip construction.
The image estimate and algebraic injectivity step do not require
the analytic mass inequality. -/

namespace SymmetricMahler

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The transpose identity in the image bound. -/
theorem transpose_pairing (A : J → I → ℝ) (p : J → ℝ) (v : I → ℝ) :
    (∑ i, push A p i * v i) = ∑ j, p j * measurement A v j := by
  simp only [push, measurement, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

/-- Coefficients with bounded l1 norm define a bounded polar functional. -/
theorem image_bound (A : J → I → ℝ) (p : J → ℝ) (v : I → ℝ)
    (hv : v ∈ stripBody A) :
    (∑ i, push A p i * v i) ≤ ∑ j, |p j| := by
  rw [transpose_pairing]
  apply sum_le_sum
  intro j _
  calc
    p j * measurement A v j ≤ |p j * measurement A v j| := le_abs_self _
    _ = |p j| * |measurement A v j| := abs_mul _ _
    _ ≤ |p j| * 1 := mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = |p j| := mul_one _

end SymmetricMahler

namespace SymmetricMahler

open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The planar uniform error accumulates only by the number of rows. -/
theorem coefficient_bound (p t : J → ℝ) (ε : ℝ)
    (hp : ∀ j, |p j| ≤ t j + ε) (ht : (∑ j, t j) < 1) :
    (∑ j, |p j|) < 1 + Fintype.card J * ε := by
  calc
    (∑ j, |p j|) ≤ ∑ j, (t j + ε) := sum_le_sum (fun j _ => hp j)
    _ = (∑ j, t j) + Fintype.card J * ε := by simp [sum_add_distrib]
    _ < 1 + Fintype.card J * ε := by linarith

/-- The pointwise image estimate, including the planar error. -/
theorem image_bound_with_error (A : J → I → ℝ) (p t : J → ℝ) (ε : ℝ)
    (hp : ∀ j, |p j| ≤ t j + ε) (ht : (∑ j, t j) < 1)
    (v : I → ℝ) (hv : v ∈ stripBody A) :
    (∑ i, push A p i * v i) < 1 + Fintype.card J * ε :=
  lt_of_le_of_lt (image_bound A p v hv) (coefficient_bound p t ε hp ht)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalSeries
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal series and its logarithmic derivative. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma D_zero : D 0 = 1 := by
  unfold D
  rw [tsum_eq_single 0]
  · norm_num
  · intro k hk
    have hp : 2*k ≠ 0 := by omega
    simp [zero_pow hp]

lemma pi_cast_ne : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- Holomorphicity on the open unit disk. -/
theorem differentiableOn_F : DifferentiableOn ℂ F (ball 0 1) := by
  intro w hw
  exact (hasDerivAt_F_series (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem F_zero : F 0 = 0 := by simp [F, series_zero]

/-- The removable value of the derivative at zero. -/
theorem hasDerivAt_F_zero : HasDerivAt F (8/(Real.pi : ℂ)^2) 0 := by
  simpa [D_zero] using hasDerivAt_F_series (w := 0) (by norm_num)

lemma log_cayley_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    Complex.log (cayley w) ≠ 0 := by
  intro h
  have hq0 : cayley w ≠ 0 := div_ne_zero (one_add_ne hw) (one_sub_ne hw)
  have he : cayley w = 1 := by rw [← Complex.exp_log hq0, h, Complex.exp_zero]
  have hl : 1+w = 1-w := (div_eq_one_iff_eq (one_sub_ne hw)).mp he
  apply hw0
  linear_combination (1/2 : ℂ) * hl

/-- Nonvanishing of the derivative. -/
theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ pi_cast_ne)
  · rw [(hasDerivAt_F_log hw hw0).deriv]
    exact mul_ne_zero
      (div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw0))
      (log_cayley_ne_zero hw hw0)

/-- Conjugation symmetry of the conformal map. -/
theorem F_conj (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  simp only [F, series, term, map_mul, map_div₀, map_pow, map_ofNat,
    map_natCast, Complex.conj_ofReal, Complex.conj_tsum]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular geometry of the conformal series. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma polar_re (r θ : ℝ) : (polar r θ).re = r * Real.cos θ := by
  simp [polar]

theorem B_lt_two_div_pi (r θ : ℝ) : B r θ < 2 / Real.pi := by
  have h := mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two (2*r*Real.sin θ/(1-r^2)))
    (show 0 < 4 / Real.pi^2 by positivity)
  have he : 4 / Real.pi^2 * (Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he] using h

lemma polar_pi_sub (r θ : ℝ) : polar r (Real.pi-θ) = -starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_pi_sub, Real.sin_pi_sub]

lemma F_real_im (r : ℝ) : (F (r : ℂ)).im = 0 := by
  have h := congrArg Complex.im (F_conj (r : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

theorem Q_pi_sub (r θ : ℝ) : Q r (Real.pi-θ) = -Q r θ := by
  simp only [Q, polar_pi_sub, F_odd, F_conj, Complex.neg_re, Complex.conj_re]

theorem Q_pi_div_two (r : ℝ) : Q r (Real.pi/2) = 0 := by
  have h := Q_pi_sub r (Real.pi/2)
  rw [show Real.pi-Real.pi/2 = Real.pi/2 by ring] at h
  linarith

theorem S_zero (r : ℝ) : S r 0 = 0 := by rw [S, polar_zero, F_real_im]

theorem S_pi (r : ℝ) : S r Real.pi = 0 := by
  rw [S, polar_pi, F_odd, Complex.neg_im, F_real_im, neg_zero]

theorem Q_mem_Ioo {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Q r θ ∈ Ioo (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := Q_strictAntiOn hr hr1
  constructor
  · simpa only [Q_pi] using ha ⟨hθ.le, hθπ.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hθπ
  · simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.le, hθπ.le⟩ hθ

/-- Reflection reduces an upper-semicircle angle to [0, pi/2], and Q to |Q|. -/
theorem Q_min_angle {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Q r (min θ (Real.pi-θ)) = |Q r θ| := by
  by_cases h : θ ≤ Real.pi/2
  · rw [min_eq_left (by linarith)]
    apply (abs_of_nonneg _).symm
    have hh := (Q_strictAntiOn hr hr1).antitoneOn hθ
      (show Real.pi/2 ∈ Icc (0 : ℝ) Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩) h
    simpa only [Q_pi_div_two] using hh
  · rw [min_eq_right (by linarith), Q_pi_sub]
    apply (abs_of_nonpos _).symm
    have hh := (Q_strictAntiOn hr hr1).antitoneOn
      (show Real.pi/2 ∈ Icc (0 : ℝ) Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
      hθ (by linarith)
    simpa only [Q_pi_div_two] using hh

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarEstimates
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An elementary uniform reciprocal-arctangent estimate for the
planar construction, with the explicit absolute constant C=2. -/

namespace SymmetricMahler
open Real

lemma arctan_le_argument {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  simpa only [tan_arctan] using
    Real.le_tan (arctan_nonneg.mpr hx) (arctan_lt_pi_div_two x)

lemma half_argument_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ arctan x := by
  have hs : 0 < Real.sqrt (1 + x^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + x^2) ≤ 2 := by
    apply Real.sqrt_le_iff.2
    constructor
    · norm_num
    · nlinarith [sq_nonneg x]
  calc
    x / 2 ≤ x / Real.sqrt (1 + x^2) :=
      div_le_div_of_nonneg_left hx hs hs2
    _ = sin (arctan x) := (sin_arctan x).symm
    _ ≤ arctan x := Real.sin_le (arctan_nonneg.mpr hx)

/-- A uniform reciprocal bound with the explicit absolute constant 2. -/
theorem reciprocal_arctan_bound {v : ℝ} (hv : 0 < v) :
    1 / arctan v ≤ 2 / Real.pi + 2 / v := by
  have ha : 0 < arctan v := arctan_pos.mpr hv
  rcases le_total v 1 with hv1 | h1v
  · have hlower := half_argument_le_arctan hv.le hv1
    have hrecip : 1 / arctan v ≤ 2 / v :=
      (div_le_div_iff₀ ha hv).2 (by nlinarith)
    have hnonneg : 0 ≤ 2 / Real.pi := by positivity
    linarith
  · have hquarter : Real.pi / 4 ≤ arctan v := by
      simpa only [arctan_one] using arctan_strictMono.monotone h1v
    have hcompl : Real.pi / 2 - arctan v ≤ 1 / v := by
      rw [← arctan_inv_of_pos hv, one_div]
      exact arctan_le_argument (inv_nonneg.mpr hv.le)
    have hcompl' : (Real.pi / 2 - arctan v) * v ≤ 1 :=
      (le_div_iff₀ hv).1 hcompl
    have hap : 1 ≤ arctan v * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hrearrange : 2 / Real.pi + 2 / v =
        (2 * v + 2 * Real.pi) / (Real.pi * v) := by
      field_simp
    rw [hrearrange]
    apply (div_le_div_iff₀ ha (mul_pos Real.pi_pos hv)).2
    nlinarith

end SymmetricMahler

namespace SymmetricMahler
open Real

/-- The reciprocal angular-speed estimate, with C = π²/4. -/
theorem angular_speed_inverse_bound {r θ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hθ : 0 < sin θ) :
    1 / angularSpeed r θ ≤ Real.pi / 2 +
      (Real.pi^2 / 4) * ((1-r^2) / (r * sin θ)) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hv : 0 < 2*r*sin θ/(1-r^2) := by positivity
  have ha : arctan (2*r*sin θ/(1-r^2)) ≠ 0 := ne_of_gt (arctan_pos.mpr hv)
  have hp := mul_le_mul_of_nonneg_left (reciprocal_arctan_bound hv)
    (show 0 ≤ Real.pi^2/4 by positivity)
  calc
    1 / angularSpeed r θ = (Real.pi^2/4) *
        (1/arctan (2*r*sin θ/(1-r^2))) := by
      dsimp [angularSpeed]
      field_simp
    _ ≤ (Real.pi^2/4) * (2/Real.pi + 2/(2*r*sin θ/(1-r^2))) := hp
    _ = Real.pi / 2 + (Real.pi^2/4)*((1-r^2)/(r*sin θ)) := by
      field_simp
      ; ring

/-- The pointwise estimate on the first half of the tail integral. -/
theorem tail_first_half {L t : ℝ} (hL : 0 < L) (_ht : 0 ≤ t)
    (htL : t ≤ L/2) :
    exp (-t) * sqrt (t/(L-t)) ≤ exp (-t) := by
  have hden : 0 < L-t := by linarith
  have hr : t/(L-t) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hs : sqrt (t/(L-t)) ≤ 1 := by
    apply sqrt_le_iff.2
    exact ⟨by norm_num, by simpa using hr⟩
  nlinarith [exp_pos (-t)]

/-- The pointwise integrable singular majorant on the second half. -/
theorem tail_second_half {L t : ℝ} (_hL : 0 < L)
    (ht : L/2 ≤ t) (htL : t < L) :
    exp (-t) * sqrt (t/(L-t)) ≤
      exp (-L/2) * sqrt L / sqrt (L-t) := by
  have ht0 : 0 ≤ t := by linarith
  have hden : 0 < sqrt (L-t) := sqrt_pos.2 (by linarith)
  have hexp : exp (-t) ≤ exp (-L/2) := exp_le_exp.mpr (by linarith)
  have hs : sqrt t / sqrt (L-t) ≤ sqrt L / sqrt (L-t) :=
    div_le_div_of_nonneg_right (sqrt_le_sqrt htL.le) hden.le
  rw [sqrt_div ht0]
  calc
    exp (-t) * (sqrt t / sqrt (L-t)) ≤ exp (-L/2) *
        (sqrt L / sqrt (L-t)) :=
      mul_le_mul hexp hs (by positivity) (by positivity)
    _ = exp (-L/2) * sqrt L / sqrt (L-t) := by ring

/-- The elementary maximization for the uniform-L bound. -/
theorem uniform_tail_constant (L : ℝ) :
    1 + 2*L*exp (-L/2) ≤ 1 + 4/exp 1 := by
  have h := mul_exp_neg_le_exp_neg_one (L/2)
  simp only [exp_neg, div_eq_mul_inv] at h
  have he : exp (-L/2) = (exp (L/2))⁻¹ := by rw [← exp_neg]; congr 1 ; ring
  rw [he]
  simp only [div_eq_mul_inv]
  nlinarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_TailIntegral
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory Set

lemma inverse_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    1 / sqrt x = x ^ (-(1/2 : ℝ)) := by
  rw [one_div, sqrt_eq_rpow, rpow_neg hx]

lemma inverse_sqrt_integrable {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1 / sqrt x) volume 0 b := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
    (r := -(1/2 : ℝ)) (by norm_num)
  apply h.congr
  intro x hx
  rw [uIoc_of_le hb] at hx
  exact (inverse_sqrt_eq_rpow hx.1.le).symm

lemma inverse_sqrt_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in (0 : ℝ)..b, 1 / sqrt x) = 2 * sqrt b := by
  calc
    (∫ x in (0 : ℝ)..b, 1 / sqrt x) = ∫ x in (0 : ℝ)..b, x ^ (-(1/2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact inverse_sqrt_eq_rpow hx.1
    _ = (b ^ (-(1/2 : ℝ)+1) - (0 : ℝ) ^ (-(1/2 : ℝ)+1)) / (-(1/2 : ℝ)+1) :=
      integral_rpow (Or.inl (by norm_num))
    _ = 2 * sqrt b := by
      norm_num [← sqrt_eq_rpow]
      ring

lemma shifted_inverse_sqrt_integrable {a L : ℝ} (haL : a ≤ L) :
    IntervalIntegrable (fun t : ℝ => 1 / sqrt (L-t)) volume a L := by
  have h := (inverse_sqrt_integrable (sub_nonneg.mpr haL)).comp_sub_left L
  convert h.symm using 1 <;> ring

lemma shifted_inverse_sqrt_integral {a L : ℝ} (haL : a ≤ L) :
    (∫ t in a..L, 1 / sqrt (L-t)) = 2 * sqrt (L-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => 1 / sqrt u) L]
  simpa using inverse_sqrt_integral (sub_nonneg.mpr haL)

/-- The singular tail integral is well-defined even at its upper endpoint. -/
theorem tail_integrable {L : ℝ} (hL : 0 < L) :
    IntervalIntegrable (fun t : ℝ => exp (-t) * sqrt (t/(L-t))) volume 0 L := by
  have h := (shifted_inverse_sqrt_integrable (a := 0) hL.le).continuousOn_mul
    (show ContinuousOn (fun t : ℝ => exp (-t) * sqrt t) (uIcc 0 L) from
      (by fun_prop : Continuous (fun t : ℝ => exp (-t) * sqrt t)).continuousOn)
  apply h.congr
  intro t ht
  rw [uIoc_of_le hL.le] at ht
  dsimp only
  rw [sqrt_div ht.1.le]
  ring

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The uniform-L integral estimate,
including integrability at the singular endpoint. -/
theorem uniform_tail_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, exp (-t) * sqrt (t/(L-t))) ≤ 1 + 4/exp 1 := by
  have hhalf : 0 ≤ L/2 := by linarith
  have hhalfL : L/2 ≤ L := by linarith
  have hfull := tail_integrable hL
  have hfirst : IntervalIntegrable (fun t : ℝ => exp (-t)*sqrt (t/(L-t))) volume 0 (L/2) :=
    hfull.mono_set (by
      intro t ht
      rw [uIcc_of_le hhalf] at ht
      rw [uIcc_of_le hL.le]
      exact ⟨ht.1, le_trans ht.2 hhalfL⟩)
  have hsecond : IntervalIntegrable (fun t : ℝ => exp (-t)*sqrt (t/(L-t))) volume (L/2) L :=
    hfull.mono_set (by
      intro t ht
      rw [uIcc_of_le hhalfL] at ht
      rw [uIcc_of_le hL.le]
      exact ⟨le_trans hhalf ht.1, ht.2⟩)
  have hexp : IntervalIntegrable (fun t : ℝ => exp (-t)) volume 0 (L/2) :=
    (by fun_prop : Continuous (fun t : ℝ => exp (-t))).intervalIntegrable _ _
  have hfirst_bound : (∫ t in (0 : ℝ)..L/2, exp (-t)*sqrt (t/(L-t))) ≤ 1 := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..L/2, exp (-t) :=
        intervalIntegral.integral_mono_on hhalf hfirst hexp
          (fun t ht => tail_first_half hL ht.1 ht.2)
      _ = 1-exp (-(L/2)) := by
        rw [intervalIntegral.integral_comp_neg exp, integral_exp]
        simp
      _ ≤ 1 := by linarith [exp_pos (-(L/2))]
  have hinv := shifted_inverse_sqrt_integrable (a := L/2) hhalfL
  have hmajor := hinv.const_mul (exp (-L/2)*sqrt L)
  have hsecond_bound : (∫ t in L/2..L, exp (-t)*sqrt (t/(L-t))) ≤
      2*L*exp (-L/2) := by
    calc
      _ ≤ ∫ t in L/2..L, (exp (-L/2)*sqrt L)*(1/sqrt (L-t)) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hhalfL hsecond hmajor
        intro t ht
        simpa only [mul_one_div] using tail_second_half hL ht.1.le ht.2
      _ = (exp (-L/2)*sqrt L)*(2*sqrt (L-L/2)) := by
        rw [intervalIntegral.integral_const_mul, shifted_inverse_sqrt_integral hhalfL]
      _ ≤ (exp (-L/2)*sqrt L)*(2*sqrt L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh : sqrt (L-L/2) ≤ sqrt L := sqrt_le_sqrt (by linarith)
        linarith
      _ = 2*L*exp (-L/2) := by
        calc
          _ = 2 * exp (-L/2) * (sqrt L)^2 := by ring
          _ = 2*L*exp (-L/2) := by rw [sq_sqrt hL.le]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond]
  exact le_trans (add_le_add hfirst_bound hsecond_bound) (uniform_tail_constant L)

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory

lemma rescaled_tail_ratio {m b : ℝ} (hm : m ≠ 0) (r : ℝ) :
    (m-m*r)/(m*(1-b)-(m-m*r)) = (1-r)/(r-b) := by
  rw [show m*(1-b)-(m-m*r) = m*(r-b) by ring,
    show m-m*r = m*(1-r) by ring, mul_div_mul_left _ _ hm]

/-- The change of variables t=m(1-r) in the error tail, with
normalization factors and endpoint orientations. -/
theorem rescaled_tail_integral {m b : ℝ} (hm : 0 < m) :
    (∫ r in b..(1 : ℝ), m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) =
      ∫ t in (0 : ℝ)..m*(1-b), exp (-t)*sqrt (t/(m*(1-b)-t)) := by
  let K : ℝ → ℝ := fun t => exp (-t)*sqrt (t/(m*(1-b)-t))
  have hfun : (fun r : ℝ => m*K (m-m*r)) =
      (fun r : ℝ => m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
    funext r
    dsimp [K]
    rw [rescaled_tail_ratio hm.ne', show -(m-m*r) = -m*(1-r) by ring]
    ring
  rw [← hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_mul K hm.ne' m]
  simp only [smul_eq_mul, mul_one, sub_self]
  rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  congr 1
  ring

/-- Integrability also survives the affine rescaling in the error estimate. -/
theorem rescaled_tail_integrable {m b : ℝ} (hm : 0 < m) (hb : b < 1) :
    IntervalIntegrable
      (fun r : ℝ => m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) volume b 1 := by
  have hL : 0 < m*(1-b) := mul_pos hm (sub_pos.mpr hb)
  have h := ((tail_integrable hL).comp_sub_left m).symm.comp_mul_left (c := m)
  have hlower : (m-m*(1-b))/m = b := by field_simp; ring
  simp only [sub_zero, hlower, div_self hm.ne'] at h
  have h' := h.const_mul m
  apply h'.congr
  intro r _
  dsimp only
  rw [rescaled_tail_ratio hm.ne', show -(m-m*r) = -m*(1-r) by ring]
  ring

/-- The uniform bound after substitution, independent of b and m. -/
theorem rescaled_tail_bound {m b : ℝ} (hm : 0 < m) (hb : b < 1) :
    (∫ r in b..(1 : ℝ), m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) ≤
      1 + 4/exp 1 := by
  rw [rescaled_tail_integral hm]
  exact uniform_tail_integral (mul_pos hm (sub_pos.mpr hb))

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory

lemma right_inverse_sqrt_integrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r : ℝ => 1/sqrt (r-a)) volume a b := by
  have h := (inverse_sqrt_integrable (sub_nonneg.mpr hab)).comp_sub_right a
  convert h using 1 <;> ring

lemma right_inverse_sqrt_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/sqrt (r-a)) = 2*sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => 1/sqrt u) a]
  simpa using inverse_sqrt_integral (sub_nonneg.mpr hab)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ErrorBound
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory

/-- Exponential majorization on the outer interval. -/
theorem radial_power_bound {m r : ℝ} (hm : 2 ≤ m) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ (2*m-3/2 : ℝ) ≤ exp (-m*(1-r)) := by
  by_cases hz : r = 0
  · rw [hz, zero_rpow (show (2*m-3/2 : ℝ) ≠ 0 by linarith)]
    positivity
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    rw [rpow_def_of_pos hrpos]
    apply exp_le_exp.mpr
    have hlog := log_le_sub_one_of_pos hrpos
    have hsign := log_nonpos hr hr1
    have hneg := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ m-3/2 by linarith) hsign
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ m by linarith)
    nlinarith

end SymmetricMahler

namespace SymmetricMahler
open Real

lemma log_le_half {x : ℝ} (hx : 0 < x) : log x ≤ x/2 := by
  have h := log_le_sub_one_of_pos (show 0 < x/2 by positivity)
  rw [log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma radial_log_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r ≤ log ((1+r)/(1-r)) := by
  have hd : 0 < 1-r := by linarith
  have hfrac : 1/(1-r) ≤ (1+r)/(1-r) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hlog := log_le_log (one_div_pos.mpr hd) hfrac
  rw [one_div, log_inv] at hlog
  have hlin := log_le_sub_one_of_pos hd
  linarith

/-- A concrete global positive lower bound for the radial derivative. -/
theorem radial_derivative_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    4/Real.pi^2 ≤ radialDerivative r := by
  have hratio : 1 ≤ log ((1+r)/(1-r))/r :=
    (le_div_iff₀ hr).2 (by simpa using radial_log_lower hr hr1)
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4/Real.pi^2 by positivity)
  calc
    4/Real.pi^2 = (4/Real.pi^2)*1 := (mul_one _).symm
    _ ≤ (4/Real.pi^2)*(log ((1+r)/(1-r))/r) := h
    _ = radialDerivative r := by dsimp [radialDerivative]; field_simp

/-- The logarithmic boundary layer starts at 1-log(m)/m. -/
lemma boundary_layer_log_lower {m r : ℝ} (hm : 1 < m)
    (hr : 0 < r) (hr1 : r < 1) (hlayer : 1-log m/m ≤ r) :
    log m/2 ≤ log ((1+r)/(1-r)) := by
  have hmpos : 0 < m := by linarith
  have hlm : 0 < log m := log_pos hm
  have hd : 0 < 1-r := by linarith
  have hgap : (1-r)*m ≤ log m := (le_div_iff₀ hmpos).1 (by linarith : 1-r ≤ log m/m)
  have hfrac : m/log m ≤ 1/(1-r) :=
    (div_le_div_iff₀ hlm hd).2 (by nlinarith)
  have hlog := log_le_log (div_pos hmpos hlm) hfrac
  rw [log_div hmpos.ne' hlm.ne', one_div, log_inv] at hlog
  have hh := log_le_half hlm
  have hfrac2 : 1/(1-r) ≤ (1+r)/(1-r) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hlog2 := log_le_log (one_div_pos.mpr hd) hfrac2
  rw [one_div, log_inv] at hlog2
  linarith

/-- The estimate M'≥c log m holds with c=2/π². -/
theorem boundary_layer_derivative_lower {m r : ℝ} (hm : 1 < m)
    (hr : 0 < r) (hr1 : r < 1) (hlayer : 1-log m/m ≤ r) :
    (2/Real.pi^2)*log m ≤ radialDerivative r := by
  have hlm : 0 < log m := log_pos hm
  have hlog := boundary_layer_log_lower hm hr hr1 hlayer
  have hratio : log m/2 ≤ log ((1+r)/(1-r))/r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4/Real.pi^2 by positivity)
  calc
    (2/Real.pi^2)*log m = (4/Real.pi^2)*(log m/2) := by ring
    _ ≤ (4/Real.pi^2)*(log ((1+r)/(1-r))/r) := h
    _ = radialDerivative r := by dsimp [radialDerivative]; field_simp

end SymmetricMahler

namespace SymmetricMahler
open Real Set

/-- The global M-increment estimate obtained from the actual radial derivative,
with only open-interval derivatives required, including when the left endpoint is 0. -/
theorem radial_increment_lower {M : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt M (radialDerivative x) x) :
    (4/Real.pi^2)*(b-a) ≤ M b-M a := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  · obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope M radialDerivative hlt hcont hderiv
    have hlow := radial_derivative_lower (show 0 < x by linarith [hx.1])
      (show x < 1 by linarith [hx.2])
    rw [heq] at hlow
    exact (le_div_iff₀ (sub_pos.mpr hlt)).1 hlow

/-- The strengthened increment estimate inside the logarithmic boundary layer. -/
theorem boundary_layer_increment_lower {M : ℝ → ℝ} {m a b : ℝ}
    (hm : 1 < m) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hlayer : 1-log m/m ≤ a)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt M (radialDerivative x) x) :
    ((2/Real.pi^2)*log m)*(b-a) ≤ M b-M a := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  · obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope M radialDerivative hlt hcont hderiv
    have hlow := boundary_layer_derivative_lower hm
      (show 0 < x by linarith [hx.1]) (show x < 1 by linarith [hx.2])
      (show 1-log m/m ≤ x by linarith [hx.1])
    rw [heq] at hlow
    exact (le_div_iff₀ (sub_pos.mpr hlt)).1 hlow

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- Pointwise domination by the exactly integrated outer-tail kernel.
Here c is the lower slope for M on the boundary layer. -/
theorem error_integrand_outer_bound {M : ℝ → ℝ} {r₀ m c b r : ℝ}
    (hm : 2 ≤ m) (hc : 0 < c) (hr : 0 ≤ r) (hbr : b < r) (hr1 : r < 1)
    (hincrement : c*(r-b) ≤ M r-M r₀) :
    errorIntegrand M r₀ m r ≤ sqrt (2/c) *
      (m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
  have hden : 0 < c*(r-b) := mul_pos hc (sub_pos.mpr hbr)
  have hM : 0 < M r-M r₀ := lt_of_lt_of_le hden hincrement
  have hnum : 0 ≤ 1-r^2 := by nlinarith
  have hratio : (1-r^2)/(M r-M r₀) ≤ (2/c)*((1-r)/(r-b)) := by
    calc
      _ ≤ (1-r^2)/(c*(r-b)) := div_le_div_of_nonneg_left hnum hden hincrement
      _ ≤ (2*(1-r))/(c*(r-b)) :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (1-r)]) hden.le
      _ = (2/c)*((1-r)/(r-b)) := by field_simp
  have hs := sqrt_le_sqrt hratio
  rw [sqrt_div hnum, sqrt_mul (show 0 ≤ 2/c by positivity)] at hs
  have hpow := radial_power_bound hm hr hr1.le
  calc
    errorIntegrand M r₀ m r = m *
        (r^(2*m-3/2 : ℝ) * (sqrt (1-r^2)/sqrt (M r-M r₀))) := by
      dsimp [errorIntegrand]
      ring
    _ ≤ m * (exp (-m*(1-r)) *
        (sqrt (2/c)*sqrt ((1-r)/(r-b)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hpow hs (by positivity) (exp_nonneg _)) (by linarith)
    _ = sqrt (2/c)*(m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by ring

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set Filter

/-- Integrability of the original outer error follows from the singular majorant;
measurability is explicit so no unproved integrability is hidden in the integral. -/
theorem outer_error_integrable {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c) (hb : 0 ≤ b) (hb1 : b < 1)
    (hincrement : ∀ r ∈ Ioo b 1, c*(r-b) ≤ M r-M r₀) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume b 1 := by
  have hmpos : 0 < m := by linarith
  have hg := (rescaled_tail_integrable hmpos hb1).const_mul (sqrt (2/c))
  have hmeas : Measurable (errorIntegrand M r₀ m) := by
    change Measurable (fun r : ℝ => m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀))
    fun_prop
  apply hg.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hb1.le] at hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  rcases hr.2.eq_or_lt with heq | hlt
  · subst r
    simp [errorIntegrand]
  · have hn : 0 ≤ errorIntegrand M r₀ m r := by
      dsimp [errorIntegrand]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact error_integrand_outer_bound hm hc hr0 hr.1 hlt (hincrement r ⟨hr.1,hlt⟩)

/-- The outer portion of the error integral, with an explicit constant. -/
theorem outer_error_integral_bound {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c) (hb : 0 ≤ b) (hb1 : b < 1)
    (hincrement : ∀ r ∈ Ioo b 1, c*(r-b) ≤ M r-M r₀) :
    (∫ r in b..(1 : ℝ), errorIntegrand M r₀ m r) ≤
      sqrt (2/c)*(1+4/exp 1) := by
  have hmpos : 0 < m := by linarith
  have hf := outer_error_integrable hM hm hc hb hb1 hincrement
  have hg := (rescaled_tail_integrable hmpos hb1).const_mul (sqrt (2/c))
  calc
    _ ≤ ∫ r in b..(1 : ℝ), sqrt (2/c)*
        (m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hb1.le hf hg
      intro r hr
      exact error_integrand_outer_bound hm hc (by linarith [hr.1]) hr.1 hr.2
        (hincrement r hr)
    _ = sqrt (2/c)*(∫ r in b..(1 : ℝ),
        m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := intervalIntegral.integral_const_mul _ _
    _ ≤ sqrt (2/c)*(1+4/exp 1) :=
      mul_le_mul_of_nonneg_left (rescaled_tail_bound hmpos hb1) (sqrt_nonneg _)

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The inner error is controlled by an integrable square-root singularity. -/
theorem error_integrand_inner_bound {M : ℝ → ℝ} {r₀ m c b r : ℝ}
    (hm : 2 ≤ m) (hc : 0 < c) (hr : 0 ≤ r) (hr₀ : r₀ < r)
    (hrb : r ≤ b) (_hb1 : b ≤ 1)
    (hincrement : c*(r-r₀) ≤ M r-M r₀) :
    errorIntegrand M r₀ m r ≤
      (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
  have hb : 0 ≤ b := le_trans hr hrb
  have hden : 0 < sqrt (c*(r-r₀)) := sqrt_pos.2 (mul_pos hc (sub_pos.mpr hr₀))
  have hM : sqrt (c*(r-r₀)) ≤ sqrt (M r-M r₀) := sqrt_le_sqrt hincrement
  have hpow : r^(2*m-3/2 : ℝ) ≤ b^(2*m-3/2 : ℝ) :=
    rpow_le_rpow hr hrb (by linarith)
  have hnum : sqrt (1-r^2) ≤ 1 := by
    apply sqrt_le_iff.2
    exact ⟨by norm_num, by nlinarith [sq_nonneg r]⟩
  have hprod : m*r^(2*m-3/2 : ℝ)*sqrt (1-r^2) ≤ m*b^(2*m-3/2 : ℝ) := by
    have h := mul_le_mul hpow hnum (sqrt_nonneg _) (rpow_nonneg hb _)
    nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ m by linarith)]
  calc
    errorIntegrand M r₀ m r ≤ m*b^(2*m-3/2 : ℝ)/sqrt (M r-M r₀) :=
      div_le_div_of_nonneg_right hprod (sqrt_nonneg _)
    _ ≤ m*b^(2*m-3/2 : ℝ)/sqrt (c*(r-r₀)) :=
      div_le_div_of_nonneg_left (by positivity) hden hM
    _ = (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
      rw [sqrt_mul hc.le]
      field_simp

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set Filter

/-- Integrability of the inner portion follows from the square-root majorant. -/
theorem inner_error_integrable {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c)
    (hr₀ : 0 ≤ r₀) (hr₀b : r₀ ≤ b) (hb1 : b ≤ 1)
    (hincrement : ∀ r ∈ Ioc r₀ b, c*(r-r₀) ≤ M r-M r₀) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume r₀ b := by
  have hb : 0 ≤ b := le_trans hr₀ hr₀b
  have hg := (right_inverse_sqrt_integrable hr₀b).const_mul
    (m*b^(2*m-3/2 : ℝ)/sqrt c)
  have hmeas : Measurable (errorIntegrand M r₀ m) := by
    change Measurable (fun r : ℝ => m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀))
    fun_prop
  apply hg.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hr₀b] at hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hn : 0 ≤ errorIntegrand M r₀ m r := by
    dsimp [errorIntegrand]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact error_integrand_inner_bound hm hc hr0 hr.1 hr.2 hb1 (hincrement r hr)

/-- The bound on the inner portion of the error integral, with its constant. -/
theorem inner_error_integral_bound {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c)
    (hr₀ : 0 ≤ r₀) (hr₀b : r₀ ≤ b) (hb1 : b ≤ 1)
    (hincrement : ∀ r ∈ Ioc r₀ b, c*(r-r₀) ≤ M r-M r₀) :
    (∫ r in r₀..b, errorIntegrand M r₀ m r) ≤ 2*m*b^(2*m-3/2 : ℝ)/sqrt c := by
  have hb : 0 ≤ b := le_trans hr₀ hr₀b
  have hf := inner_error_integrable hM hm hc hr₀ hr₀b hb1 hincrement
  have hg := (right_inverse_sqrt_integrable hr₀b).const_mul
    (m*b^(2*m-3/2 : ℝ)/sqrt c)
  have hcoeff : 0 ≤ m*b^(2*m-3/2 : ℝ)/sqrt c := by positivity
  calc
    _ ≤ ∫ r in r₀..b, (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hr₀b hf hg
      intro r hr
      exact error_integrand_inner_bound hm hc (by linarith [hr.1]) hr.1 hr.2.le hb1
        (hincrement r ⟨hr.1,hr.2.le⟩)
    _ = (m*b^(2*m-3/2 : ℝ)/sqrt c)*(2*sqrt (b-r₀)) := by
      rw [intervalIntegral.integral_const_mul, right_inverse_sqrt_integral hr₀b]
    _ ≤ (m*b^(2*m-3/2 : ℝ)/sqrt c)*2 := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      have hs : sqrt (b-r₀) ≤ 1 := sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
      linarith
    _ = 2*m*b^(2*m-3/2 : ℝ)/sqrt c := by ring

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_UniformError
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory Set

lemma radial_cutoff_bounds {m : ℝ} (hm : 1 < m) :
    0 ≤ radialCutoff m ∧ radialCutoff m < 1 := by
  have hm0 : 0 < m := by linarith
  have hl := log_le_sub_one_of_pos hm0
  have hp : 0 < log m/m := div_pos (log_pos hm) hm0
  have hlt : log m/m < 1 := (div_lt_one hm0).2 (by linarith)
  dsimp [radialCutoff]
  constructor <;> linarith

/-- The whole singular error integral is bounded uniformly in its basepoint.
The only analytic premise about M is the radial derivative formula plus
continuity/measurability; every integral estimate and endpoint argument is proved. -/
theorem uniform_error_bound {M : ℝ → ℝ}
    (hM : Measurable M) (hcont : ContinuousOn M (Ico 0 1))
    (hderiv : ∀ r ∈ Ioo 0 1, HasDerivAt M (radialDerivative r) r)
    {m r₀ : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume r₀ 1 ∧
      (∫ r in r₀..(1 : ℝ), errorIntegrand M r₀ m r) ≤ errorEnvelope m := by
  have hm1 : 1 < m := by linarith
  have hc0 : (0 : ℝ) < 4/Real.pi^2 := by positivity
  have hc1 : 0 < (2/Real.pi^2)*log m := mul_pos (by positivity) (log_pos hm1)
  have hcut := radial_cutoff_bounds hm1
  have hglobal : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 →
      (4/Real.pi^2)*(b-a) ≤ M b-M a := by
    intro a b ha hab hb
    apply radial_increment_lower ha hab hb
    · apply hcont.mono
      intro x hx
      exact ⟨le_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    · intro x hx
      exact hderiv x ⟨lt_of_le_of_lt ha hx.1, lt_trans hx.2 hb⟩
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 → M a ≤ M b := by
    intro a b ha hab hb
    have h := hglobal a b ha hab hb
    have hnonneg := mul_nonneg hc0.le (sub_nonneg.mpr hab)
    linarith
  have hboundary : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 → radialCutoff m ≤ a →
      ((2/Real.pi^2)*log m)*(b-a) ≤ M b-M a := by
    intro a b ha hab hb hlayer
    apply boundary_layer_increment_lower hm1 ha hab hb hlayer
    · apply hcont.mono
      intro x hx
      exact ⟨le_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    · intro x hx
      exact hderiv x ⟨lt_of_le_of_lt ha hx.1, lt_trans hx.2 hb⟩
  have htail : ∀ b : ℝ, r₀ ≤ b → 0 ≤ b → b < 1 → radialCutoff m ≤ b →
      IntervalIntegrable (errorIntegrand M r₀ m) volume b 1 ∧
      (∫ r in b..(1 : ℝ), errorIntegrand M r₀ m r) ≤
        sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1) := by
    intro b hr₀b hb hb1 hcb
    have hi : ∀ r ∈ Ioo b 1, ((2/Real.pi^2)*log m)*(r-b) ≤ M r-M r₀ := by
      intro r hr
      have h := hboundary b r hb hr.1.le hr.2 hcb
      have hmb := hmono r₀ b hr₀ hr₀b hb1
      linarith
    exact ⟨outer_error_integrable hM hm hc1 hb hb1 hi,
      outer_error_integral_bound hM hm hc1 hb hb1 hi⟩
  by_cases hsplit : r₀ ≤ radialCutoff m
  · have hi : ∀ r ∈ Ioc r₀ (radialCutoff m), (4/Real.pi^2)*(r-r₀) ≤ M r-M r₀ := by
      intro r hr
      exact hglobal r₀ r hr₀ hr.1.le (lt_of_le_of_lt hr.2 hcut.2)
    have hinner := inner_error_integrable hM hm hc0 hr₀ hsplit hcut.2.le hi
    have hinnerbound := inner_error_integral_bound hM hm hc0 hr₀ hsplit hcut.2.le hi
    have houter := htail (radialCutoff m) hsplit hcut.1 hcut.2 le_rfl
    constructor
    · exact hinner.trans houter.1
    · rw [← intervalIntegral.integral_add_adjacent_intervals hinner houter.1]
      exact add_le_add hinnerbound houter.2
  · have houter := htail r₀ le_rfl hr₀ hr₀1 (le_of_not_ge hsplit)
    refine ⟨houter.1, ?_⟩
    have hinnernonneg : 0 ≤ 2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) := by
      have := hcut.1
      have hm0 : 0 ≤ m := by linarith
      positivity
    exact le_trans houter.2 (by dsimp [errorEnvelope]; linarith)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RadialBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex MeasureTheory Set

lemma measurable_conformal_F : Measurable MahlerConformal.F := by
  change Measurable (fun w : ℂ => (8/(Real.pi : ℂ)^2) *
    ∑' k : ℕ, MahlerConformal.term 2 k w)
  apply measurable_const.mul
  apply Measurable.tsum
  intro k
  change Measurable (fun w : ℂ => w^(2*k+1) / ((2*k+1 : ℕ) : ℂ)^2)
  fun_prop

lemma measurable_radialMap : Measurable radialMap := by
  change Measurable (fun r : ℝ => (MahlerConformal.F (r : ℂ)).re)
  exact Complex.measurable_re.comp (measurable_conformal_F.comp Complex.measurable_ofReal)

lemma continuousOn_radialMap : ContinuousOn radialMap (Ico 0 1) := by
  intro r hr
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr.1] using hr.2
  have h := (MahlerConformal.hasDerivAt_F_series hw).real_of_complex
  exact h.continuousAt.continuousWithinAt

theorem hasDerivAt_radialMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt radialMap (radialDerivative r) r := by
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hr] using hr1
  have hw0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := (MahlerConformal.hasDerivAt_F_log hw hw0).real_of_complex
  have hq : 0 ≤ (1+r)/(1-r) := by positivity
  have hcast : (1+(r : ℂ))/(1-(r : ℂ)) = (((1+r)/(1-r) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hd : 4/((Real.pi : ℂ)^2*(r : ℂ))*Complex.log ((1+(r : ℂ))/(1-(r : ℂ))) =
      (radialDerivative r : ℂ) := by
    rw [hcast, ← Complex.ofReal_log hq]
    dsimp [radialDerivative]
    push_cast
    rfl
  rw [hd, Complex.ofReal_re] at h
  exact h

/-- The actual series obeys the quantitative radial increment estimate. -/
theorem conformal_radial_increment {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (4/Real.pi^2)*(b-a) ≤ radialMap b-radialMap a := by
  apply radial_increment_lower ha hab hb
  · exact continuousOn_radialMap.mono (fun x hx => ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)
  · intro x hx
    exact hasDerivAt_radialMap (by linarith [hx.1]) (hx.2.trans hb)

/-- Strict radial monotonicity is proved on the entire positive real radius. -/
theorem strictMonoOn_radialMap : StrictMonoOn radialMap (Ico 0 1) := by
  intro a ha b hb hab
  have h := conformal_radial_increment ha.1 hab.le hb.2
  have hpos : 0 < (4/Real.pi^2)*(b-a) := by positivity
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_VerticalSpeed
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology

/-- The Cauchy--Riemann algebra on a real-level curve. -/
theorem vertical_speed_algebra {z : ℂ} {t : ℝ}
    (hreal : (z*(1+Complex.I*(t : ℂ))).re = 0) (him : 0 < z.im) :
    (z*(1+Complex.I*(t : ℂ))).im = Complex.normSq z/z.im := by
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.I_re,
    Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.one_im] at hreal ⊢
  have hmul := congrArg (fun x : ℝ => z.re*x) hreal
  rw [Complex.normSq_apply]
  field_simp
  nlinarith

/-- The derivative of a polar curve with differentiable angle. -/
theorem hasDerivAt_polarCurve {θ : ℝ → ℝ} {r t : ℝ} (hθ : HasDerivAt θ t r) :
    HasDerivAt (polarCurve θ)
      (Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have hc := (Complex.hasDerivAt_exp ((θ r : ℂ)*Complex.I)).comp r
    (hθ.ofReal_comp.mul_const Complex.I)
  have h := (Complex.ofRealCLM.hasDerivAt (x := r)).mul hc
  have heq : Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ)) =
      Complex.ofRealCLM 1 * (Complex.exp ∘ fun y => (θ y : ℂ)*Complex.I) r +
      Complex.ofRealCLM r * (Complex.exp ((θ r : ℂ)*Complex.I)*((t : ℂ)*Complex.I)) := by
    dsimp only [Complex.ofRealCLM_apply, Function.comp_def]
    push_cast
    ring
  rw [← heq] at h
  exact h

/-- The image curve's derivative is obtained by the actual complex chain rule. -/
theorem hasDerivAt_image_polarCurve {F : ℂ → ℂ} {θ : ℝ → ℝ} {r t : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r) :
    HasDerivAt (fun s => F (polarCurve θ s))
      ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have h := hF.comp r (hasDerivAt_polarCurve hθ)
  rw [mul_assoc]
  exact h

/-- Constancy of the real part forces the image curve to move upward
under the angular derivative sign condition. -/
theorem image_polarCurve_vertical_derivative {F : ℂ → ℂ} {θ : ℝ → ℝ}
    {r t q : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r)
    (hlevel : ∀ᶠ s in 𝓝 r, (F (polarCurve θ s)).re = q)
    (him : 0 < (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) :
    HasDerivAt (fun s => (F (polarCurve θ s)).im)
      (Complex.normSq (g*Complex.exp ((θ r : ℂ)*Complex.I)) /
        (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) r := by
  have h := hasDerivAt_image_polarCurve hF hθ
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have hconst : HasDerivAt (fun s => (F (polarCurve θ s)).re) 0 r :=
    (hasDerivAt_const r q).congr_of_eventuallyEq hlevel
  have hzero := hre.unique hconst
  have hreal : ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))).re = 0 := hzero
  have himder := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  simpa only [Complex.imCLM_apply, Function.comp_def, vertical_speed_algebra hreal him] using! himder

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ImplicitAngle
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The scalar implicit function theorem with the angular nonzero derivative
as its explicit hypothesis. -/
theorem exists_local_real_level {f : ℝ × ℝ → ℝ} {a b c : ℝ}
    (hC : ContDiffAt ℝ ∞ f (a,b))
    (hD : HasDerivAt (fun y => f (a,y)) c b) (hc : c ≠ 0) :
    ∃ θ : ℝ → ℝ, θ a = b ∧ ContDiffAt ℝ ∞ θ a ∧
      ∀ᶠ r in 𝓝 a, f (r,θ r) = f (a,b) := by
  let D := fderiv ℝ f (a,b) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hfd : HasFDerivAt (fun y => f (a,y)) D b :=
    (hC.differentiableAt (by norm_num)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have heq := hfd.unique hD.hasFDerivAt
  have hval (x : ℝ) : D x = x*c := by
    rw [heq]
    simp
  have hinj : Function.Injective D := by
    intro x y h
    rw [hval, hval] at h
    exact mul_right_cancel₀ hc h
  have hsurj : Function.Surjective D := by
    intro x
    refine ⟨x/c, ?_⟩
    rw [hval]
    field_simp
  have hInv : D.IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), ?_⟩
    rfl
  refine ⟨hC.implicitFunction (by norm_num) hInv, ?_, ?_, ?_⟩
  · exact hC.implicitFunction_apply_self (by norm_num) hInv
  · exact hC.contDiffAt_implicitFunction (by norm_num) hInv
  · exact hC.eventually_apply_implicitFunction (by norm_num) hInv

lemma contDiffAt_Q_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.Q p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.reCLM.contDiff.contDiffAt.comp (r,θ) hcomp

lemma contDiffAt_S_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.S p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.imCLM.contDiff.contDiffAt.comp (r,θ) hcomp

/-- A smooth local angular fiber exists at every point of the upper half-disk.
This instantiates the implicit theorem with the actual power-series real part. -/
theorem exists_local_angle {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ ψ : ℝ → ℝ, ψ r = θ ∧ ContDiffAt ℝ ∞ ψ r ∧
      ∀ᶠ s in 𝓝 r, MahlerConformal.Q s (ψ s) = MahlerConformal.Q r θ := by
  apply exists_local_real_level (contDiffAt_Q_uncurry hr hr1)
    (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  exact neg_ne_zero.mpr (MahlerConformal.B_pos hr hr1 hθ hθπ).ne'

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularFibers
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

lemma fiberDomain_isOpen (q : ℝ) : IsOpen (fiberDomain q) := by
  apply isOpen_iff_mem_nhds.mpr
  intro r hr
  have hc := (hasDerivAt_radialMap hr.1 hr.2.1).continuousAt
  have hm := hc (Ioi_mem_nhds hr.2.2)
  filter_upwards [Ioo_mem_nhds hr.1 hr.2.1, hm] with s hs hms
  exact ⟨hs.1,hs.2,hms⟩

lemma fiberAngle_spec {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle q r ∈ Ioo 0 Real.pi ∧ MahlerConformal.Q r (fiberAngle q r) = q := by
  unfold fiberAngle
  rw [dite_eq_left hr]
  exact Classical.choose_spec (exists_fiberAngle hr)

/-- Local implicit angles agree with the globally chosen fiber by uniqueness.
Thus the global choice is smooth at every point of its open domain. -/
theorem contDiffAt_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ContDiffAt ℝ ∞ (fiberAngle q) r := by
  have hs := fiberAngle_spec hr
  obtain ⟨ψ,hψr,hψC,hψQ⟩ := exists_local_angle hr.1 hr.2.1 hs.1.1 hs.1.2
  have hψcont := hψC.continuousAt
  have hψrange : ∀ᶠ s in 𝓝 r, ψ s ∈ Ioo (0 : ℝ) Real.pi := by
    apply hψcont
    rw [hψr]
    exact Ioo_mem_nhds hs.1.1 hs.1.2
  apply hψC.congr_of_eventuallyEq
  filter_upwards [(fiberDomain_isOpen q).mem_nhds hr, hψrange, hψQ] with s hsd hsp hsQ
  have hg := fiberAngle_spec hsd
  have heq : MahlerConformal.Q s (fiberAngle q s) = MahlerConformal.Q s (ψ s) := by
    rw [hg.2, hsQ, hs.2]
  exact (MahlerConformal.Q_strictAntiOn hsd.1 hsd.2.1).injOn
    ⟨hg.1.1.le,hg.1.2.le⟩ ⟨hsp.1.le,hsp.2.le⟩ heq

/-- Measurability of the actual fiber angle, including its zero extension. -/
theorem measurable_fiberAngle (q : ℝ) : Measurable (fiberAngle q) := by
  classical
  have hc : ContinuousOn (fiberAngle q) (fiberDomain q) :=
    fun _ hr => (contDiffAt_fiberAngle hr).continuousAt.continuousWithinAt
  have hmeas := hc.measurable_piecewise continuous_zero.continuousOn
    (fiberDomain_isOpen q).measurableSet
  convert hmeas using 1
  ext r
  by_cases hr : r ∈ fiberDomain q
  · simp [hr]
  · simp [fiberAngle, hr]

/-- Every radius after r0 has a unique fiber angle when M(r0)=|q|. -/
theorem mem_fiberDomain_of_basepoint {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) : r ∈ fiberDomain q := by
  have hrpos : 0 < r := hr₀.trans_lt hr.1
  refine ⟨hrpos,hr.2,?_⟩
  rw [← hq]
  exact strictMonoOn_radialMap ⟨hr₀,hr.1.trans hr.2⟩ ⟨hrpos.le,hr.2⟩ hr.1

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiberHeight
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The angular function B gives the imaginary part of the rotated complex derivative. -/
theorem rotated_derivative_im {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
      Complex.exp ((θ : ℂ)*Complex.I)).im = MahlerConformal.B r θ := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by rwa [MahlerConformal.norm_polar hr.le]
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hQ := (hF.comp (θ : ℂ) (MahlerConformal.hasDerivAt_polar_complex r θ)).real_of_complex
  have hq : HasDerivAt (MahlerConformal.Q r)
      ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re θ := hQ
  have heq := hq.unique (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  have halg : ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re =
      -r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        Complex.exp ((θ : ℂ)*Complex.I)).im := by
    simp only [MahlerConformal.polar, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [halg] at heq
  linarith

/-- The actual chosen fiber has positive vertical derivative on its open domain. -/
theorem hasDerivAt_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    HasDerivAt (fiberHeight q)
      (r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r)) r := by
  have hs := fiberAngle_spec hr
  have hθ := (contDiffAt_fiberAngle hr).differentiableAt (by norm_num) |>.hasDerivAt
  have hw : ‖MahlerConformal.polar r (fiberAngle q r)‖ < 1 := by
    simpa only [MahlerConformal.norm_polar hr.1.le] using hr.2.1
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hlevel : ∀ᶠ s in 𝓝 r,
      (MahlerConformal.F (polarCurve (fiberAngle q) s)).re = q := by
    filter_upwards [(fiberDomain_isOpen q).mem_nhds hr] with s hs
    exact (fiberAngle_spec hs).2
  have hB := MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2
  have hrot := rotated_derivative_im hr.1 hr.2.1 (θ := fiberAngle q r)
  have him : 0 < ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im := by nlinarith [hr.1]
  have hv := image_polarCurve_vertical_derivative hF hθ hlevel him
  have hn : Complex.normSq ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)) =
      ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
    rw [Complex.normSq_eq_norm_sq, norm_mul]
    simp [Complex.norm_exp]
  rw [hn] at hv
  have hquot : ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
      ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
        Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im =
      r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r) := by
    rw [← hrot]
    field_simp [hr.1.ne']
  rw [hquot] at hv
  exact hv

theorem deriv_fiberHeight_pos {q r : ℝ} (hr : r ∈ fiberDomain q) :
    0 < deriv (fiberHeight q) r := by
  rw [(hasDerivAt_fiberHeight hr).deriv]
  have hs := fiberAngle_spec hr
  have hw : ‖MahlerConformal.polar r (fiberAngle q r)‖ < 1 := by
    simpa only [MahlerConformal.norm_polar hr.1.le] using hr.2.1
  exact div_pos (mul_pos hr.1 (sq_pos_of_pos (norm_pos_iff.mpr (MahlerConformal.deriv_F_ne_zero hw))))
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularIntegrals
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular integral and sine estimate. -/

noncomputable section
open Complex Set MeasureTheory
open scoped Topology
namespace MahlerConformal

lemma continuous_B (r : ℝ) : Continuous (B r) := by
  unfold B
  fun_prop

/-- Fundamental theorem of calculus for the actual angular derivative. -/
theorem integral_B {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (a b : ℝ) :
    (∫ θ in a..b, B r θ) = Q r a - Q r b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => -Q r θ) (f' := B r)
    (fun θ (_ : θ ∈ uIcc a b) => by
      convert (hasDerivAt_Q hr hr1 θ).fun_neg using 1
      simp only [neg_neg])
    (show IntervalIntegrable (B r) volume a b from (continuous_B r).intervalIntegrable a b)
  simpa only [neg_neg, neg_sub_neg] using h

/-- The normalization identity for the angular integral. -/
theorem integral_B_semicircle {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, B r θ) = 2*(F (r : ℂ)).re := by
  rw [integral_B hr hr1, Q_zero, Q_pi]
  ring

lemma arctan_le_self_nonneg {v : ℝ} (hv : 0 ≤ v) : Real.arctan v ≤ v := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hv) (Real.arctan_lt_pi_div_two v)

lemma B_le_linear {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    B r θ ≤ (8*r/(Real.pi^2*(1-r^2))) * θ := by
  have hd : 0 < 1-r^2 := by nlinarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hv : 0 ≤ 2*r*Real.sin θ/(1-r^2) := by positivity
  calc
    B r θ ≤ 4/Real.pi^2 * (2*r*Real.sin θ/(1-r^2)) :=
      mul_le_mul_of_nonneg_left (arctan_le_self_nonneg hv) (by positivity)
    _ ≤ 4/Real.pi^2 * (2*r*θ/(1-r^2)) := by
      gcongr
      exact Real.sin_le hθ.1
    _ = _ := by field_simp; ring

/-- The quadratic angular estimate, with C=4/pi². -/
theorem Q_drop_le_quadratic {r d : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : d ∈ Icc 0 Real.pi) :
    (F (r : ℂ)).re - Q r d ≤ 4*r*d^2/(Real.pi^2*(1-r^2)) := by
  let c : ℝ := 8*r/(Real.pi^2*(1-r^2))
  have hi : (∫ θ in (0 : ℝ)..d, c*θ) = c*d^2/2 := by
    have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => c*θ^2/2) (f' := fun θ => c*θ)
      (fun θ (_ : θ ∈ uIcc 0 d) => by
        convert ((hasDerivAt_pow 2 θ).const_mul c).div_const 2 using 1 <;> first | rfl | ring | (norm_num; ring))
      (show IntervalIntegrable (fun θ => c*θ) volume 0 d from
        (continuous_const.mul continuous_id).intervalIntegrable 0 d)
    simpa using ht
  have hle := intervalIntegral.integral_mono_on (μ := volume) hd.1
    ((continuous_B r).intervalIntegrable 0 d)
    ((continuous_const.mul continuous_id : Continuous (fun θ : ℝ => c*θ)).intervalIntegrable 0 d)
    (fun θ (hθ : θ ∈ Icc 0 d) => B_le_linear hr hr1 ⟨hθ.1, hθ.2.trans hd.2⟩)
  simp only [Pi.mul_apply] at hle
  rw [integral_B hr hr1, Q_zero, hi] at hle
  change (F (r : ℂ)).re - Q r d ≤ c*d^2/2 at hle
  have he : c*d^2/2 = 4*r*d^2/(Real.pi^2*(1-r^2)) := by dsimp [c]; ring
  rwa [he] at hle

/-- The reflected angle gives the sine estimate with the explicit
absolute constant c=1. This theorem is about F itself and assumes no inverse map. -/
theorem sine_bound {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Real.sqrt ((1-r^2)*((F (r : ℂ)).re - |Q r θ|)/r) ≤ Real.sin θ := by
  let d := min θ (Real.pi-θ)
  have hd0 : 0 ≤ d := le_min hθ.1 (sub_nonneg.mpr hθ.2)
  have hdπ : d ≤ Real.pi/2 := by
    dsimp [d]
    by_cases h : θ ≤ Real.pi/2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have hd : d ∈ Icc 0 Real.pi := ⟨hd0, hdπ.trans (by linarith [Real.pi_pos])⟩
  have hsin : Real.sin d = Real.sin θ := by
    dsimp [d]
    rcases le_total θ (Real.pi-θ) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.sin_pi_sub]
  have hdrop := Q_drop_le_quadratic hr hr1 hd
  rw [Q_min_angle hr hr1 hθ] at hdrop
  have hden : 0 < Real.pi^2*(1-r^2) := mul_pos (sq_pos_of_pos Real.pi_pos) (by nlinarith)
  have hsqrt : Real.sqrt ((1-r^2)*((F (r : ℂ)).re - |Q r θ|)/r) ≤ 2/Real.pi*d := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hh := (le_div_iff₀ hden).mp hdrop
    apply (div_le_iff₀ hr).mpr
    have he : (2/Real.pi*d)^2*r * Real.pi^2 = 4*r*d^2 := by field_simp; ring
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos Real.pi_pos)).mp
    nlinarith
  exact hsqrt.trans (hsin ▸ Real.mul_le_sin hd0 hdπ)

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PrimitiveBound
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- Dividing the sine lower bound yields the exact residual reciprocal estimate. -/
theorem sine_reciprocal_bound {r θ Δ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hΔ : 0 < Δ) (hsine : sqrt ((1-r^2)*Δ/r) ≤ sin θ) :
    (1-r^2)/(r*sin θ) ≤ sqrt (1-r^2)/(sqrt r*sqrt Δ) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hroot : 0 < sqrt ((1-r^2)*Δ/r) := sqrt_pos.2 (by positivity)
  have hs : 0 < sin θ := hroot.trans_le hsine
  calc
    _ ≤ (1-r^2)/(r*sqrt ((1-r^2)*Δ/r)) := by
      apply div_le_div_of_nonneg_left hden.le (by positivity)
      exact mul_le_mul_of_nonneg_left hsine hr.le
    _ = sqrt (1-r^2)/(sqrt r*sqrt Δ) := by
      rw [sqrt_div (mul_nonneg hden.le hΔ.le), sqrt_mul hden.le]
      have hr2 := sq_sqrt hr.le
      have hd2 := sq_sqrt hden.le
      field_simp
      nlinarith

/-- The reciprocal angular-speed estimate converts to the
error-integral density, with the explicit coefficient π. -/
theorem radial_primitive_density_bound {r θ Δ m : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hm : 0 ≤ m) (hΔ : 0 < Δ)
    (hsine : sqrt ((1-r^2)*Δ/r) ≤ sin θ) :
    (4*m/Real.pi)*(r^(2*m-1 : ℝ)/angularSpeed r θ) ≤
      2*m*r^(2*m-1 : ℝ) +
      Real.pi*(m*r^(2*m-3/2 : ℝ)*sqrt (1-r^2)/sqrt Δ) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hs : 0 < sin θ := (sqrt_pos.2 (show 0 < (1-r^2)*Δ/r by positivity)).trans_le hsine
  have hi := angular_speed_inverse_bound hr hr1 hs
  have hi' := sine_reciprocal_bound hr hr1 hΔ hsine
  have hrecip : 1/angularSpeed r θ ≤ Real.pi/2 +
      (Real.pi^2/4)*(sqrt (1-r^2)/(sqrt r*sqrt Δ)) := by
    have hh := mul_le_mul_of_nonneg_left hi' (show 0 ≤ Real.pi^2/4 by positivity)
    linarith
  have hpow : r^(2*m-1 : ℝ)/sqrt r = r^(2*m-3/2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_sub hr]
    congr 1
    ring
  calc
    _ = ((4*m/Real.pi)*r^(2*m-1 : ℝ))*(1/angularSpeed r θ) := by ring
    _ ≤ ((4*m/Real.pi)*r^(2*m-1 : ℝ))*(Real.pi/2 +
        (Real.pi^2/4)*(sqrt (1-r^2)/(sqrt r*sqrt Δ))) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 2*m*r^(2*m-1 : ℝ) +
        Real.pi*m*(r^(2*m-1 : ℝ)/sqrt r)*sqrt (1-r^2)/sqrt Δ := by
      field_simp
      ; ring
    _ = _ := by rw [hpow]; ring

lemma radial_error_integrable {m r₀ : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) :
    IntervalIntegrable (errorIntegrand radialMap r₀ m) volume r₀ 1 :=
  (uniform_error_bound measurable_radialMap continuousOn_radialMap
    (fun _ hr => hasDerivAt_radialMap hr.1 hr.2) hm hr₀ hr₀1).1

/-- The density is integrable through the potentially singular initial radius;
the square-root sine bound, rather than an assumed endpoint regularity, controls it. -/
theorem radial_primitive_integrable {θ : ℝ → ℝ} {m r₀ s : ℝ}
    (hθ : Measurable θ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ s) (hs1 : s < 1)
    (hsine : ∀ r ∈ Ioo r₀ 1,
      sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (θ r)) :
    IntervalIntegrable (radialPrimitiveDensity θ m) volume r₀ s := by
  have hr₀1 : r₀ < 1 := hr₀s.trans_lt hs1
  have herr := (radial_error_integrable hm hr₀ hr₀1).mono_set
    (show uIcc r₀ s ⊆ uIcc r₀ 1 by
      rw [uIcc_of_le hr₀s, uIcc_of_le hr₀1.le]
      exact Icc_subset_Icc le_rfl hs1.le)
  have hpow : IntervalIntegrable (fun r : ℝ => 2*m*r^(2*m-1 : ℝ)) volume r₀ s :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inl (by linarith))).const_mul (2*m)
  have hmajor := hpow.add (herr.const_mul Real.pi)
  have hmeas : Measurable (radialPrimitiveDensity θ m) := by
    unfold radialPrimitiveDensity angularSpeed
    fun_prop
  apply hmajor.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hr₀s] at hr
  have hrpos : 0 < r := hr₀.trans_lt hr.1
  have hr1 : r < 1 := hr.2.trans_lt hs1
  have hΔ : 0 < radialMap r-radialMap r₀ :=
    sub_pos.mpr (strictMonoOn_radialMap ⟨hr₀,hr₀1⟩ ⟨hrpos.le,hr1⟩ hr.1)
  have hs := hsine r ⟨hr.1,hr1⟩
  have hsin : 0 < sin (θ r) :=
    (sqrt_pos.2 (show 0 < (1-r^2)*(radialMap r-radialMap r₀)/r by
      have : 0 < 1-r^2 := by nlinarith
      positivity)).trans_le hs
  have hn : 0 ≤ radialPrimitiveDensity θ m r := by
    unfold radialPrimitiveDensity angularSpeed
    have : 0 < 1-r^2 := by nlinarith
    have : 0 < arctan (2*r*sin (θ r)/(1-r^2)) := arctan_pos.mpr (by positivity)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact radial_primitive_density_bound hrpos hr1 (by linarith) hΔ hs

/-- The leading term of the radial primitive integrates with coefficient exactly one. -/
theorem integral_radial_leading {m a b : ℝ} (hm : 0 < m) :
    (∫ r in a..b, 2*m*r^(2*m-1 : ℝ)) = b^(2*m : ℝ)-a^(2*m : ℝ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have he : 2*m-1+1 = 2*m := by ring
  rw [he]
  field_simp

/-- The radial primitive is bounded by s^(2m) plus π times the
uniformly controlled error. This bound does not assert equality
with the image-domain primitive. -/
theorem radial_primitive_integral_bound {θ : ℝ → ℝ} {m r₀ s : ℝ}
    (hθ : Measurable θ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ s) (hs1 : s < 1)
    (hsine : ∀ r ∈ Ioo r₀ 1,
      sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (θ r)) :
    (∫ r in r₀..s, radialPrimitiveDensity θ m r) ≤
      s^(2*m : ℝ) + Real.pi*(∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) := by
  have hr₀1 : r₀ < 1 := hr₀s.trans_lt hs1
  have herr := radial_error_integrable hm hr₀ hr₀1
  have herr' := herr.mono_set
    (show uIcc r₀ s ⊆ uIcc r₀ 1 by
      rw [uIcc_of_le hr₀s, uIcc_of_le hr₀1.le]
      exact Icc_subset_Icc le_rfl hs1.le)
  have hpow : IntervalIntegrable (fun r : ℝ => 2*m*r^(2*m-1 : ℝ)) volume r₀ s :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inl (by linarith))).const_mul (2*m)
  have hcompare : (∫ r in r₀..s, radialPrimitiveDensity θ m r) ≤
      (∫ r in r₀..s, 2*m*r^(2*m-1 : ℝ) + Real.pi*errorIntegrand radialMap r₀ m r) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr₀s
      (radial_primitive_integrable hθ hm hr₀ hr₀s hs1 hsine) (hpow.add (herr'.const_mul Real.pi))
    intro r hr
    have hrpos : 0 < r := hr₀.trans_lt hr.1
    have hr1 : r < 1 := hr.2.trans hs1
    have hΔ : 0 < radialMap r-radialMap r₀ :=
      sub_pos.mpr (strictMonoOn_radialMap ⟨hr₀,hr₀1⟩ ⟨hrpos.le,hr1⟩ hr.1)
    exact radial_primitive_density_bound hrpos hr1 (by linarith) hΔ (hsine r ⟨hr.1,hr1⟩)
  rw [intervalIntegral.integral_add hpow (herr'.const_mul Real.pi),
    integral_radial_leading (show 0 < m by linarith), intervalIntegral.integral_const_mul] at hcompare
  have herrmono : (∫ r in r₀..s, errorIntegrand radialMap r₀ m r) ≤
      (∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) := by
    apply intervalIntegral.integral_mono_interval le_rfl hr₀s hs1.le _ herr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    unfold errorIntegrand
    have hrpos : 0 ≤ r := hr₀.trans hr.1.le
    positivity
  have hnonneg : 0 ≤ r₀^(2*m : ℝ) := rpow_nonneg hr₀ _
  nlinarith [mul_le_mul_of_nonneg_left herrmono Real.pi_pos.le]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiberPrimitive
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- The actual chosen angular fiber satisfies the singular sine estimate. -/
theorem fiberAngle_sine_bound {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (fiberAngle q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hs := fiberAngle_spec hmem
  have h := MahlerConformal.sine_bound hmem.1 hmem.2.1 ⟨hs.1.1.le,hs.1.2.le⟩
  rw [hs.2, ← hq] at h
  exact h

lemma planarError_nonneg (m : ℝ) : 0 ≤ planarError m := le_max_left _ _

/-- The actual radial primitive obeys the concrete error bound for every m≥2,
not only eventually large m. -/
theorem fiber_primitive_bound {q r₀ m s : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hs : s ∈ Ico r₀ 1) :
    (∫ r in r₀..s, radialPrimitiveDensity (fiberAngle q) m r) ≤ s^(2*m : ℝ)+planarError m := by
  have hp := radial_primitive_integral_bound (measurable_fiberAngle q) hm hr₀ hs.1 hs.2
    (fun r hr => fiberAngle_sine_bound hr₀ hq hr)
  have he := (uniform_error_bound measurable_radialMap continuousOn_radialMap
    (fun _ hr => hasDerivAt_radialMap hr.1 hr.2) hm hr₀ (hs.1.trans_lt hs.2)).2
  have he' := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hmax : Real.pi*errorEnvelope m ≤ planarError m := le_max_right _ _
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RadialPrimitiveDeriv
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

lemma continuousAt_radialPrimitiveDensity {q m r : ℝ} (hr : r ∈ fiberDomain q) :
    ContinuousAt (radialPrimitiveDensity (fiberAngle q) m) r := by
  have hθ := (contDiffAt_fiberAngle hr).continuousAt
  have hs := fiberAngle_spec hr
  have hrpos : 0 < r := hr.1
  have hden : 1-r^2 ≠ 0 := ne_of_gt (by nlinarith [hr.2.1])
  have hB : angularSpeed r (fiberAngle q r) ≠ 0 :=
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2).ne'
  have hbcont : ContinuousAt (fun t => angularSpeed t (fiberAngle q t)) r := by
    unfold angularSpeed
    fun_prop
  unfold radialPrimitiveDensity
  exact continuousAt_const.mul ((Real.continuousAt_rpow_const r (2*m-1) (Or.inl hrpos.ne')).div hbcont hB)

lemma measurable_radialPrimitiveDensity (q m : ℝ) :
    Measurable (radialPrimitiveDensity (fiberAngle q) m) := by
  have hθ := measurable_fiberAngle q
  unfold radialPrimitiveDensity angularSpeed
  fun_prop

/-- The radial primitive has its defining density as derivative, including
an integrable singular lower endpoint. -/
theorem hasDerivAt_radialPrimitive {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (radialPrimitive q r₀ m)
      (radialPrimitiveDensity (fiberAngle q) m r) r := by
  have hi := radial_primitive_integrable (measurable_fiberAngle q) hm hr₀ hr.1.le hr.2
    (fun s hs => fiberAngle_sine_bound hr₀ hq hs)
  exact intervalIntegral.integral_hasDerivAt_right hi
    (measurable_radialPrimitiveDensity q m).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_radialPrimitiveDensity (mem_fiberDomain_of_basepoint hr₀ hq hr))

/-- Dividing radial density by vertical speed gives the prescribed vertical
derivative. -/
theorem radial_density_div_vertical_speed {q r m : ℝ} (hr : r ∈ fiberDomain q) :
    radialPrimitiveDensity (fiberAngle q) m r / deriv (fiberHeight q) r =
      (4*m/Real.pi)*r^(2*m-2 : ℝ) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
  have hs := fiberAngle_spec hr
  have hB : MahlerConformal.B r (fiberAngle q r) ≠ 0 :=
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2).ne'
  have hrne : r ≠ 0 := hr.1.ne'
  have hp : r^(2*m-1 : ℝ)/r = r^(2*m-2 : ℝ) := by
    rw [← rpow_sub_one hrne]
    congr 1
    ring
  rw [(hasDerivAt_fiberHeight hr).deriv]
  change ((4*m/Real.pi)*(r^(2*m-1 : ℝ)/MahlerConformal.B r (fiberAngle q r))) /
      (r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r)) = _
  calc
    _ = (4*m/Real.pi)*(r^(2*m-1 : ℝ)/r) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
      field_simp
    _ = _ := by rw [hp]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularEndpoint
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-convergence normalization M(r) → 1. -/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
namespace MahlerConformal

lemma eventually_radius : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one

lemma B_nonneg {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) : 0 ≤ B r θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hd : 0 < 1-r^2 := by nlinarith
  unfold B
  apply mul_nonneg (by positivity)
  apply Real.arctan_nonneg.mpr
  positivity

/-- Pointwise interior-angle limit; the endpoint angles are intentionally excluded. -/
theorem B_tendsto_one {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun r => B r θ) (𝓝[<] 1) (𝓝 (2/Real.pi)) := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hd0 : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hid.pow 2)
  have hd : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd0, ?_⟩
    filter_upwards [eventually_radius] with r hr
    change 0 < 1-r^2
    nlinarith [hr.1, hr.2]
  have hn : Tendsto (fun r : ℝ => 2*r*Real.sin θ) (𝓝[<] 1) (𝓝 (2*Real.sin θ)) := by
    simpa using (tendsto_const_nhds.mul hid).mul_const (Real.sin θ)
  have hv : Tendsto (fun r : ℝ => 2*r*Real.sin θ/(1-r^2)) (𝓝[<] 1) atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hn.pos_mul_atTop
      (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
      hd.inv_tendsto_nhdsGT_zero
  have ha := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hv).const_mul
    (4/Real.pi^2)
  have he : 4/Real.pi^2*(Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he, Function.comp_apply] using ha

/-- Bounded convergence applied to the actual angular speed of F. -/
theorem integral_B_tendsto_one :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..Real.pi, B r θ) (𝓝[<] 1) (𝓝 2) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := Real.pi) (F := B) (f := fun _ => 2/Real.pi)
    (fun _ => 2/Real.pi)
    (Filter.Eventually.of_forall fun r => (continuous_B r).aestronglyMeasurable)
    (by
      filter_upwards [eventually_radius] with r hr
      exact Filter.Eventually.of_forall fun θ hθ => by
        rw [uIoc_of_le Real.pi_pos.le] at hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (B_nonneg hr.1 hr.2 ⟨hθ.1.le, hθ.2⟩)]
        exact (B_lt_two_div_pi r θ).le)
    (intervalIntegrable_const)
    (by
      filter_upwards [(Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := Real.pi))] with θ heq
      intro hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hi : θ ∈ Ioo (0 : ℝ) Real.pi := heq.mpr hθ
      exact B_tendsto_one hi.1 hi.2)
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rwa [he] at ht

/-- The real part of M(r)=F(r) tends to 1.
No radial derivative or assumed endpoint normalization is used. -/
theorem F_real_tendsto_one :
    Tendsto (fun r : ℝ => (F (r : ℂ)).re) (𝓝[<] 1) (𝓝 1) := by
  have ht := integral_B_tendsto_one.div_const 2
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (∫ θ in (0 : ℝ)..Real.pi, B r θ)/2 = (F (r : ℂ)).re := by
    filter_upwards [eventually_radius] with r hr
    rw [integral_B_semicircle hr.1 hr.2]
    ring
  simpa using ht.congr' he

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularStrip
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-part image and real preimages of the conformal map. -/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
namespace MahlerConformal

lemma F_real_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : (F (r : ℂ)).re < 1 := by
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := B r) (g := fun _ => 2/Real.pi) Real.pi_pos (continuous_B r).continuousOn
    continuous_const.continuousOn (fun θ _ => (B_lt_two_div_pi r θ).le)
    ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, B_lt_two_div_pi r 0⟩
  rw [integral_B_semicircle hr hr1] at hi
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rw [he] at hi
  linarith

lemma polar_neg_angle (r θ : ℝ) : polar r (-θ) = starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_neg, Real.sin_neg]

lemma Q_neg_angle (r θ : ℝ) : Q r (-θ) = Q r θ := by
  simp only [Q, polar_neg_angle, F_conj, Complex.conj_re]

lemma Q_mem_Icc {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Q r θ ∈ Icc (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := (Q_strictAntiOn hr hr1).antitoneOn
  exact ⟨by simpa only [Q_pi] using ha hθ ⟨Real.pi_pos.le, le_rfl⟩ hθ.2,
    by simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ hθ hθ.1⟩

/-- Every image point has real part in the strip. -/
theorem F_re_mem_strip {w : ℂ} (hw : ‖w‖ < 1) : (F w).re ∈ Ioo (-1 : ℝ) 1 := by
  by_cases hw0 : w = 0
  · simp [hw0, F_zero]
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hp : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
  have hθ : |w.arg| ∈ Icc (0 : ℝ) Real.pi := by
    refine ⟨abs_nonneg _, abs_le.mpr ⟨?_, Complex.arg_le_pi w⟩⟩
    exact (Complex.neg_pi_lt_arg w).le
  have he : Q ‖w‖ |w.arg| = (F w).re := by
    rcases le_total 0 w.arg with h | h
    · rw [abs_of_nonneg h, Q, hp]
    · rw [abs_of_nonpos h, Q_neg_angle, Q, hp]
  have hb := Q_mem_Icc hr hw hθ
  rw [he] at hb
  have hm := F_real_lt_one hr hw
  constructor <;> linarith [hb.1, hb.2]

lemma continuousOn_F_real {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun t : ℝ => (F (t : ℂ)).re) (Icc 0 r) := by
  intro t ht
  have hw : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  exact (hasDerivAt_F_series hw).real_of_complex.continuousAt.continuousWithinAt

/-- Every point on the real interval (-1,1) is the actual value F(t) at a real
point t in the disk. This is existence only; it does not assert univalence. -/
theorem exists_real_preimage {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ t : ℝ, t ∈ Ioo (-1 : ℝ) 1 ∧ F (t : ℂ) = (q : ℂ) := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1], hq.2⟩
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 ∧ |q| < (F (r : ℂ)).re :=
    eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r, hr, hqr⟩ := he.exists
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  have hF : F (t : ℂ) = ((|q| : ℝ) : ℂ) := by
    apply Complex.ext
    · exact hte
    · simpa using F_real_im t
  by_cases hq0 : 0 ≤ q
  · refine ⟨t, ⟨by linarith [ht.1], ht.2.trans_lt hr.2⟩, ?_⟩
    simpa only [abs_of_nonneg hq0] using hF
  · refine ⟨-t, ⟨by linarith [ht.2, hr.2], by linarith [ht.1]⟩, ?_⟩
    rw [Complex.ofReal_neg, F_odd, hF, abs_of_neg (lt_of_not_ge hq0)]
    simp

/-- The set of real parts of the image is exactly (-1,1).
This does not assert that each vertical fiber is an interval. -/
theorem image_re_F_disk : Complex.re '' (F '' ball (0 : ℂ) 1) = Ioo (-1 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact F_re_mem_strip (by simpa using hw)
  · intro hq
    obtain ⟨t, ht, hF⟩ := exists_real_preimage hq
    refine ⟨(q : ℂ), ⟨(t : ℂ), ?_, hF⟩, by simp⟩
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalInjectivity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma norm_add_sub_sq (w : ℂ) : ‖1+w‖^2 - ‖1-w‖^2 = 4*w.re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

lemma re_mul_log_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hx : w.re ≠ 0) :
    0 < w.re * (Complex.log (cayley w)).re := by
  have hnum : 0 < ‖1+w‖ := norm_pos_iff.mpr (one_add_ne hw)
  have hden : 0 < ‖1-w‖ := norm_pos_iff.mpr (one_sub_ne hw)
  have hn := norm_add_sub_sq w
  rw [Complex.log_re, cayley, norm_div]
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hc : ‖1+w‖/‖1-w‖ < 1 := (div_lt_one hden).mpr (by nlinarith)
    exact mul_pos_of_neg_of_neg hx (Real.log_neg (div_pos hnum hden) hc)
  · have hc : 1 < ‖1+w‖/‖1-w‖ := (one_lt_div hden).mpr (by nlinarith)
    exact mul_pos hx (Real.log_pos hc)

lemma re_mul_log_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.re * (Complex.log (cayley w)).re := by
  by_cases hx : w.re = 0
  · simp [hx]
  · exact (re_mul_log_cayley_pos hw hx).le

lemma im_mul_arg_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hy : w.im ≠ 0) :
    0 < w.im * (cayley w).arg := by
  have hd : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rw [arg_eq_arctan_of_re_pos (cayley_re_pos hw), cayley_im_div_re hw]
  rcases lt_or_gt_of_ne hy with hy | hy
  · exact mul_pos_of_neg_of_neg hy
      (Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hd))
  · exact mul_pos hy (Real.arctan_pos.mpr (div_pos (by linarith) hd))

lemma im_mul_arg_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.im * (cayley w).arg := by
  by_cases hy : w.im = 0
  · simp [hy]
  · exact (im_mul_arg_cayley_pos hw hy).le

/-- A consequence of the derivative formula on the full disk, used for injectivity.
This is not a formula for M'(r), nor does it assume univalence. -/
theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  have hc : (4/(Real.pi : ℂ)^2) = ((4/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    have he : (8/(Real.pi : ℂ)^2) = ((8/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.ofReal_re]
    positivity
  have he : deriv F w = (4/(Real.pi : ℂ)^2)*(Complex.log (cayley w)/w) := by
    rw [(hasDerivAt_F_log hw hw0).deriv]
    dsimp [cayley]
    field_simp
  rw [he, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_pos (by positivity)
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hx := re_mul_log_cayley_nonneg hw
  have hy := im_mul_arg_cayley_nonneg hw
  rw [Complex.log_im]
  by_cases hx0 : w.re = 0
  · have hy0 : w.im ≠ 0 := by
      intro hy0
      apply hw0
      apply Complex.ext <;> simp [hx0, hy0]
    have hp := im_mul_arg_cayley_pos hw hy0
    nlinarith
  · have hp := re_mul_log_cayley_pos hw hx0
    nlinarith

lemma segment_mem_disk {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖a+(t : ℂ)*(b-a)‖ < 1 := by
  have hc := (convex_ball (0 : ℂ) (1 : ℝ)) (by simpa using ha) (by simpa using hb)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have he : (1-t) • a + t • b = a+(t : ℂ)*(b-a) := by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he] at hc
  simpa using hc

/-- Injectivity on the exact open unit disk, with no assumed inverse or central
univalence theorem. Positive real derivative makes the segment projection strict. -/
theorem F_injOn_disk : Set.InjOn F (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  by_contra hne
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hb' : ‖b‖ < 1 := by simpa using hb
  have hd : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g : ℝ → ℝ := fun t => (F (a+(t : ℂ)*(b-a))/(b-a)).re
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (deriv F (a+(t : ℂ)*(b-a))).re t := by
    intro t ht
    have hw := segment_mem_disk ha' hb' ht
    have hf := (hasDerivAt_F_series hw).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun z : ℂ => a+z*(b-a)) (b-a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a
    have hs := ((hf.comp (t : ℂ) hline).div_const (b-a)).real_of_complex
    have he : (deriv F (a+(t : ℂ)*(b-a))*(b-a))/(b-a) =
        deriv F (a+(t : ℂ)*(b-a)) := mul_div_cancel_right₀ _ hd
    change HasDerivAt g _ t at hs
    rwa [he] at hs
  have hm : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hg t ht').deriv]
    exact deriv_F_re_pos (segment_mem_disk ha' hb' ht')
  have hlt := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  dsimp [g] at hlt
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at hlt
  rw [hab] at hlt
  exact lt_irrefl _ hlt

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalInverse
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The biholomorphic map and its inverse.
The vertical interval property and P_m estimates are not asserted here. -/

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace MahlerConformal

lemma inverseF_mem {u : ℂ} (hu : u ∈ Omega) : inverseF u ∈ ball (0 : ℂ) 1 :=
  Function.invFunOn_mem hu

lemma inverseF_right {u : ℂ} (hu : u ∈ Omega) : F (inverseF u) = u :=
  Function.invFunOn_eq hu

lemma inverseF_left {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : inverseF (F w) = w :=
  F_injOn_disk.leftInvOn_invFunOn hw

lemma hasStrictDerivAt_F {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasStrictDerivAt F (deriv F w) w :=
  ((differentiableOn_F.analyticAt (isOpen_ball.mem_nhds hw)).contDiffAt (n := 1)).hasStrictDerivAt
    (by norm_num)

theorem isOpen_Omega : IsOpen Omega := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨w, hw, rfl⟩
  rw [← (hasStrictDerivAt_F hw).map_nhds_eq (deriv_F_ne_zero (by simpa using hw))]
  change F ⁻¹' Omega ∈ 𝓝 w
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hw)
  intro z hz
  exact ⟨z, hz, rfl⟩

/-- The selected inverse is holomorphic on its exact image domain, with the
reciprocal derivative. Its local inverse hypotheses follow from proved injectivity. -/
theorem hasDerivAt_inverseF {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt inverseF (deriv F (inverseF u))⁻¹ u := by
  have hw := inverseF_mem hu
  have hl : ∀ᶠ w in 𝓝 (inverseF u), inverseF (F w) = w := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w hw
    exact inverseF_left hw
  have hd := (hasStrictDerivAt_F hw).to_local_left_inverse
    (deriv_F_ne_zero (by simpa using hw)) hl
  rw [inverseF_right hu] at hd
  exact hd.hasDerivAt

theorem differentiableOn_inverseF : DifferentiableOn ℂ inverseF Omega :=
  fun _ hu => (hasDerivAt_inverseF hu).differentiableAt.differentiableWithinAt

theorem Omega_conj {u : ℂ} (hu : u ∈ Omega) : starRingEnd ℂ u ∈ Omega := by
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa using hw

theorem inverseF_conj {u : ℂ} (hu : u ∈ Omega) :
    inverseF (starRingEnd ℂ u) = starRingEnd ℂ (inverseF u) := by
  apply F_injOn_disk (inverseF_mem (Omega_conj hu)) (by simpa using inverseF_mem hu)
  rw [inverseF_right (Omega_conj hu), F_conj, inverseF_right hu]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_VerticalRadius
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical geometry of the actual inverse. The squared inverse radius has
positive vertical derivative on the image of the upper half-disk. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma hasDerivAt_normSq {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => Complex.normSq (f x))
      (2*((f t).re*f'.re+(f t).im*f'.im)) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hre.mul hre).add (him.mul him) using 1 <;> (try rfl)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_apply]
  ring

lemma im_polar_mul_deriv_F {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (polar r θ * deriv F (polar r θ)).im = B r θ := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  rw [(hasDerivAt_F_log hw (polar_ne_zero hr θ)).deriv]
  have he : polar r θ * (4/((Real.pi : ℂ)^2*polar r θ)*Complex.log (cayley (polar r θ))) =
      ((4/Real.pi^2 : ℝ) : ℂ)*Complex.log (cayley (polar r θ)) := by
    push_cast
    field_simp [polar_ne_zero hr θ]
  change (polar r θ * (4/((Real.pi : ℂ)^2*polar r θ)*Complex.log (cayley (polar r θ)))).im = _
  rw [he, Complex.im_ofReal_mul, Complex.log_im, arg_cayley_polar hr hr1]
  rfl

/-- Differentiation in the actual vertical coordinate of Omega. -/
theorem hasDerivAt_verticalRadiusSq {q ξ : ℝ} (hu : (q : ℂ)+ξ*I ∈ Omega) :
    HasDerivAt (verticalRadiusSq q)
      (2*(inverseF ((q : ℂ)+ξ*I)*deriv F (inverseF ((q : ℂ)+ξ*I))).im /
        ‖deriv F (inverseF ((q : ℂ)+ξ*I))‖^2) ξ := by
  let w := inverseF ((q : ℂ)+ξ*I)
  let d := deriv F w
  have hl : HasDerivAt (fun z : ℂ => (q : ℂ)+z*I) I (ξ : ℂ) := by
    simpa using ((hasDerivAt_id (ξ : ℂ)).mul_const I).const_add (q : ℂ)
  have hf := ((hasDerivAt_inverseF hu).comp (ξ : ℂ) hl).comp_ofReal
  have hd : d⁻¹*I = I/d := by ring
  change HasDerivAt (fun t : ℝ => inverseF ((q : ℂ)+t*I)) (d⁻¹*I) ξ at hf
  rw [hd] at hf
  have hn := hasDerivAt_normSq hf
  change HasDerivAt (verticalRadiusSq q) (2*(w.re*(I/d).re+w.im*(I/d).im)) ξ at hn
  have he : 2*(w.re*(I/d).re+w.im*(I/d).im) = 2*(w*d).im/‖d‖^2 := by
    simp only [Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_div, zero_add, sub_zero, Complex.mul_im,
      Complex.normSq_eq_norm_sq]
    ring
  rwa [he] at hn

lemma Q_add_S_I (r θ : ℝ) : (Q r θ : ℂ)+(S r θ : ℂ)*I = F (polar r θ) := by
  exact Complex.re_add_im _

/-- At each upper-semicircle image point, the inverse radius increases vertically.
This is the inverse differential form of the vertical-speed identity. -/
theorem hasDerivAt_verticalRadiusSq_polar {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (verticalRadiusSq (Q r θ))
      (2*B r θ/‖deriv F (polar r θ)‖^2) (S r θ) := by
  have hw : polar r θ ∈ ball (0 : ℂ) 1 := by simpa [norm_polar hr.le] using hr1
  have hu : (Q r θ : ℂ)+(S r θ : ℂ)*I ∈ Omega := by
    rw [Q_add_S_I]
    exact ⟨polar r θ, hw, rfl⟩
  have hd := hasDerivAt_verticalRadiusSq hu
  rw [Q_add_S_I, inverseF_left hw, im_polar_mul_deriv_F hr hr1] at hd
  exact hd

theorem verticalRadiusSq_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    verticalRadiusSq (Q r θ) (S r θ) = r^2 := by
  unfold verticalRadiusSq
  rw [Q_add_S_I, inverseF_left (by simpa [norm_polar hr.le] using hr1),
    Complex.normSq_eq_norm_sq, norm_polar hr.le]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ActualVerticalPrimitive
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

lemma sqrt_verticalRadiusSq (q t : ℝ) :
    Real.sqrt (MahlerConformal.verticalRadiusSq q t) = verticalRadius q t := by
  unfold MahlerConformal.verticalRadiusSq verticalRadius
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem verticalRadius_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    verticalRadius (MahlerConformal.Q r θ) (MahlerConformal.S r θ) = r := by
  rw [← sqrt_verticalRadiusSq, MahlerConformal.verticalRadiusSq_polar hr hr1,
    Real.sqrt_sq hr.le]

theorem hasDerivAt_verticalRadius_polar {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (verticalRadius (MahlerConformal.Q r θ))
      (MahlerConformal.B r θ/(r*‖deriv MahlerConformal.F (MahlerConformal.polar r θ)‖^2))
      (MahlerConformal.S r θ) := by
  have hv := MahlerConformal.verticalRadiusSq_polar hr hr1 θ
  have hnonzero : MahlerConformal.verticalRadiusSq (MahlerConformal.Q r θ)
      (MahlerConformal.S r θ) ≠ 0 := by rw [hv]; positivity
  have h := (MahlerConformal.hasDerivAt_verticalRadiusSq_polar hr hr1).sqrt hnonzero
  simp only [sqrt_verticalRadiusSq, verticalRadius_polar hr hr1] at h
  convert h using 1
  field_simp

theorem verticalRadius_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    verticalRadius q (fiberHeight q r) = r := by
  have hs := fiberAngle_spec hr
  have h := verticalRadius_polar hr.1 hr.2.1 (fiberAngle q r)
  rw [hs.2] at h
  exact h

theorem hasDerivAt_verticalRadius_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    HasDerivAt (verticalRadius q) (deriv (fiberHeight q) r)⁻¹ (fiberHeight q r) := by
  have hs := fiberAngle_spec hr
  have h := hasDerivAt_verticalRadius_polar hr.1 hr.2.1 (θ := fiberAngle q r)
  rw [hs.2] at h
  rw [(hasDerivAt_fiberHeight hr).deriv, inv_div]
  exact h

/-- Composition with the actual inverse radius has the prescribed vertical
primitive derivative, before taking the endpoint limit and global integral. -/
theorem hasDerivAt_actual_vertical_primitive {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ m (verticalRadius q t))
      ((4*m/Real.pi)*r^(2*m-2 : ℝ) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2)
      (fiberHeight q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hρ := hasDerivAt_verticalRadius_fiber hmem
  have hP := hasDerivAt_radialPrimitive hm hr₀ hq hr
  have h := hP.comp_of_eq (fiberHeight q r) hρ (verticalRadius_fiber hmem).symm
  have hquot := radial_density_div_vertical_speed (m := m) hmem
  simpa only [Function.comp_def, ← div_eq_mul_inv, hquot] using h

lemma fiber_image_eq {q r : ℝ} (hr : r ∈ fiberDomain q) :
    (q : ℂ)+(fiberHeight q r : ℂ)*Complex.I =
      MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)) := by
  have h := MahlerConformal.Q_add_S_I r (fiberAngle q r)
  rw [(fiberAngle_spec hr).2] at h
  exact h

lemma fiber_image_mem {q r : ℝ} (hr : r ∈ fiberDomain q) :
    (q : ℂ)+(fiberHeight q r : ℂ)*Complex.I ∈ MahlerConformal.Omega := by
  rw [fiber_image_eq hr]
  refine ⟨MahlerConformal.polar r (fiberAngle q r), ?_, rfl⟩
  simpa [MahlerConformal.norm_polar hr.1.le] using hr.2.1

lemma inverseF_fiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I) =
      MahlerConformal.polar r (fiberAngle q r) := by
  rw [fiber_image_eq hr]
  apply MahlerConformal.inverseF_left
  simpa [MahlerConformal.norm_polar hr.1.le] using hr.2.1

/-- The derivative along the upper fiber, with h and h'
being the constructed holomorphic inverse and its derivative. -/
theorem actual_vertical_primitive_derivative {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ m (verticalRadius q t))
      ((4*m/Real.pi)*
        ‖MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)‖^(2*m-2 : ℝ)*
        ‖deriv MahlerConformal.inverseF ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)‖^2)
      (fiberHeight q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have h := hasDerivAt_actual_vertical_primitive hm hr₀ hq hr
  rw [(MahlerConformal.hasDerivAt_inverseF (fiber_image_mem hmem)).deriv,
    inverseF_fiber hmem, MahlerConformal.norm_polar hmem.1.le, norm_inv, inv_pow]
  simpa only [div_eq_mul_inv] using h

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarDensity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

lemma contDiffAt_normSq_comp {f : ℂ → ℂ} {u : ℂ}
    (hf : ContDiffAt ℝ ∞ f u) : ContDiffAt ℝ ∞ (fun z => Complex.normSq (f z)) u := by
  have hre := Complex.reCLM.contDiff.contDiffAt.comp u hf
  have him := Complex.imCLM.contDiff.contDiffAt.comp u hf
  convert (hre.mul hre).add (him.mul him) using 1 <;> first | rfl | (funext z; simp [Complex.normSq_apply])

/-- Smoothness of the actual vertical density, including at the origin. -/
theorem contDiffAt_planarDensity (m : ℕ) {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    ContDiffAt ℝ ∞ (planarDensity m) u := by
  have hA := MahlerConformal.differentiableOn_inverseF.analyticAt
    (MahlerConformal.isOpen_Omega.mem_nhds hu)
  have hh : ContDiffAt ℝ ∞ MahlerConformal.inverseF u := hA.contDiffAt.restrict_scalars ℝ
  have hhd : ContDiffAt ℝ ∞ (deriv MahlerConformal.inverseF) u := hA.deriv.contDiffAt.restrict_scalars ℝ
  exact (contDiffAt_const.mul ((contDiffAt_normSq_comp hh).pow (m-1))).mul
    (contDiffAt_normSq_comp hhd)

lemma planarDensity_nonneg (m : ℕ) (u : ℂ) : 0 ≤ planarDensity m u := by
  have hh := Complex.normSq_nonneg (MahlerConformal.inverseF u)
  have hd := Complex.normSq_nonneg (deriv MahlerConformal.inverseF u)
  unfold planarDensity
  positivity

lemma continuousAt_planarDensity_vertical (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    ContinuousAt (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) t := by
  have hl : ContinuousAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) t := by fun_prop
  have hd := (contDiffAt_planarDensity m hu).continuousAt
  have hc := hd.comp (f := fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) hl
  exact hc

/-- The fundamental theorem yields the vertical derivative whenever
the segment from zero lies in Omega.
Segment containment is an explicit geometric premise. -/
theorem hasDerivAt_planarPrimitive (m : ℕ) {q t : ℝ}
    (hseg : ∀ s ∈ uIcc (0 : ℝ) t, (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    HasDerivAt (planarPrimitive m q) (planarDensity m ((q : ℂ)+(t : ℂ)*Complex.I)) t := by
  have hi : IntervalIntegrable (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact (continuousAt_planarDensity_vertical m (hseg s hs)).continuousWithinAt
  have hopen : IsOpen {s : ℝ | (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega} :=
    MahlerConformal.isOpen_Omega.preimage
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hmeas := ContinuousAt.stronglyMeasurableAtFilter (μ := volume) hopen
    (fun s hs => continuousAt_planarDensity_vertical m hs) t (hseg t (right_mem_uIcc))
  exact intervalIntegral.integral_hasDerivAt_right hi hmeas
    (continuousAt_planarDensity_vertical m (hseg t (right_mem_uIcc)))

/-- The polynomial expression equals the norm-power density. -/
theorem planarDensity_eq (m : ℕ) (hm : 1 ≤ m) (u : ℂ) :
    planarDensity m u = (4*(m : ℝ)/Real.pi)*
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ)*
      ‖deriv MahlerConformal.inverseF u‖^2 := by
  have he : ((2*(m-1) : ℕ) : ℝ) = 2*(m : ℝ)-2 := by
    rw [Nat.cast_mul, Nat.cast_sub hm]
    norm_num
    ; ring
  have hp : ‖MahlerConformal.inverseF u‖^(2*(m-1) : ℕ) =
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ) := by
    rw [← Real.rpow_natCast, he]
  unfold planarDensity
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← pow_mul, hp]

/-- Both the radial inverse-coordinate primitive and the original vertical
integral have the same density on each upper fiber. -/
theorem hasDerivAt_actual_primitive_density {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ (m : ℝ) (verticalRadius q t))
      (planarDensity m ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)) (fiberHeight q r) := by
  rw [planarDensity_eq m (by omega)]
  exact actual_vertical_primitive_derivative (by exact_mod_cast hm) hr₀ hq hr

lemma planarPrimitive_zero (m : ℕ) (q : ℝ) : planarPrimitive m q 0 = 0 := by
  simp [planarPrimitive]

lemma planarPrimitive_nonneg (m : ℕ) (q : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ planarPrimitive m q t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _s => planarDensity_nonneg m _)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarSymmetry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

lemma inverseF_deriv_conj {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    deriv MahlerConformal.inverseF (starRingEnd ℂ u) =
      starRingEnd ℂ (deriv MahlerConformal.inverseF u) := by
  have h := ((MahlerConformal.hasDerivAt_inverseF hu).differentiableAt.hasDerivAt).conj_conj
  have hd : HasDerivAt MahlerConformal.inverseF
      (starRingEnd ℂ (deriv MahlerConformal.inverseF u)) (starRingEnd ℂ u) := by
    apply h.congr_of_eventuallyEq
    filter_upwards [MahlerConformal.isOpen_Omega.mem_nhds (MahlerConformal.Omega_conj hu)] with v hv
    change MahlerConformal.inverseF v = starRingEnd ℂ (MahlerConformal.inverseF (starRingEnd ℂ v))
    rw [MahlerConformal.inverseF_conj hv]
    simp
  exact hd.deriv

lemma planarDensity_conj (m : ℕ) {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    planarDensity m (starRingEnd ℂ u) = planarDensity m u := by
  unfold planarDensity
  rw [MahlerConformal.inverseF_conj hu, inverseF_deriv_conj hu]
  simp

/-- Conjugation changes the sign of the original vertical primitive. -/
theorem planarPrimitive_neg (m : ℕ) {q t : ℝ}
    (hseg : ∀ s ∈ uIcc (0 : ℝ) t, (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    planarPrimitive m q (-t) = -planarPrimitive m q t := by
  have heq : (∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+((-s : ℝ) : ℂ)*Complex.I)) =
      planarPrimitive m q t := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hc : (q : ℂ)+((-s : ℝ) : ℂ)*Complex.I =
        starRingEnd ℂ ((q : ℂ)+(s : ℂ)*Complex.I) := by simp
    dsimp only
    rw [hc]
    exact planarDensity_conj m (hseg s hs)
  have hchange : (∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+((-s : ℝ) : ℂ)*Complex.I)) =
      -planarPrimitive m q (-t) := by
    change (∫ s in (0 : ℝ)..t, (fun x : ℝ => planarDensity m ((q : ℂ)+(x : ℂ)*Complex.I)) (-s)) = _
    have hc := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => planarDensity m ((q : ℂ)+(x : ℂ)*Complex.I)) (a := 0) (b := t)
    calc
      _ = ∫ s in (-t)..(0 : ℝ), planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
        simpa only [neg_zero] using hc
      _ = _ := intervalIntegral.integral_symm 0 (-t)
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiberEndpoint
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoints of the selected global angular fibers. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma eventually_fiberDomain {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ∀ᶠ r in 𝓝[>] r₀, r ∈ fiberDomain q := by
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hr₁).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  exact mem_fiberDomain_of_basepoint hr₀ hq ⟨hr,hr1⟩

lemma fiberAngle_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle (-q) r = Real.pi - fiberAngle q r := by
  have hn : r ∈ fiberDomain (-q) := by simpa [fiberDomain, abs_neg] using hr
  have hs := fiberAngle_spec hr
  have ht := fiberAngle_spec hn
  apply (Q_strictAntiOn hr.1 hr.2.1).injOn ⟨ht.1.1.le,ht.1.2.le⟩
    ⟨by linarith [hs.1.2],by linarith [hs.1.1]⟩
  rw [ht.2, Q_pi_sub, hs.2]

lemma fiberHeight_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight (-q) r = fiberHeight q r := by
  rw [fiberHeight, fiberAngle_neg hr]
  simp only [S, polar_pi_sub, F_odd, F_conj, Complex.neg_im, Complex.conj_im, neg_neg,
    fiberHeight]

/-- On the actual selected angle, the positive real basepoint has angle limit zero. -/
theorem fiberAngle_tendsto_zero {q r₀ : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hq0 : 0 ≤ q) (hq : radialMap r₀ = |q|) :
    Tendsto (fiberAngle q) (𝓝[>] r₀) (𝓝 0) := by
  have hd := eventually_fiberDomain hr₀.le hr₁ hq
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hd] with r hr
    exact ha.trans (fiberAngle_spec hr).1.1
  · intro b hb
    let t := min (b/2) (Real.pi/2)
    have ht : 0 < t := lt_min (by linarith) Real.pi_div_two_pos
    have htπ : t < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    have htb : t < b := (min_le_left _ _).trans_lt (by linarith)
    have hQ : Q r₀ t < q := by
      have h := Q_strictAntiOn hr₀ hr₁
        (show 0 ∈ Icc (0 : ℝ) Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.le,htπ.le⟩ ht
      rw [Q_zero] at h
      change Q r₀ t < radialMap r₀ at h
      simpa only [hq, abs_of_nonneg hq0] using h
    have hc : ContinuousAt (fun r : ℝ => Q r t) r₀ := by
      have hp : ContinuousAt (fun r : ℝ => polar r t) r₀ := by
        unfold polar
        fun_prop
      have hf := (hasDerivAt_F_series (w := polar r₀ t)
        (by rwa [norm_polar hr₀.le])).continuousAt
      exact Complex.continuous_re.continuousAt.comp (hf.comp (f := fun r : ℝ => polar r t) hp)
    have he : ∀ᶠ r in 𝓝[>] r₀, Q r t < q := (hc.tendsto.eventually (eventually_lt_nhds hQ)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hd, he] with r hr hQr
    have hs := fiberAngle_spec hr
    have hθ : fiberAngle q r < t := by
      by_contra h
      have hh := (Q_strictAntiOn hr.1 hr.2.1).antitoneOn
        ⟨ht.le,htπ.le⟩ ⟨hs.1.1.le,hs.1.2.le⟩ (le_of_not_gt h)
      rw [hs.2] at hh
      linarith
    exact hθ.trans htb

/-- Zero radius is handled by the norm of the actual polar preimage; no
angle at the origin is imposed. -/
theorem fiberHeight_tendsto_at_zero (q : ℝ) :
    Tendsto (fiberHeight q) (𝓝 0) (𝓝 0) := by
  have hn : Tendsto (fun r : ℝ => ‖polar r (fiberAngle q r)‖) (𝓝 0) (𝓝 0) := by
    simpa [polar, Complex.norm_exp] using (continuous_abs.tendsto (0 : ℝ))
  have hp : Tendsto (fun r : ℝ => polar r (fiberAngle q r)) (𝓝 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hF := (hasDerivAt_F_series (w := 0) (by simp)).continuousAt.tendsto.comp hp
  change Tendsto (fun r => (F (polar r (fiberAngle q r))).im) (𝓝 0) (𝓝 0)
  simpa only [F_zero, Complex.zero_im, Function.comp_def] using Complex.continuous_im.continuousAt.tendsto.comp hF

/-- The endpoint of the selected fiber, including q=0. -/
theorem fiberHeight_tendsto_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) :
    Tendsto (fiberHeight q) (𝓝[>] r₀) (𝓝 0) := by
  rcases hr₀.eq_or_lt with hzero | hpos
  · subst r₀
    exact (fiberHeight_tendsto_at_zero q).mono_left nhdsWithin_le_nhds
  have hnonneg (p : ℝ) (hp : 0 ≤ p) (he : radialMap r₀ = |p|) :
      Tendsto (fiberHeight p) (𝓝[>] r₀) (𝓝 0) := by
    have ht := fiberAngle_tendsto_zero hpos hr₁ hp he
    have hc := (contDiffAt_S_uncurry (θ := 0) hpos hr₁).continuousAt.tendsto
    have hp : Tendsto (fun r : ℝ => (r, fiberAngle p r)) (𝓝[>] r₀) (𝓝 (r₀,0)) :=
      (show Tendsto (fun r : ℝ => r) (𝓝[>] r₀) (𝓝 r₀) from nhdsWithin_le_nhds).prodMk_nhds ht
    change Tendsto (fun r => S r (fiberAngle p r)) (𝓝[>] r₀) (𝓝 0)
    simpa only [Function.comp_def, S_zero] using hc.comp hp
  by_cases hp : 0 ≤ q
  · exact hnonneg q hp hq
  · have hn := hnonneg (-q) (by linarith) (by simpa using hq)
    apply hn.congr'
    filter_upwards [eventually_fiberDomain hr₀ hr₁ hq] with r hr
    exact fiberHeight_neg hr

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_GlobalVerticalGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global vertical intervals of the conformal image. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma exists_radial_basepoint {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ r₀ ∈ Ico (0 : ℝ) 1, radialMap r₀ = |q| := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1],hq.2⟩
  have he := eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r,hr,hqr⟩ := he.exists
  obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by
      simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  exact ⟨t,⟨ht.1,ht.2.trans_lt hr.2⟩,hte⟩

lemma fiberHeight_basepoint {q r₀ : ℝ} (hq : radialMap r₀ = |q|) :
    fiberHeight q r₀ = 0 := by
  have hn : r₀ ∉ fiberDomain q := by simp [fiberDomain, hq]
  simp [fiberHeight, fiberAngle, hn, S_zero]

lemma continuousOn_fiberHeight_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ContinuousOn (fiberHeight q) (Ico r₀ 1) := by
  intro r hr
  rcases hr.1.eq_or_lt with he | hlt
  · subst r
    have hc : ContinuousWithinAt (fiberHeight q) (Ioi r₀) r₀ := by
      rw [ContinuousWithinAt, fiberHeight_basepoint hq]
      exact fiberHeight_tendsto_basepoint hr₀ hr₁ hq
    exact (continuousWithinAt_Ioi_iff_Ici.mp hc).mono (fun _ h => h.1)
  · exact (hasDerivAt_fiberHeight (mem_fiberDomain_of_basepoint hr₀ hq ⟨hlt,hr.2⟩)).continuousAt.continuousWithinAt

lemma strictMonoOn_fiberHeight_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : StrictMonoOn (fiberHeight q) (Ico r₀ 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
    (continuousOn_fiberHeight_basepoint hr₀ hr₁ hq)
  intro r hr
  rw [interior_Ico] at hr
  exact deriv_fiberHeight_pos (mem_fiberDomain_of_basepoint hr₀ hq hr)

lemma fiberHeight_pos {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|)
    (hr : r ∈ Ioo r₀ 1) : 0 < fiberHeight q r := by
  have h := strictMonoOn_fiberHeight_basepoint hr₀ (hr.1.trans hr.2) hq
    ⟨le_rfl,hr.1.trans hr.2⟩ ⟨hr.1.le,hr.2⟩ hr.1
  simpa [fiberHeight_basepoint hq] using h

lemma fiberHeight_nonneg {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|)
    (hr : r ∈ Ico r₀ 1) : 0 ≤ fiberHeight q r := by
  rcases hr.1.eq_or_lt with he | hlt
  · subst r; rw [fiberHeight_basepoint hq]
  · exact (fiberHeight_pos hr₀ hq ⟨hlt,hr.2⟩).le

lemma zero_mem_verticalFiber {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : 0 ∈ verticalFiber q := by
  obtain ⟨t,ht,hF⟩ := exists_real_preimage hq
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [Complex.norm_real, abs_lt] using ht
  simpa [verticalFiber] using (show (q : ℂ) ∈ Omega from ⟨t,hw,hF⟩)

lemma fiberHeight_mem_verticalFiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight q r ∈ verticalFiber q := by
  refine ⟨polar r (fiberAngle q r), ?_, ?_⟩
  · simpa [norm_polar hr.1.le] using hr.2.1
  · apply Complex.ext
    · simpa [Q] using (fiberAngle_spec hr).2
    · simp [fiberHeight, S]

lemma verticalFiber_neg {q y : ℝ} (hy : y ∈ verticalFiber q) : -y ∈ verticalFiber q := by
  have h := Omega_conj hy
  simpa [verticalFiber, map_add, map_mul] using h

lemma angular_height_mem_image {q r₀ r θ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) (hQ : Q r θ = q) :
    S r θ ∈ fiberHeight q '' Ico r₀ 1 := by
  by_cases hz : θ = 0
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hz,S_zero,fiberHeight_basepoint hq]⟩
  by_cases hp : θ = Real.pi
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hp,S_pi,fiberHeight_basepoint hq]⟩
  have hi : θ ∈ Ioo 0 Real.pi := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hz),lt_of_le_of_ne hθ.2 hp⟩
  have hm := Q_mem_Ioo hr hr1 hi.1 hi.2
  rw [hQ] at hm
  have habs : |q| < radialMap r := abs_lt.mpr hm
  have hrr : r₀ < r := by
    by_contra h
    have hb := strictMonoOn_radialMap.monotoneOn ⟨hr.le,hr1⟩ ⟨hr₀,hr₁⟩ (le_of_not_gt h)
    rw [hq] at hb
    linarith
  have hd : r ∈ fiberDomain q := ⟨hr,hr1,habs⟩
  have hs := fiberAngle_spec hd
  have he := (Q_strictAntiOn hr hr1).injOn ⟨hs.1.1.le,hs.1.2.le⟩ hθ (hs.2.trans hQ.symm)
  exact ⟨r,⟨hrr.le,hr1⟩,by simp only [fiberHeight,he]⟩

/-- Every image height belongs to the global increasing upper fiber or its reflection. -/
theorem verticalFiber_eq_images {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    verticalFiber q = fiberHeight q '' Ico r₀ 1 ∪
      (fun r => -fiberHeight q r) '' Ico r₀ 1 := by
  ext y
  constructor
  · rintro ⟨w,hw,hF⟩
    have hn : ‖w‖ < 1 := by simpa using hw
    have hQw : (F w).re = q := by rw [hF]; simp
    have hSw : (F w).im = y := by rw [hF]; simp
    by_cases hw0 : w = 0
    · have hy : y = 0 := by simpa [hw0,F_zero] using hSw.symm
      exact Or.inl ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hy,fiberHeight_basepoint hq]⟩
    have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have he : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    by_cases ha : 0 ≤ w.arg
    · have h := angular_height_mem_image hr₀ hr₁ hq hr hn ⟨ha,Complex.arg_le_pi w⟩
        (show Q ‖w‖ w.arg = q by simpa [Q,he] using hQw)
      exact Or.inl (by simpa [S,he,hSw] using h)
    · have har : -w.arg ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith,by linarith [Complex.neg_pi_lt_arg w]⟩
      have hep : polar ‖w‖ (-w.arg) = starRingEnd ℂ w := by rw [polar_neg_angle,he]
      have h := angular_height_mem_image hr₀ hr₁ hq hr hn har
        (show Q ‖w‖ (-w.arg) = q by simpa [Q,hep,F_conj] using hQw)
      obtain ⟨r,hrt,heq⟩ := h
      refine Or.inr ⟨r,hrt,?_⟩
      simpa [S,hep,F_conj,hSw] using congrArg Neg.neg heq
  · intro hy
    have hmem {r : ℝ} (hr : r ∈ Ico r₀ 1) : fiberHeight q r ∈ verticalFiber q := by
      rcases hr.1.eq_or_lt with he | ht
      · subst r; rw [fiberHeight_basepoint hq]; exact zero_mem_verticalFiber hqstrip
      · exact fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq ⟨ht,hr.2⟩)
    rcases hy with ⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩
    · exact hmem hr
    · exact verticalFiber_neg (hmem hr)

/-- The actual global vertical section is an open interval containing zero. -/
theorem verticalFiber_interval {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    IsOpen (verticalFiber q) ∧ OrdConnected (verticalFiber q) ∧ 0 ∈ verticalFiber q := by
  obtain ⟨r₀,hr₀,hbase⟩ := exists_radial_basepoint hq
  have hc := continuousOn_fiberHeight_basepoint hr₀.1 hr₀.2 hbase
  have hp := isPreconnected_Ico.image (fiberHeight q) hc
  have hn := isPreconnected_Ico.image (fun r => -fiberHeight q r) hc.neg
  have hz : (0 : ℝ) ∈ fiberHeight q '' Ico r₀ 1 ∩ (fun r => -fiberHeight q r) '' Ico r₀ 1 :=
    ⟨⟨r₀,⟨le_rfl,hr₀.2⟩,fiberHeight_basepoint hbase⟩,
     ⟨r₀,⟨le_rfl,hr₀.2⟩,by dsimp only; rw [fiberHeight_basepoint hbase,neg_zero]⟩⟩
  refine ⟨isOpen_Omega.preimage (by fun_prop),?_,zero_mem_verticalFiber hq⟩
  rw [verticalFiber_eq_images hq hr₀.1 hr₀.2 hbase]
  exact (IsPreconnected.union' ⟨0,hz⟩ hp hn).ordConnected

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_GlobalFiberParametrization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma F_polar_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    F (polar r (fiberAngle q r)) = (q : ℂ) + (fiberHeight q r : ℂ)*I := by
  apply Complex.ext
  · simpa [Q] using (fiberAngle_spec hr).2
  · simp [fiberHeight,S]

/-- The already proved conformal inverse agrees with the actual global polar choice. -/
theorem inverseF_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    inverseF ((q : ℂ) + (fiberHeight q r : ℂ)*I) = polar r (fiberAngle q r) := by
  rw [← F_polar_fiberAngle hr]
  apply inverseF_left
  simpa [norm_polar hr.1.le] using hr.2.1

theorem norm_inverseF_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ‖inverseF ((q : ℂ) + (fiberHeight q r : ℂ)*I)‖ = r := by
  rw [inverseF_fiberHeight hr,norm_polar hr.1.le]

/-- No positive heights are omitted, and no spurious positive heights are added. -/
theorem positive_verticalFiber_eq_image {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    verticalFiber q ∩ Ioi 0 = fiberHeight q '' Ioo r₀ 1 := by
  ext y
  constructor
  · rintro ⟨hy,hpos⟩
    rw [verticalFiber_eq_images hqstrip hr₀ hr₁ hq] at hy
    rcases hy with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
    · have hlt : r₀ < r := by
        rcases hr.1.eq_or_lt with hz | ht
        · subst r
          rw [fiberHeight_basepoint hq] at he
          exact False.elim (by simp [← he] at hpos)
        · exact ht
      exact ⟨r,⟨hlt,hr.2⟩,he⟩
    · have hn := fiberHeight_nonneg hr₀ hq hr
      dsimp only at he
      change 0 < y at hpos
      linarith
  · rintro ⟨r,hr,rfl⟩
    exact ⟨fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq hr),
      fiberHeight_pos hr₀ hq hr⟩

/-- The whole integration segment for the vertical primitive belongs to Omega. -/
theorem vertical_segment_mem_Omega {u : ℂ} (hu : u ∈ Omega) {t : ℝ}
    (ht : t ∈ uIcc 0 u.im) : (u.re : ℂ) + (t : ℂ)*I ∈ Omega := by
  have hq : u.re ∈ Ioo (-1 : ℝ) 1 := by
    rw [← image_re_F_disk]
    exact ⟨u,hu,rfl⟩
  have hv := verticalFiber_interval hq
  have hy : u.im ∈ verticalFiber u.re := by
    simpa only [verticalFiber, mem_ofPred_eq, Complex.re_add_im] using hu
  exact hv.2.1.uIcc_subset hv.2.2 hy ht

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PrimitiveEquality
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- Along the actual fiber, the original vertical primitive has exactly the
radial density as derivative. This proves the substitution locally without
assuming a change-of-variables identity. -/
theorem hasDerivAt_planarPrimitive_fiber {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1)
    (hseg : ∀ t ∈ uIcc (0 : ℝ) (fiberHeight q r),
      (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    HasDerivAt (fun s => planarPrimitive m q (fiberHeight q s))
      (radialPrimitiveDensity (fiberAngle q) (m : ℝ) r) r := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hH : HasDerivAt (fiberHeight q) (deriv (fiberHeight q) r) r :=
    (hasDerivAt_fiberHeight hmem).differentiableAt.hasDerivAt
  have hG := (hasDerivAt_planarPrimitive m hseg).comp r hH
  have hA := (hasDerivAt_actual_primitive_density hm hr₀ hq hr).comp r hH
  have hR : HasDerivAt (radialPrimitive q r₀ (m : ℝ))
      (planarDensity m ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)*deriv (fiberHeight q) r) r := by
    apply hA.congr_of_eventuallyEq
    filter_upwards [(fiberDomain_isOpen q).mem_nhds hmem] with s hs
    simp only [Function.comp_def, verticalRadius_fiber hs]
  have heq := hR.unique (hasDerivAt_radialPrimitive (m := (m : ℝ)) (by exact_mod_cast hm) hr₀ hq hr)
  rw [heq] at hG
  exact hG

/-- Global radial substitution follows once the fiber's endpoint continuity
and vertical-segment geometry have been established. -/
theorem planarPrimitive_eq_radial_of_geometry {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1)
    (hheight : ContinuousOn (fiberHeight q) (Icc r₀ r))
    (hseg : ∀ s ∈ Icc r₀ r, ∀ t ∈ uIcc (0 : ℝ) (fiberHeight q s),
      (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    planarPrimitive m q (fiberHeight q r) = radialPrimitive q r₀ (m : ℝ) r := by
  let G : ℝ → ℝ := fun s => planarPrimitive m q (fiberHeight q s) - radialPrimitive q r₀ (m : ℝ) s
  have hi := radial_primitive_integrable (m := (m : ℝ)) (measurable_fiberAngle q) (by exact_mod_cast hm)
    hr₀ hr.1.le hr.2 (fun s hs => fiberAngle_sine_bound hr₀ hq hs)
  have hRcont : ContinuousOn (radialPrimitive q r₀ (m : ℝ)) (Icc r₀ r) := by
    simpa only [radialPrimitive, uIcc_of_le hr.1.le] using!
      intervalIntegral.continuousOn_primitive_interval' hi (show r₀ ∈ uIcc r₀ r from left_mem_uIcc)
  have hGcont : ContinuousOn G (Icc r₀ r) := by
    apply ContinuousOn.sub _ hRcont
    intro s hs
    exact (hasDerivAt_planarPrimitive m (hseg s hs)).continuousAt.comp_continuousWithinAt (hheight s hs)
  have hGder : ∀ s ∈ Ioo r₀ r, HasDerivAt G 0 s := by
    intro s hs
    have hs1 : s ∈ Ioo r₀ 1 := ⟨hs.1,hs.2.trans hr.2⟩
    have hleft := hasDerivAt_planarPrimitive_fiber hm hr₀ hq hs1 (hseg s ⟨hs.1.le,hs.2.le⟩)
    have hright := hasDerivAt_radialPrimitive (m := (m : ℝ)) (by exact_mod_cast hm) hr₀ hq hs1
    simpa only [G, Pi.sub_apply, sub_self] using! hleft.sub hright
  obtain ⟨s,hs,heq⟩ := exists_hasDerivAt_eq_slope G (fun _ => 0) hr.1 hGcont hGder
  have hzero : G r₀ = 0 := by simp [G, fiberHeight_basepoint hq, planarPrimitive_zero, radialPrimitive]
  rw [hzero, sub_zero] at heq
  have hGr : G r = 0 := by
    have h := (eq_div_iff (sub_pos.mpr hr.1).ne').mp heq
    simpa using h.symm
  exact sub_eq_zero.mp hGr

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_GlobalPlanarBound
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology
open MahlerConformal

/-- The vertical integral is the radial primitive, with endpoint
continuity and every integration segment contained in the actual domain. -/
theorem planarPrimitive_eq_radial {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    planarPrimitive m q (fiberHeight q r) = radialPrimitive q r₀ (m : ℝ) r := by
  have hr₁ := hr.1.trans hr.2
  have hstrip : q ∈ Ioo (-1 : ℝ) 1 := by
    have hab : |q| < 1 := by
      rw [← hq]
      exact (F_re_mem_strip (w := (r₀ : ℂ)) (by simpa [Complex.norm_real,abs_of_nonneg hr₀] using hr₁)).2
    exact ⟨by linarith [(abs_lt.mp hab).1],(abs_lt.mp hab).2⟩
  apply planarPrimitive_eq_radial_of_geometry hm hr₀ hq hr
  · exact (continuousOn_fiberHeight_basepoint hr₀ hr₁ hq).mono
      (fun s hs => ⟨hs.1,hs.2.trans_lt hr.2⟩)
  · intro s hs t ht
    have hu : (q : ℂ)+(fiberHeight q s : ℂ)*I ∈ Omega := by
      rcases hs.1.eq_or_lt with he | hlt
      · subst s
        simpa [fiberHeight_basepoint hq, verticalFiber] using zero_mem_verticalFiber hstrip
      · exact fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq ⟨hlt,hs.2.trans_lt hr.2⟩)
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,mul_one] using vertical_segment_mem_Omega hu (t := t) (by simpa using ht)

/-- Uniform bound for the vertical integral on the upper section. -/
theorem planarPrimitive_upper_bound {m : ℕ} (hm : 2 ≤ m) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) (ht : 0 ≤ t) :
    planarPrimitive m q t ≤ ‖inverseF ((q : ℂ)+(t : ℂ)*I)‖^(2*(m : ℝ) : ℝ)+planarError m := by
  rcases ht.eq_or_lt with hz | hp
  · subst t
    rw [planarPrimitive_zero]
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (planarError_nonneg _)
  have hstrip : q ∈ Ioo (-1 : ℝ) 1 := by
    have h := F_re_mem_strip (w := inverseF ((q : ℂ)+(t : ℂ)*I)) (by simpa using inverseF_mem hu)
    rw [inverseF_right hu] at h
    simpa using h
  obtain ⟨r₀,hr₀,hq⟩ := exists_radial_basepoint hstrip
  have htmem : t ∈ verticalFiber q ∩ Ioi 0 := ⟨hu,hp⟩
  rw [positive_verticalFiber_eq_image hstrip hr₀.1 hr₀.2 hq] at htmem
  obtain ⟨r,hr,rfl⟩ := htmem
  rw [planarPrimitive_eq_radial hm hr₀.1 hq hr,
    norm_inverseF_fiberHeight (mem_fiberDomain_of_basepoint hr₀.1 hq hr)]
  exact fiber_primitive_bound (by exact_mod_cast hm) hr₀.1 hq ⟨hr.1.le,hr.2⟩

/-- Uniform bound for F, inverseF and the vertical integral:
one nonnegative error tends to zero and controls every point of Omega. -/
theorem planarPrimitive_abs_bound {m : ℕ} (hm : 2 ≤ m) {u : ℂ} (hu : u ∈ Omega) :
    |planarPrimitive m u.re u.im| ≤ ‖inverseF u‖^(2*(m : ℝ) : ℝ)+planarError m := by
  have he : (u.re : ℂ)+(u.im : ℂ)*I = u := Complex.re_add_im u
  have hseg : ∀ s ∈ uIcc (0 : ℝ) u.im, (u.re : ℂ)+(s : ℂ)*I ∈ Omega :=
    fun s hs => vertical_segment_mem_Omega hu hs
  by_cases ht : 0 ≤ u.im
  · rw [abs_of_nonneg (planarPrimitive_nonneg m u.re ht)]
    have hb := planarPrimitive_upper_bound hm (q := u.re) (t := u.im) (by simpa only [Complex.re_add_im] using hu) ht
    simpa only [Complex.re_add_im] using! hb
  · have hc := Omega_conj hu
    have hcp : (u.re : ℂ)+((-u.im : ℝ) : ℂ)*I = starRingEnd ℂ u := by
      apply Complex.ext <;> simp
    have hb := planarPrimitive_upper_bound hm (hcp ▸ hc) (neg_nonneg.mpr (le_of_not_ge ht))
    rw [planarPrimitive_neg m hseg,hcp,inverseF_conj hu] at hb
    have hn : planarPrimitive m u.re u.im ≤ 0 := by
      have hp := planarPrimitive_nonneg m u.re (neg_nonneg.mpr (le_of_not_ge ht))
      rw [planarPrimitive_neg m hseg] at hp
      linarith
    simpa only [abs_of_nonpos hn,Complex.norm_conj] using hb

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ActualFiniteStrips
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

lemma verticalFiber_realPart {q t : ℝ} (ht : t ∈ verticalFiber q) : q ∈ Ioo (-1 : ℝ) 1 := by
  have hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ Omega := ht
  have h := F_re_mem_strip (w := inverseF ((q : ℂ)+(t : ℂ)*Complex.I))
    (by simpa using inverseF_mem hu)
  rw [inverseF_right hu] at h
  simpa using h

omit fintypeJ in
lemma stripDomain_realPart [Fintype J] (A : J → I → ℝ) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) : z.1 ∈ stripBody A := by
  intro j
  exact (abs_lt.mpr (verticalFiber_realPart (hz j))).le

/-- The image functional bound uses the literal P and tau, with the
uniform analytic estimate proved rather than supplied as a premise. -/
theorem stripMap_pairing_bound (A : J → I → ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hτ : stripTau A m z < 1)
    {v : I → ℝ} (hv : v ∈ stripBody A) :
    (∑ i, (stripMap A m z).2 i*v i) < 1+Fintype.card J*planarError m := by
  apply image_bound_with_error A
    (fun j => planarPrimitive m (measurement A z.1 j) (measurement A z.2 j))
    (fun j => ‖inverseF (stripCoordinate A z j)‖^(2*(m : ℝ) : ℝ)) (planarError m)
    _ hτ v hv
  intro j
  simpa [stripCoordinate] using planarPrimitive_abs_bound hm (hz j)

/-- Dividing the image's vertical component by 1+N epsilon places it in the
literal polar body of the strip intersection. -/
theorem normalized_stripMap_mem_polar (A : J → I → ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hτ : stripTau A m z < 1) :
    (fun i => (stripMap A m z).2 i/(1+Fintype.card J*planarError m)) ∈
      coordinatePolar (stripBody A) := by
  have hc : 0 < 1+Fintype.card J*planarError m := by
    have := planarError_nonneg (m : ℝ)
    positivity
  intro v hv
  have h := (stripMap_pairing_bound A hm hz hτ hv).le
  calc
    _ = (∑ i, (stripMap A m z).2 i*v i)/(1+Fintype.card J*planarError m) := by
      simp only [div_mul_eq_mul_div, sum_div]
    _ ≤ 1 := (div_le_one hc).mpr h

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripVolume
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

/-- Pointwise containment in K times a scaled polar body. -/
theorem stripMap_image_subset_product (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    stripMap A m '' stripSublevel A m ⊆ stripBody A ×ˢ
      ((1+(N : ℝ)*planarError m) • coordinatePolar (stripBody A)) := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨?_,?_⟩
  · exact stripDomain_realPart A (z := z) hz.1
  · have hc : 0 < 1+(N : ℝ)*planarError m := by
      have := planarError_nonneg (m : ℝ)
      positivity
    refine ⟨fun i => (stripMap A m z).2 i/(1+(N : ℝ)*planarError m),?_,?_⟩
    · simpa only [Fintype.card_fin] using normalized_stripMap_mem_polar A hm hz.1 hz.2
    · funext i
      simp only [Pi.smul_apply,smul_eq_mul]
      field_simp
/-- The image-volume upper bound from the actual polar containment. -/
theorem stripMap_volume_le_product_oai (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) ≤
      volume (stripBody A) * (ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
        volume (coordinatePolar (stripBody A))) := by
  have hc : 0 ≤ 1+(N : ℝ)*planarError m := by
    have := planarError_nonneg (m : ℝ)
    positivity
  have h := measure_mono (μ := volume) (stripMap_image_subset_product A hm)
  rw [Measure.volume_eq_prod,Measure.prod_prod,
    Measure.addHaar_smul_of_nonneg volume hc] at h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one, ← Measure.volume_eq_prod] using! h

end SymmetricMahler

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.stripMap_volume_le_product_oai := @OAI.SymmetricMahler.stripMap_volume_le_product_oai
