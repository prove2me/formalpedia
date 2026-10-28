-- Prove2me | solution 1 for OAI.SymmetricMahler.equality_polar_gauge_medians_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:32:19.50619+00:00
-- url     : https://prove2.me/submissions/46ae3456-7f22-4ba2-bf63-ad0bdddd1bc3

import Mathlib
import Definitions.Def_SymmetricMahlerEquality
import Definitions.Def_OAIQ2Ma000
import Theorems.Thm_OAI_SymmetricMahler_equality_strip_images_dense_eq
import Theorems.Thm_OAI_SymmetricMahler_strip_concentration_bound_eq
import Theorems.Thm_OAI_SymmetricMahler_strip_weights_bound_eq

section
-- module Solutions.OAIQ2_Mah.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_ConformalSeries
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_AngularGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_TailIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ErrorBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real

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

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_UniformError
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end SymmetricMahler

namespace SymmetricMahler
open Real Filter
open scoped Topology

/-- A decaying bound for the inner term, weaker than O(m⁻¹)
but sufficient for uniform convergence. -/
theorem cutoff_power_bound {m : ℝ} (hm : 3 ≤ m) :
    m*(radialCutoff m)^(2*m-3/2 : ℝ) ≤ 1/sqrt m := by
  have hmpos : 0 < m := by linarith
  have hm1 : 1 < m := by linarith
  have hcut := radial_cutoff_bounds hm1
  have hlogm := log_le_sub_one_of_pos hmpos
  have hcutpos : 0 < radialCutoff m := by
    dsimp [radialCutoff]
    have hlt : log m/m < 1 := (div_lt_one hmpos).2 (by linarith)
    linarith
  have hpow : (radialCutoff m)^(2*m-3/2 : ℝ) ≤
      exp (-(3*m/2)*(1-radialCutoff m)) := by
    rw [rpow_def_of_pos hcutpos]
    apply exp_le_exp.mpr
    have hlog := log_le_sub_one_of_pos hcutpos
    have hsign := log_nonpos hcut.1 hcut.2.le
    have hneg := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (2*m-3/2)-(3*m/2) by linarith) hsign
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 3*m/2 by linarith)
    nlinarith
  calc
    m*(radialCutoff m)^(2*m-3/2 : ℝ) ≤
        m*exp (-(3*m/2)*(1-radialCutoff m)) :=
      mul_le_mul_of_nonneg_left hpow hmpos.le
    _ = m*m^(-(3/2 : ℝ)) := by
      rw [rpow_def_of_pos hmpos]
      congr 1
      congr 1
      dsimp [radialCutoff]
      field_simp
      ring
    _ = m^(-(1/2 : ℝ)) := by
      conv_lhs => lhs; rw [← rpow_one m]
      rw [← rpow_add hmpos]
      norm_num
    _ = 1/sqrt m := (inverse_sqrt_eq_rpow hmpos.le).symm

/-- The uniform majorant tends to zero; its rate is enough for the planar lemma. -/
theorem error_envelope_tendsto_zero : Tendsto errorEnvelope atTop (𝓝 0) := by
  have hinvsqrt : Tendsto (fun m : ℝ => 1/sqrt m) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  have hinnerlim : Tendsto (fun m : ℝ =>
      (2/sqrt (4/Real.pi^2))*(1/sqrt m)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinvsqrt
  have hinner : Tendsto (fun m : ℝ =>
      2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hinnerlim
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with m hm
      have hm1 : 1 < m := by linarith
      have hc := (radial_cutoff_bounds hm1).1
      have hm0 : 0 ≤ m := by linarith
      positivity
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with m hm
      have h := mul_le_mul_of_nonneg_left (cutoff_power_bound hm)
        (show 0 ≤ 2/sqrt (4/Real.pi^2) by positivity)
      calc
        _ = (2/sqrt (4/Real.pi^2))*(m*(radialCutoff m)^(2*m-3/2 : ℝ)) := by ring
        _ ≤ _ := h
  have hinvlog : Tendsto (fun m : ℝ => 1/log m) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_log_atTop
  have hbase : Tendsto (fun m : ℝ => 2/((2/Real.pi^2)*log m)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2/(2/Real.pi^2)) atTop
      (𝓝 (2/(2/Real.pi^2)))).mul hinvlog
    convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  have hsqrt := continuous_sqrt.continuousAt.tendsto.comp hbase
  have houter : Tendsto (fun m : ℝ =>
      sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)) atTop (𝓝 0) := by
    simpa using hsqrt.mul_const (1+4/exp 1)
  change Tendsto (fun m : ℝ => 2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) +
    sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)) atTop (𝓝 0)
  simpa only [add_zero] using hinner.add houter

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_RadialBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex MeasureTheory Set

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
-- module Solutions.OAIQ2_Mah.Mahler_VerticalSpeed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_ImplicitAngle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_AngularFibers
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_FiberHeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularIntegrals
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
      convert (hasDerivAt_Q hr hr1 θ).neg using 1
      all_goals first | rfl | simp only [neg_neg])
    (show IntervalIntegrable (B r) volume a b from (continuous_B r).intervalIntegrable a b)
  simpa only [neg_neg, neg_sub_neg] using h

/-- The normalization identity for the angular integral. -/
theorem integral_B_semicircle {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, B r θ) = 2*(F (r : ℂ)).re := by
  rw [integral_B hr hr1, Q_zero, Q_pi]
  ring

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiberPrimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

lemma planarError_nonneg (m : ℝ) : 0 ≤ planarError m := le_max_left _ _

lemma planarError_tendsto_zero : Filter.Tendsto planarError Filter.atTop (nhds 0) := by
  have h := error_envelope_tendsto_zero.const_mul Real.pi
  have hh := Filter.Tendsto.max (tendsto_const_nhds (x := (0 : ℝ))) h
  change Filter.Tendsto (fun m : ℝ => max 0 (Real.pi*errorEnvelope m)) Filter.atTop (nhds 0)
  simpa only [mul_zero, max_self] using! hh

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularEndpoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_AngularStrip
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInjectivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

theorem inverseF_deriv_ne_zero {u : ℂ} (hu : u ∈ Omega) : deriv inverseF u ≠ 0 := by
  rw [(hasDerivAt_inverseF hu).deriv]
  exact inv_ne_zero (deriv_F_ne_zero (by simpa using inverseF_mem hu))

theorem Omega_conj {u : ℂ} (hu : u ∈ Omega) : starRingEnd ℂ u ∈ Omega := by
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa using hw

theorem zero_mem_Omega : (0 : ℂ) ∈ Omega := ⟨0, by simp, F_zero⟩

theorem inverseF_zero : inverseF 0 = 0 := by
  simpa only [F_zero] using inverseF_left (w := 0) (by simp)

theorem inverseF_eq_zero_iff {u : ℂ} (hu : u ∈ Omega) : inverseF u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [← inverseF_right hu, h, F_zero]
  · intro h
    rw [h, inverseF_zero]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PlanarDensity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
  convert (hre.mul hre).add (him.mul him) using 1 <;> rfl

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

lemma planarDensity_pos {m : ℕ} (hm : 0 < m) {u : ℂ}
    (hu : u ∈ MahlerConformal.Omega) (hu0 : u ≠ 0) : 0 < planarDensity m u := by
  have hh : 0 < Complex.normSq (MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (fun h => hu0 ((MahlerConformal.inverseF_eq_zero_iff hu).mp h))
  have hhd : 0 < Complex.normSq (deriv MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (MahlerConformal.inverseF_deriv_ne_zero hu)
  unfold planarDensity
  positivity

lemma continuousAt_planarDensity_vertical (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    ContinuousAt (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) t := by
  have hl : ContinuousAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) t := by fun_prop
  have hd := (contDiffAt_planarDensity m hu).continuousAt
  have hc := hd.comp (f := fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) hl
  exact hc

lemma planarPrimitive_zero (m : ℕ) (q : ℝ) : planarPrimitive m q 0 = 0 := by
  simp [planarPrimitive]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiberEndpoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_GlobalVerticalGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_GlobalPlanarMonotonicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- The original primitive is strictly increasing on every entire actual
vertical section, including across its possible zero derivative at the origin. -/
theorem strictMonoOn_planarPrimitive_global {m : ℕ} (hm : 0 < m) {q : ℝ}
    (hq : q ∈ Ioo (-1 : ℝ) 1) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  have hv := verticalFiber_interval hq
  have hcont : ∀ a b : ℝ, a ∈ verticalFiber q → b ∈ verticalFiber q →
      ContinuousOn (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) (uIcc a b) := by
    intro a b ha hb s hs
    have hmem : s ∈ verticalFiber q := hv.2.1.uIcc_subset ha hb hs
    exact (continuousAt_planarDensity_vertical m hmem).continuousWithinAt
  intro a ha b hb hab
  have h0 : (0 : ℝ) ∈ verticalFiber q := hv.2.2
  have hia := (hcont 0 a h0 ha).intervalIntegrable (μ := volume)
  have hiab := (hcont a b ha hb).intervalIntegrable (μ := volume)
  have heq := intervalIntegral.integral_add_adjacent_intervals hia hiab
  have hpos : 0 < ∫ s in a..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
    apply intervalIntegral.integral_pos hab
    · simpa only [uIcc_of_le hab.le] using hcont a b ha hb
    · intro s _
      exact planarDensity_nonneg m _
    · by_cases ha0 : a = 0
      · refine ⟨b,⟨hab.le,le_rfl⟩,planarDensity_pos hm hb ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      · refine ⟨a,⟨le_rfl,hab.le⟩,planarDensity_pos hm ha ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        exact ha0 him
  change (∫ s in (0 : ℝ)..a, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) <
    ∫ s in (0 : ℝ)..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ActualFiniteStrips
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

lemma strictMonoOn_planarPrimitive_any {m : ℕ} (hm : 0 < m) (q : ℝ) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  intro a ha b hb hab
  exact strictMonoOn_planarPrimitive_global hm (verticalFiber_realPart ha) ha hb hab

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexApproximation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-strip approximation with coordinate definitions of the convex body and its polar. -/
namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [Fintype I] [Fintype J]

lemma continuous_pairing (x : I → ℝ) : Continuous (fun p : I → ℝ => ∑ i, p i * x i) := by
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

lemma coordinatePolar_antitone {K L : Set (I → ℝ)} (h : K ⊆ L) :
    coordinatePolar L ⊆ coordinatePolar K := fun _ hp x hx => hp x (h hx)

lemma zero_mem_coordinatePolar (K : Set (I → ℝ)) : (0 : I → ℝ) ∈ coordinatePolar K := by
  intro x hx
  simp

lemma isClosed_coordinatePolar (K : Set (I → ℝ)) : IsClosed (coordinatePolar K) := by
  have heq : coordinatePolar K = ⋂ x ∈ K, {p | (∑ i, p i*x i) ≤ 1} := by
    ext p
    simp [coordinatePolar]
  rw [heq]
  exact isClosed_biInter (fun x hx => isClosed_le (continuous_pairing x) continuous_const)

/-- Strict separation normalized by a positive separator level. The origin
membership makes that level positive, without assuming a supporting maximum. -/
theorem exists_coordinatePolar_separator [DecidableEq I] {K : Set (I → ℝ)}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K)
    {x : I → ℝ} (hx : x ∉ K) :
    ∃ p ∈ coordinatePolar K, 1 < ∑ i, p i * x i := by
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hclosed hx
  have hu0 : 0 < u := by simpa using hu 0 hzero
  refine ⟨fun i => f (Pi.single i 1) / u, ?_, ?_⟩
  · intro v hv
    simp only [div_mul_eq_mul_div, ← sum_div, pairing_of_dual]
    exact (div_le_one hu0).mpr (hu v hv).le
  · simp only [div_mul_eq_mul_div, ← sum_div, pairing_of_dual]
    exact (one_lt_div hu0).mpr hux

lemma polar_pairing_abs {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K)
    {p : I → ℝ} (hp : p ∈ coordinatePolar K) {x : I → ℝ} (hx : x ∈ K) :
    |∑ i, p i * x i| ≤ 1 := by
  refine abs_le.mpr ⟨?_, hp x hx⟩
  have h := hp (-x) (hsym x hx)
  simp only [Pi.neg_apply, mul_neg, sum_neg_distrib] at h
  linarith

/-- Dense polar constraints recover the original closed convex set. -/
theorem dense_polar_strips_intersection [DecidableEq I] {K : Set (I → ℝ)}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K)
    (hsym : ∀ x ∈ K, -x ∈ K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    {x : I → ℝ | ∀ j, |∑ i, (a j).val i * x i| ≤ 1} = K := by
  ext x
  constructor
  · intro hx
    by_contra hxK
    obtain ⟨p, hp, hpx⟩ := exists_coordinatePolar_separator hconv hclosed hzero hxK
    let C : Set (coordinatePolar K) := {q | (∑ i, q.val i * x i) ≤ 1}
    have hC : IsClosed C :=
      isClosed_le ((continuous_pairing x).comp continuous_subtype_val) continuous_const
    have hr : Set.range a ⊆ C := by
      rintro _ ⟨j, rfl⟩
      exact (le_abs_self _).trans (hx j)
    have hpC : (⟨p, hp⟩ : coordinatePolar K) ∈ C := by
      rw [← hC.closure_eq]
      exact closure_mono hr (ha ⟨p, hp⟩)
    exact (not_le_of_gt hpx) hpC
  · intro hx j
    exact polar_pairing_abs hsym (a j).property hx

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [fintypeI : Fintype I] [fintypeJ : Fintype J] [decidableEqI : DecidableEq I]

/-- Compactness supplies small nonzero coordinate rows in the polar. -/
theorem exists_coordinate_rows {K : Set (I → ℝ)} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : I, Pi.single i c ∈ coordinatePolar K := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro i x hx
  have hxi : x i ≤ R := (le_abs_self _).trans ((norm_le_pi_norm x i).trans (hb x hx))
  have hbound : R⁻¹ * x i ≤ (1 : ℝ) := by
    rw [inv_mul_le_iff₀ hR]
    simpa using hxi
  simpa [Pi.single_apply] using hbound

omit fintypeJ decidableEqI in
/-- Finite strip constraints form a closed set. -/
theorem isClosed_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : IsClosed (stripBody A) := by
  have he : stripBody A = ⋂ j, {x | |measurement A x j| ≤ 1} := by
    ext x
    simp [stripBody]
  rw [he]
  refine isClosed_iInter (fun j => isClosed_le ?_ continuous_const)
  exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).abs

lemma approximationRows_basis (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) (x : I → ℝ) (i : I) :
    measurement (approximationRows c a N) x (.inl i) = c * x i := by
  simp [measurement, approximationRows, Pi.single_apply]

lemma stripBody_approximationRows_mem (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) (x : I → ℝ) :
    x ∈ stripBody (approximationRows c a N) ↔
      (∀ i, |c*x i| ≤ 1) ∧ (∀ j < N, |∑ i, a j i*x i| ≤ 1) := by
  constructor
  · intro hx
    refine ⟨fun i => ?_, fun j hj => ?_⟩
    · simpa only [approximationRows_basis] using hx (.inl i)
    · exact hx (.inr ⟨j, hj⟩)
  · rintro ⟨hb, hs⟩ (i | j)
    · simpa only [approximationRows_basis] using hb i
    · exact hs j j.isLt

/-- A single fixed coordinate box bounds every approximating strip body. -/
theorem approximation_subset_box {c : ℝ} (hc : 0 < c) (a : ℕ → I → ℝ) (N : ℕ) :
    stripBody (approximationRows c a N) ⊆ Icc (fun _ => -c⁻¹) (fun _ => c⁻¹) := by
  intro x hx
  have hb := (stripBody_approximationRows_mem c a N x).mp hx |>.1
  have hi : ∀ i, |x i| ≤ c⁻¹ := by
    intro i
    have h := hb i
    rw [abs_mul, abs_of_pos hc] at h
    simpa using (le_inv_mul_iff₀ hc).mpr h
  exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem isCompact_approximation {c : ℝ} (hc : 0 < c) (a : ℕ → I → ℝ) (N : ℕ) :
    IsCompact (stripBody (approximationRows c a N)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_stripBody _) (approximation_subset_box hc a N)

lemma approximation_antitone (c : ℝ) (a : ℕ → I → ℝ) :
    Antitone (fun N => stripBody (approximationRows c a N)) := by
  intro M N hMN x hx
  rw [stripBody_approximationRows_mem] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (lt_of_lt_of_le hj hMN)⟩

/-- The polar of a symmetric body is bounded because K contains a ball. -/
theorem isCompact_coordinatePolar {K : Set (I → ℝ)}
    (hsym : ∀ x ∈ K, -x ∈ K) (hzero : (0 : I → ℝ) ∈ interior K) :
    IsCompact (coordinatePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hb : ∀ i : I, Pi.single i (r/2) ∈ K := by
    intro i
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : I => -(r/2)⁻¹) (fun _ => (r/2)⁻¹))).of_isClosed_subset
    (isClosed_coordinatePolar K)
  intro p hp
  have hpi : ∀ i, |p i| ≤ (r/2)⁻¹ := by
    intro i
    have h := polar_pairing_abs hsym hp (hb i)
    simp [Pi.single_apply, abs_mul, abs_of_pos (half_pos hr)] at h
    have h' : (r/2)*|p i| ≤ 1 := by nlinarith
    simpa using (le_inv_mul_iff₀ (half_pos hr)).mpr h'
  exact ⟨fun i => (abs_le.mp (hpi i)).1, fun i => (abs_le.mp (hpi i)).2⟩

lemma subset_approximation {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K)
    (c : ℝ) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (N : ℕ) :
    K ⊆ stripBody (approximationRows c (fun j => (a j).val) N) := by
  intro x hx j
  cases j with
  | inl i => exact polar_pairing_abs hsym (hcK i) hx
  | inr j => exact polar_pairing_abs hsym (a j).property hx

/-- The common intersection is literally K, including the fixed initial rows. -/
theorem iInter_approximation {K : Set (I → ℝ)} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (c : ℝ) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    (⋂ N, stripBody (approximationRows c (fun j => (a j).val) N)) = K := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← dense_polar_strips_intersection hconv hclosed hzero hsym a ha]
    intro j
    have h := mem_iInter.mp hx (j+1)
    exact h (.inr ⟨j, Nat.lt_succ_self j⟩)
  · exact subset_iInter (fun N => subset_approximation hsym c hcK a N)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexTransfer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Continuity from above applies to the actual decreasing strip bodies. -/
theorem tendsto_volume_approximation {K : Set (I → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hzero : (0 : I → ℝ) ∈ K) (hsym : ∀ x ∈ K, -x ∈ K)
    {c : ℝ} (hc : 0 < c) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    Tendsto (fun N => (volume (stripBody (approximationRows c (fun j => (a j).val) N))).toReal)
      atTop (𝓝 (volume K).toReal) := by
  have hlim := tendsto_measure_iInter_atTop (μ := (volume : Measure (I → ℝ)))
    (fun N => (isClosed_stripBody (approximationRows c (fun j => (a j).val) N)).measurableSet.nullMeasurableSet)
    (approximation_antitone c (fun j => (a j).val))
    ⟨0, (isCompact_approximation hc (fun j => (a j).val) 0).measure_ne_top⟩
  rw [iInter_approximation hconv hK.isClosed hzero hsym c hcK a ha] at hlim
  exact (ENNReal.tendsto_toReal hK.measure_ne_top).comp hlim

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexCompletion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J J' : Type*} [Fintype I] [fintypeJ : Fintype J] [fintypeJPrime : Fintype J'] [decidableEqI : DecidableEq I]

omit fintypeJ decidableEqI in
lemma convex_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : Convex ℝ (stripBody A) := by
  intro x hx y hy a b ha hb hab j
  have he : measurement A (a • x + b • y) j =
      a * measurement A x j + b * measurement A y j := by
    simp only [measurement, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      sum_add_distrib, mul_sum]
    apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intros <;> ring
  rw [he]
  calc
    |a * measurement A x j + b * measurement A y j| ≤
        |a * measurement A x j| + |b * measurement A y j| := abs_add_le _ _
    _ = a * |measurement A x j| + b * |measurement A y j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (hx j) ha) (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = 1 := by linarith

omit fintypeJ decidableEqI in
lemma symmetric_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : ∀ x ∈ stripBody A, -x ∈ stripBody A := by
  intro x hx j
  simpa [measurement, mul_neg, sum_neg_distrib] using hx j

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexSequence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {n : ℕ} {K : Set (Fin n → ℝ)}

lemma prependPolarBasis_first (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (i : Fin n) :
    (prependPolarBasis c hcK a i).val = Pi.single i c := by
  simp [prependPolarBasis, i.isLt]

lemma prependPolarBasis_tail (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (j : ℕ) :
    prependPolarBasis c hcK a (n+j) = a j := by
  simp [prependPolarBasis, show ¬n+j < n by omega]

lemma denseRange_prependPolarBasis (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    DenseRange (prependPolarBasis c hcK a) := by
  apply ha.mono
  rintro p ⟨j, rfl⟩
  exact ⟨n+j, prependPolarBasis_tail c hcK a j⟩

/-- The first n terms of the sequence are linearly independent. -/
lemma linearIndependent_prependPolarBasis (c : ℝ) (hc : c ≠ 0)
    (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K) (a : ℕ → coordinatePolar K) :
    LinearIndependent ℝ (fun i : Fin n => (prependPolarBasis c hcK a i).val) := by
  simp only [prependPolarBasis_first]
  exact Pi.linearIndependent_single_of_ne_zero (fun _ => hc)

/-- The literal first n+N rows describe exactly the previously constructed compact approximants. -/
lemma prefix_stripBody_eq (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (N : ℕ) :
    stripBody (fun j : Fin (n+N) => (prependPolarBasis c hcK a j).val) =
      stripBody (approximationRows c (fun j => (a j).val) N) := by
  ext x
  rw [stripBody_approximationRows_mem]
  constructor
  · intro hx
    constructor
    · intro i
      have h := hx ⟨i.val, by omega⟩
      change |∑ k, (prependPolarBasis c hcK a i.val).val k * x k| ≤ 1 at h
      simpa [prependPolarBasis_first, Pi.single_apply] using h
    · intro j hj
      have h := hx ⟨n+j, by omega⟩
      simpa only [measurement, prependPolarBasis_tail] using h
  · rintro ⟨hb, hs⟩ j
    by_cases hj : j.val < n
    · change |∑ k, (prependPolarBasis c hcK a j.val).val k*x k| ≤ 1
      simpa [prependPolarBasis, hj, Pi.single_apply] using hb ⟨j.val, hj⟩
    · have hnj : n ≤ j.val := by omega
      have he : j.val = n + (j.val-n) := by omega
      change |∑ k, (prependPolarBasis c hcK a j.val).val k*x k| ≤ 1
      rw [he, prependPolarBasis_tail]
      exact hs (j.val-n) (by omega)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexMain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {n : ℕ} {K : Set (Fin n → ℝ)}

lemma measurement_prefix_injective (c : ℝ) (hc : c ≠ 0)
    (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K) (a : ℕ → coordinatePolar K)
    (N : ℕ) :
    Function.Injective (measurement (fun j : Fin (n+N) => (prependPolarBasis c hcK a j).val)) := by
  intro x y h
  ext i
  have hi := congrFun h ⟨i.val, by omega⟩
  have hi' : c*x i = c*y i := by
    simpa [measurement, prependPolarBasis, i.isLt, Pi.single_apply] using hi
  exact mul_left_cancel₀ hc hi'

/-- An approximation certificate for an arbitrary symmetric convex body.
The sequence and every geometric and measure property are
constructed from exactly the body hypotheses; no approximation premise remains.
Each prefix has N+n rows and contains the
independent first n rows. -/
theorem exists_finite_strip_approximation (_hn : 1 ≤ n) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ∃ a : ℕ → coordinatePolar K,
      DenseRange a ∧
      LinearIndependent ℝ (fun i : Fin n => (a i).val) ∧
      (∀ N, Function.Injective (measurement (fun j : Fin (n+N) => (a j).val))) ∧
      (∀ N, IsCompact (stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        Convex ℝ (stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        (∀ x ∈ stripBody (fun j : Fin (n+N) => (a j).val),
          -x ∈ stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        (interior (stripBody (fun j : Fin (n+N) => (a j).val))).Nonempty) ∧
      Antitone (fun N => stripBody (fun j : Fin (n+N) => (a j).val)) ∧
      (∀ N, K ⊆ stripBody (fun j : Fin (n+N) => (a j).val)) ∧
      (⋂ N, stripBody (fun j : Fin (n+N) => (a j).val)) = K ∧
      Tendsto (fun N => (volume (stripBody (fun j : Fin (n+N) => (a j).val))).toReal)
        atTop (𝓝 (volume K).toReal) ∧
      (∀ N, coordinatePolar (stripBody (fun j : Fin (n+N) => (a j).val)) ⊆ coordinatePolar K) := by
  have hz := zero_mem_interior_of_symmetric hconv hsym hint
  obtain ⟨c, hc, hcK⟩ := exists_coordinate_rows hK
  let : Nonempty (coordinatePolar K) := ⟨⟨0, zero_mem_coordinatePolar K⟩⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (coordinatePolar K)
  refine ⟨prependPolarBasis c hcK a, denseRange_prependPolarBasis c hcK a ha,
    linearIndependent_prependPolarBasis c hc.ne' hcK a,
    measurement_prefix_injective c hc.ne' hcK a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    rw [prefix_stripBody_eq]
    refine ⟨isCompact_approximation hc _ N, convex_stripBody _, symmetric_stripBody _, ?_⟩
    exact hint.mono (interior_mono (subset_approximation hsym c hcK a N))
  · simpa only [prefix_stripBody_eq] using approximation_antitone c (fun j => (a j).val)
  · intro N
    rw [prefix_stripBody_eq]
    exact subset_approximation hsym c hcK a N
  · simp only [prefix_stripBody_eq]
    exact iInter_approximation hconv hK.isClosed (interior_subset hz) hsym c hcK a ha
  · simp only [prefix_stripBody_eq]
    exact tendsto_volume_approximation hK hconv (interior_subset hz) hsym hc hcK a ha
  · intro N
    rw [prefix_stripBody_eq]
    exact coordinatePolar_antitone (subset_approximation hsym c hcK a N)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexPolarBody
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset
variable {I : Type*} [Fintype I] [decidableEqI : DecidableEq I]

omit decidableEqI in
lemma convex_coordinatePolar [DecidableEq I] (K : Set (I → ℝ)) : Convex ℝ (coordinatePolar K) := by
  intro p hp q hq a b ha hb hab x hx
  calc
    (∑ i, (a • p + b • q) i * x i) =
        a * (∑ i, p i*x i) + b * (∑ i, q i*x i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        sum_add_distrib, mul_sum]
      apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ a*1+b*1 := add_le_add
      (mul_le_mul_of_nonneg_left (hp x hx) ha) (mul_le_mul_of_nonneg_left (hq x hx) hb)
    _ = 1 := by linarith

omit decidableEqI in
lemma symmetric_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K) :
    ∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K := by
  intro p hp x hx
  have h := (abs_le.mp (polar_pairing_abs hsym hp hx)).1
  simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]
  linarith

omit decidableEqI in
/-- A compact K gives an open l1 neighborhood of zero inside the literal polar. -/
theorem zero_mem_interior_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hK : IsCompact K) :
    (0 : I → ℝ) ∈ interior (coordinatePolar K) := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  let S : Set (I → ℝ) := {p | (∑ i, |p i|) < R⁻¹}
  have hS : IsOpen S := isOpen_lt
    (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)) continuous_const
  have hz : (0 : I → ℝ) ∈ S := by simpa [S] using inv_pos.mpr hR
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hS.mem_nhds hz)
  intro p hp x hx
  calc
    (∑ i, p i*x i) ≤ ∑ i, |p i| * R := by
      apply sum_le_sum
      intro i _
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm x i).trans (hb x hx)) (abs_nonneg _)
    _ = (∑ i, |p i|)*R := by rw [sum_mul]
    _ ≤ 1 := by
      have h : (∑ i, |p i|) < 1/R := by simpa only [S, Set.mem_ofPred_eq, one_div] using hp
      exact ((lt_div_iff₀ hR).mp h).le

/-- The polar of an origin-symmetric convex body is again such a body. -/
theorem coordinatePolar_is_symmetric_convex_body {K : Set (I → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    IsCompact (coordinatePolar K) ∧ Convex ℝ (coordinatePolar K) ∧
      (∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K) ∧
      (interior (coordinatePolar K)).Nonempty :=
  ⟨isCompact_coordinatePolar hsym (zero_mem_interior_of_symmetric hconv hsym hint),
    convex_coordinatePolar K, symmetric_coordinatePolar hsym,
    ⟨0, zero_mem_interior_coordinatePolar hK⟩⟩

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripRankGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

omit fintypeJ in
lemma stripCoordinate_injective [Fintype J] (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) : Function.Injective (stripCoordinate A) := by
  intro z w h
  apply Prod.ext
  · apply hA
    funext j
    have := congrArg Complex.re (congrFun h j)
    simpa [stripCoordinate] using this
  · apply hA
    funext j
    have := congrArg Complex.im (congrFun h j)
    simpa [stripCoordinate] using this

/-- Rank n implies properness of the full complexified matrix. -/
theorem stripCoordinate_isClosedEmbedding (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) :
    Topology.IsClosedEmbedding (stripCoordinate A) :=
  (stripCoordinateLinear A).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (stripCoordinate_injective A hA))

/-- Compact coordinate constraints have compact inverse image, with no
additional boundedness assumption on z. -/
theorem stripCoordinate_compact_preimage (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {K : Set (J → ℂ)} (hK : IsCompact K) :
    IsCompact (stripCoordinate A ⁻¹' K) :=
  (stripCoordinate_isClosedEmbedding A hA).isCompact_preimage hK

@[simp] lemma zero_mem_stripDomain (A : J → I → ℝ) :
    (0 : (I → ℝ) × (I → ℝ)) ∈ stripDomain A := by
  intro j
  simpa only [stripCoordinate_zero, Pi.zero_apply] using zero_mem_Omega

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PlanarErrorRate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Filter
open scoped Topology

lemma planarError_nat_tendsto_zero :
    Tendsto (fun m : ℕ => planarError (m : ℝ)) atTop (𝓝 0) :=
  planarError_tendsto_zero.comp tendsto_natCast_atTop_atTop

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HannerBodies
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set MeasureTheory

namespace RealNormData
open MeasureTheory.Measure
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma unit_max (g : RealNormData E) (h : RealNormData F) :
    (g.max h).unit = g.unit ×ˢ h.unit := by ext x; simp [unit]

lemma convex_unit (g : RealNormData E) : Convex ℝ g.unit := by
  intro x hx y hy a b ha hb hab
  change g (a • x + b • y) ≤ 1
  calc
    g (a • x + b • y) ≤ g (a • x) + g (b • y) := g.add_le _ _
    _ = a * g x + b * g y := by rw [g.smul_eq, g.smul_eq, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by linarith

lemma unit_comap (g : RealNormData E) (e : F ≃ₗ[ℝ] E) :
    (g.comap e).unit = e.symm '' g.unit := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [unit, comap_apply, Set.mem_ofPred_eq, e.apply_symm_apply] using hy

variable [inst423 : TopologicalSpace E] [inst424 : IsTopologicalAddGroup E] [inst425 : T2Space E] [inst426 : ContinuousSMul ℝ E]
  [MeasurableSpace E] [inst428 : BorelSpace E] [inst429 : FiniteDimensional ℝ E] [inst430 : SecondCountableTopology E]
  [inst431 : TopologicalSpace F] [inst432 : IsTopologicalAddGroup F] [inst433 : T2Space F] [inst434 : ContinuousSMul ℝ F]
  [MeasurableSpace F] [inst436 : BorelSpace F] [inst437 : FiniteDimensional ℝ F] [inst438 : SecondCountableTopology F]

omit inst430 in
lemma measure_unit [SecondCountableTopology E] (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    μ g.unit = ENNReal.ofReal ((∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  rw [unit, MeasureTheory.measure_le_eq_lt μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) 1]
  have hh := MeasureTheory.measure_lt_one_eq_integral_div_gamma μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) (show (0:ℝ) < 1 by norm_num)
  simpa only [div_one, Real.rpow_one, Real.Gamma_nat_eq_factorial] using hh

lemma measureReal_unit (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    (μ g.unit).toReal = (∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ) := by
  rw [g.measure_unit μ, ENNReal.toReal_ofReal]
  exact div_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le) (by positivity)

lemma measureReal_unit_sum (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    [SigmaFinite μ] [SigmaFinite ν] [Nontrivial E] [Nontrivial F] :
    ((μ.prod ν) (g.sum h).unit).toReal =
      (Nat.factorial (Module.finrank ℝ E) : ℝ) * Nat.factorial (Module.finrank ℝ F) /
        Nat.factorial (Module.finrank ℝ E + Module.finrank ℝ F) *
      (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [(g.sum h).measureReal_unit, g.measureReal_unit, h.measureReal_unit]
  simp_rw [sum_apply, neg_add, Real.exp_add]
  rw [integral_prod_mul (μ := μ) (ν := ν) (fun x : E => Real.exp (-g x))
    (fun y : F => Real.exp (-h y)), Module.finrank_prod]
  have hE : (Nat.factorial (Module.finrank ℝ E) : ℝ) ≠ 0 := by positivity
  have hF : (Nat.factorial (Module.finrank ℝ F) : ℝ) ≠ 0 := by positivity
  field_simp

omit inst423 inst424 inst425 inst426 inst428 inst429 inst430 inst431 inst432 inst433 inst434 inst436 inst437 inst438 in
lemma measureReal_unit_max [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology E] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F] [ContinuousSMul ℝ F] [BorelSpace F] [FiniteDimensional ℝ F] [SecondCountableTopology F] (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [SigmaFinite ν] :
    ((μ.prod ν) (g.max h).unit).toReal = (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [unit_max, Measure.prod_prod, ENNReal.toReal_mul]

end RealNormData

lemma measurePreserving_appendEquiv (k l : ℕ) : MeasurePreserving (appendEquiv k l) := by
  let e₁ := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ)).symm
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : Fin (k+l) => ℝ) (finSumFinEquiv : Fin k ⊕ Fin l ≃ _)
  have h₁ : MeasurePreserving e₁ := volume_measurePreserving_sumPiEquivProdPi_symm _
  have h₂ : MeasurePreserving e₂ := volume_measurePreserving_piCongrLeft _ _
  convert h₂.comp h₁ using 1
  funext z i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
    simp [e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, appendEquiv]

lemma volume_appendEquiv_image {k l : ℕ} (S : Set ((Fin k → ℝ) × (Fin l → ℝ))) :
    volume (appendEquiv k l '' S) = volume S :=
  by
    have hh := (measurePreserving_appendEquiv k l).measure_preimage_emb
      (appendEquiv k l).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
      (appendEquiv k l '' S)
    rw [Set.preimage_image_eq _ (appendEquiv k l).injective] at hh
    exact hh.symm

lemma dot_append {k l : ℕ} (x p : Fin k → ℝ) (y q : Fin l → ℝ) :
    (∑ i, Fin.append p q i * Fin.append x y i) = (∑ i, p i*x i) + ∑ i, q i*y i := by
  rw [Fin.sum_univ_add]
  simp

namespace RealNormData

lemma volumeReal_unit_coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordMax h).unit).toReal = (volume g.unit).toReal * (volume h.unit).toReal := by
  rw [coordMax, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  exact g.measureReal_unit_max h volume volume

lemma volumeReal_unit_coordSum {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordSum h).unit).toReal = (Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) *
      (volume g.unit).toReal * (volume h.unit).toReal := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp hl
  rw [coordSum, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  change (((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin l → ℝ)))
    (g.sum h).unit).toReal = _
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
    g.measureReal_unit_sum h volume volume

lemma unit_interval (a : ℝ) (ha : 0 < a) :
    (interval a ha).unit = Icc (fun _ : Fin 1 => -a) (fun _ => a) := by
  ext x
  simp only [unit, Set.mem_ofPred_eq, interval_apply, div_le_one ha, abs_le, mem_Icc,
    Pi.le_def, Fin.forall_fin_one]

lemma volumeReal_unit_interval (a : ℝ) (ha : 0 < a) :
    (volume (interval a ha).unit).toReal = 2*a := by
  rw [unit_interval, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_one, sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith : 0 ≤ a+a)]
  ring

lemma IsDual.polar_unit {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) :
    coordinatePolar g.unit = h.unit := by
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,he⟩ := hd.2 p
    change h p ≤ 1
    rw [← he]
    exact hp x hx
  · intro hp x hx
    change h p ≤ 1 at hp
    exact (hd.1 x p).trans <|
      (mul_le_mul_of_nonneg_right hx (h.nonneg p)).trans (by simpa using hp)

lemma interval_isDual (a : ℝ) (ha : 0 < a) :
    (interval a ha).IsDual (interval a⁻¹ (inv_pos.mpr ha)) := by
  constructor
  · intro x p
    simp only [Fin.sum_univ_one, interval_apply, div_inv_eq_mul]
    calc
      p 0 * x 0 ≤ |p 0 * x 0| := le_abs_self _
      _ = |x 0| / a * (|p 0| * a) := by rw [abs_mul]; field_simp
  · intro p
    by_cases hp : 0 ≤ p 0
    · refine ⟨fun _ => a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_nonneg hp]
    · refine ⟨fun _ => -a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_neg (lt_of_not_ge hp)]

theorem IsDual.coordSum_max {k l : ℕ} {g g' : RealNormData (Fin k → ℝ)}
    {h h' : RealNormData (Fin l → ℝ)} (hg : g.IsDual g') (hh : h.IsDual h') :
    (g.coordSum h).IsDual (g'.coordMax h') := by
  constructor
  · intro x p
    obtain ⟨⟨x₁,x₂⟩,rfl⟩ := (appendEquiv k l).surjective x
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    simp only [appendEquiv_apply, coordMax_append, coordSum_append, dot_append]
    calc
      _ ≤ g x₁ * g' p₁ + h x₂ * h' p₂ := add_le_add (hg.1 _ _) (hh.1 _ _)
      _ ≤ g x₁ * Max.max (g' p₁) (h' p₂) + h x₂ * Max.max (g' p₁) (h' p₂) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (g.nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (h.nonneg _))
      _ = _ := by ring
  · intro p
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    obtain ⟨x,hx,hxp⟩ := hg.2 p₁
    obtain ⟨y,hy,hyp⟩ := hh.2 p₂
    rcases le_total (h' p₂) (g' p₁) with hp | hp
    · refine ⟨Fin.append x 0, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, add_zero] using hx
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, hxp, coordMax_append, max_eq_left hp]
    · refine ⟨Fin.append 0 y, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, zero_add] using hy
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          zero_add, hyp, coordMax_append, max_eq_right hp]

end RealNormData

lemma hanner_volume_recursion {k l : ℕ} {v v' w w' : ℝ}
    (h₁ : v*v' = (4:ℝ)^k / Nat.factorial k)
    (h₂ : w*w' = (4:ℝ)^l / Nat.factorial l) :
    (v*w) * ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) * v' * w') =
      (4:ℝ)^(k+l) / Nat.factorial (k+l) := by
  calc
    _ = ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l)) * (v*v') * (w*w') := by ring
    _ = _ := by
      rw [h₁, h₂, pow_add]
      have hfk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hfl : (Nat.factorial l : ℝ) ≠ 0 := by positivity
      field_simp

open Set Metric MeasureTheory
open scoped Topology Pointwise
namespace RealNormData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [inst443 : FiniteDimensional ℝ E]

lemma continuous (g : RealNormData E) : Continuous g := by
  exact continuous_norm.comp g.spaceEquiv.symm.toContinuousLinearEquiv.continuous

omit inst443 in
lemma unit_eq_image_closedBall [FiniteDimensional ℝ E] (g : RealNormData E) :
    g.unit = g.spaceEquiv '' closedBall (0:g.Space) 1 := by
  ext x
  constructor
  · intro hx
    exact ⟨g.spaceEquiv.symm x, by simpa only [mem_closedBall_zero_iff,space_norm,LinearEquiv.apply_symm_apply,unit,Set.mem_ofPred_eq] using hx, g.spaceEquiv.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [mem_closedBall_zero_iff,space_norm,unit,Set.mem_ofPred_eq] using hy

lemma isCompact_unit (g : RealNormData E) : IsCompact g.unit := by
  rw [g.unit_eq_image_closedBall]
  exact (isCompact_closedBall (0:g.Space) 1).image g.spaceEquiv.toContinuousLinearEquiv.continuous

lemma unit_nhds (g : RealNormData E) : g.unit ∈ 𝓝 (0:E) := by
  have hh : ∀ᶠ x in 𝓝 (0:E), g x < 1 :=
    (g.continuous.tendsto 0).eventually (Iio_mem_nhds (by simp))
  exact Filter.mem_of_superset hh (fun x hx => (show g x < 1 from hx).le)

omit inst443 in
lemma symmetric_unit [FiniteDimensional ℝ E] (g : RealNormData E) : ∀ x ∈ g.unit, -x ∈ g.unit := by
  intro x hx
  simpa only [unit,Set.mem_ofPred_eq,g.apply_neg] using hx

lemma interior_unit_nonempty (g : RealNormData E) : (interior g.unit).Nonempty :=
  ⟨0,mem_interior_iff_mem_nhds.mpr g.unit_nhds⟩

end RealNormData

lemma bodyNorm_unit {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hc : Convex ℝ B)
    (hs : ∀ x ∈ B, -x ∈ B) (hi : (interior B).Nonempty) :
    (bodyNorm hB hc hs hi).unit = B := by
  ext x
  change gauge B x ≤ 1 ↔ x ∈ B
  rw [gauge_le_one_iff_mem_closure hc (body_nhds_zero hc hs hi),hB.isClosed.closure_eq]

namespace RealNormData
open Finset

lemma dot_continuous {n : ℕ} (p : Fin n → ℝ) : Continuous (fun x : Fin n → ℝ => ∑ i, p i*x i) := by
  fun_prop

theorem isDual_of_polar {n : ℕ} (g h : RealNormData (Fin n → ℝ))
    (hpolar : coordinatePolar g.unit = h.unit) : g.IsDual h := by
  have hupper (p x : Fin n → ℝ) : (∑ i, p i*x i) ≤ g x * h p := by
    by_cases hp : p = 0
    · simp [hp]
    by_cases hx : x = 0
    · simp [hx]
    have hpp : 0 < h p := lt_of_le_of_ne (h.nonneg _) (Ne.symm (h.eq_zero.not.mpr hp))
    have hxx : 0 < g x := lt_of_le_of_ne (g.nonneg _) (Ne.symm (g.eq_zero.not.mpr hx))
    have hpu : (h p)⁻¹ • p ∈ coordinatePolar g.unit := by
      rw [hpolar]
      change h ((h p)⁻¹ • p) ≤ 1
      rw [h.smul_eq,abs_of_pos (inv_pos.mpr hpp),inv_mul_cancel₀ hpp.ne']
    have hxu : (g x)⁻¹ • x ∈ g.unit := by
      change g ((g x)⁻¹ • x) ≤ 1
      rw [g.smul_eq,abs_of_pos (inv_pos.mpr hxx),inv_mul_cancel₀ hxx.ne']
    have hb := hpu _ hxu
    have hb' : (h p)⁻¹ * (g x)⁻¹ * (∑ i, p i*x i) ≤ 1 := by
      have he : (∑ i, ((h p)⁻¹ • p) i * ((g x)⁻¹ • x) i) =
          (h p)⁻¹ * (g x)⁻¹ * (∑ i, p i*x i) := by
        simp only [Pi.smul_apply,smul_eq_mul, mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
      rwa [he] at hb
    have ht := mul_le_mul_of_nonneg_left hb' (mul_nonneg hpp.le hxx.le)
    field_simp at ht
    nlinarith
  refine ⟨fun x p => hupper p x,?_⟩
  intro p
  obtain ⟨x,hx,hmax⟩ := g.isCompact_unit.exists_isMaxOn
    (show g.unit.Nonempty from ⟨0,by simp [unit]⟩) (dot_continuous p).continuousOn
  let t : ℝ := ∑ i, p i*x i
  have ht0 : 0 ≤ t := by
    have hh := hmax (show (0:Fin n → ℝ) ∈ g.unit by simp [unit])
    change (∑ i, p i*(0:Fin n → ℝ) i) ≤ t at hh
    simpa only [Pi.zero_apply,mul_zero,sum_const_zero] using hh
  have htt : t ≤ h p := by
    exact (hupper p x).trans ((mul_le_mul_of_nonneg_right hx (h.nonneg _)).trans_eq (one_mul _))
  have hpt : h p ≤ t := by
    by_contra hnot
    have hlt : t < h p := lt_of_not_ge hnot
    let r : ℝ := (t+h p)/2
    have hr : 0 < r := by dsimp [r]; linarith
    have htr : t < r := by dsimp [r]; linarith
    have hrp : r < h p := by dsimp [r]; linarith
    have hpunit : r⁻¹ • p ∈ coordinatePolar g.unit := by
      intro y hy
      have hy' : (∑ i, p i*y i) ≤ t := hmax hy
      simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]
      exact (inv_mul_le_iff₀ hr).mpr (by linarith)
    rw [hpolar] at hpunit
    change h (r⁻¹ • p) ≤ 1 at hpunit
    rw [h.smul_eq,abs_of_pos (inv_pos.mpr hr)] at hpunit
    have hh := (inv_mul_le_iff₀ hr).mp hpunit
    linarith
  exact ⟨x,hx,le_antisymm htt hpt⟩

end RealNormData

open Set Finset MeasureTheory

lemma coordinatePolar_bipolar {n : ℕ} {B : Set (Fin n → ℝ)}
    (hc : Convex ℝ B) (hclosed : IsClosed B) (hzero : (0:Fin n → ℝ) ∈ B) :
    coordinatePolar (coordinatePolar B) = B := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨p,hp,hpx⟩ := exists_coordinatePolar_separator hc hclosed hzero hnot
    have hle := hx p hp
    have he : (∑ i, x i*p i) = ∑ i, p i*x i := by apply sum_congr rfl; intro i hi; ring
    rw [he] at hle
    linarith
  · intro hx p hp
    simpa only [mul_comm] using hp x hx

namespace RealNormData
lemma IsDual.symm {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) : h.IsDual g := by
  apply h.isDual_of_polar g
  rw [← hd.polar_unit,coordinatePolar_bipolar g.convex_unit g.isCompact_unit.isClosed g.zero_mem_unit]

lemma coordinate_of_dual {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (f : h.Space →L[ℝ] ℝ) :
    ∃ u : Fin n → ℝ, g u ≤ ‖f‖ ∧ ∀ p : h.Space,
      f p = ∑ i, (h.spaceEquiv p) i * u i := by
  let F : (Fin n → ℝ) →L[ℝ] ℝ :=
    f.comp h.spaceEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let u : Fin n → ℝ := fun i => F (Pi.single i 1)
  have he (p : h.Space) : f p = ∑ i, (h.spaceEquiv p) i*u i := by
    have hh := pairing_of_dual F (h.spaceEquiv p)
    change (∑ i, u i * (h.spaceEquiv p) i) = f (h.spaceEquiv.symm (h.spaceEquiv p)) at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    simpa only [mul_comm] using hh.symm
  refine ⟨u,?_,he⟩
  obtain ⟨p,hp,hpu⟩ := hd.symm.2 u
  have hn : ‖h.spaceEquiv.symm p‖ ≤ 1 := by simpa only [space_norm,LinearEquiv.apply_symm_apply,unit,Set.mem_ofPred_eq] using hp
  have hh := (le_abs_self (f (h.spaceEquiv.symm p))).trans ((f.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg f)).trans_eq (mul_one _)))
  rw [he] at hh
  simp only [LinearEquiv.apply_symm_apply] at hh
  rw [← hpu]
  simpa only [mul_comm] using hh

lemma equality_segment_lift {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    let c := interval 1 (by norm_num : (0:ℝ) < 1)
    (g.coordSum c).IsDual (h.coordMax c) ∧
      (volume (g.coordSum c).unit).toReal * (volume (h.coordMax c).unit).toReal =
        (4:ℝ)^(n+1)/Nat.factorial (n+1) := by
  intro c
  have hc : c.IsDual c := by simpa only [inv_one] using interval_isDual 1 (by norm_num)
  refine ⟨hd.coordSum_max hc,?_⟩
  rw [volumeReal_unit_coordSum hn (by norm_num),volumeReal_unit_coordMax,volumeReal_unit_interval]
  have heq' : (volume h.unit).toReal * (volume g.unit).toReal = (4:ℝ)^n/Nat.factorial n := by
    simpa only [mul_comm] using heq
  have hh := hanner_volume_recursion heq' (show (2:ℝ)*(2:ℝ)=(4:ℝ)^1/Nat.factorial 1 by norm_num)
  convert hh using 1 <;> first | rfl | ring

end RealNormData

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Medians
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem median_of_aggregate_decomposition (x y rp rm : E)
    (hadd : rp + rm = x - y)
    (hp : ‖rp‖ ≤ (‖x-y‖ + ‖x‖ - ‖y‖)/2)
    (hm : ‖rm‖ ≤ (‖x-y‖ - ‖x‖ + ‖y‖)/2)
    (hrem : ‖x+y-(rp-rm)‖ ≤ ‖x‖ + ‖y‖ - ‖x-y‖) :
    ∃ m : E, ‖x‖ = ‖m‖ + ‖x-m‖ ∧ ‖y‖ = ‖m‖ + ‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖ + ‖m-y‖ := by
  let m := x-rp
  have hx : x-m = rp := by dsimp [m]; abel
  have hy : m-y = rm := by
    calc
      _ = (x-y)-rp := by dsimp [m]; abel
      _ = (rp+rm)-rp := by rw [hadd]
      _ = rm := by abel
  have htwo : x+y-(rp-rm) = (2 : ℝ) • m := by
    have hy' : y = x-(rp+rm) := by rw [hadd]; abel
    rw [hy']
    dsimp [m]
    module
  have hmn : ‖m‖ ≤ (‖x‖ + ‖y‖ - ‖x-y‖)/2 := by
    rw [htwo, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hrem
    linarith
  have hxt : ‖x‖ ≤ ‖m‖ + ‖rp‖ := by
    have := norm_add_le m rp
    have he : m+rp = x := by dsimp [m]; abel
    simpa [he] using this
  have hyt : ‖y‖ ≤ ‖m‖ + ‖rm‖ := by
    have := norm_sub_le m rm
    have he : m-rm = y := by rw [← hy]; abel
    simpa [he] using this
  have hpt : ‖x-y‖ ≤ ‖rp‖ + ‖rm‖ := by
    rw [← hadd]
    exact norm_add_le _ _
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [hx]; linarith
  · rw [← norm_neg (y-m), neg_sub, hy]; linarith
  · rw [hx, hy]; linarith

end

section
open Set Metric
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [inst449 : NormedSpace ℝ E]

omit inst449 in
lemma aggregateSet_eq_image [NormedSpace ℝ E] (w : E) (A B : ℝ) :
    aggregateSet w A B = (fun r : E × E => r.1 - r.2) ''
      ((closedBall (0 : E) A ×ˢ closedBall (0 : E) B) ∩
        {r : E × E | r.1 + r.2 = w}) := by
  ext z
  simp only [aggregateSet, Set.mem_ofPred_eq, mem_image, mem_inter_iff, mem_prod,
    mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨rp, rm, hadd, hp, hm, rfl⟩
    exact ⟨(rp, rm), ⟨⟨hp, hm⟩, hadd⟩, rfl⟩
  · rintro ⟨⟨rp, rm⟩, ⟨⟨hp, hm⟩, hadd⟩, rfl⟩
    exact ⟨rp, rm, hadd, hp, hm, rfl⟩

lemma isCompact_aggregateSet [FiniteDimensional ℝ E] (w : E) (A B : ℝ) :
    IsCompact (aggregateSet w A B) := by
  rw [aggregateSet_eq_image]
  exact (((isCompact_closedBall (0 : E) A).prod (isCompact_closedBall (0 : E) B)).inter_right
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)).image
      (continuous_fst.sub continuous_snd)

lemma convex_aggregateSet (w : E) (A B : ℝ) : Convex ℝ (aggregateSet w A B) := by
  intro z hz v hv a b ha hb hab
  rcases hz with ⟨zp, zm, hzadd, hzp, hzm, rfl⟩
  rcases hv with ⟨vp, vm, hvadd, hvp, hvm, rfl⟩
  refine ⟨a • zp + b • vp, a • zm + b • vm, ?_, ?_, ?_, ?_⟩
  · calc
      _ = a • (zp + zm) + b • (vp + vm) := by module
      _ = w := by rw [hzadd, hvadd, ← add_smul, hab, one_smul]
  · calc
      _ ≤ ‖a • zp‖ + ‖b • vp‖ := norm_add_le _ _
      _ = a * ‖zp‖ + b * ‖vp‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * A + b * A := add_le_add (mul_le_mul_of_nonneg_left hzp ha)
        (mul_le_mul_of_nonneg_left hvp hb)
      _ = A := by rw [← add_mul, hab, one_mul]
  · calc
      _ ≤ ‖a • zm‖ + ‖b • vm‖ := norm_add_le _ _
      _ = a * ‖zm‖ + b * ‖vm‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := add_le_add (mul_le_mul_of_nonneg_left hzm ha)
        (mul_le_mul_of_nonneg_left hvm hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  · module

lemma exists_unitBall_dual_maximizer [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ ≤ 1 ∧ f v = ‖f‖ := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (nonempty_closedBall.mpr (by norm_num)) f.continuous.continuousOn
  have hvnorm : ‖v‖ ≤ 1 := by simpa using hv
  have hfv : 0 ≤ f v := by
    have := hmax (by simp : (0 : E) ∈ closedBall 0 1)
    simpa using this
  have hupper (x : E) : f x ≤ f v * ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnx.le),
        inv_mul_cancel₀ hnx.ne']
    have hh := hmax (by simpa using hunit)
    have hh' : ‖x‖⁻¹ * f x ≤ f v := by simpa using hh
    have := mul_le_mul_of_nonneg_left hh' hnx.le
    simpa [← mul_assoc, hnx.ne', mul_comm] using this
  have hop : ‖f‖ ≤ f v := by
    apply f.opNorm_le_bound hfv
    intro x
    rw [Real.norm_eq_abs, abs_le]
    have hneg := hupper (-x)
    simp only [map_neg, norm_neg] at hneg
    exact ⟨by linarith, hupper x⟩
  refine ⟨v, hvnorm, le_antisymm ?_ hop⟩
  calc
    f v ≤ ‖f v‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
    _ ≤ ‖f‖ := by simpa using mul_le_mul_of_nonneg_left hvnorm (norm_nonneg f)

lemma aggregate_decomposition_of_support [FiniteDimensional ℝ E]
    (w t : E) (A B R : ℝ) (hR : 0 ≤ R)
    (hsupport : ∀ (f : E →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      ∃ z ∈ aggregateSet w A B, f t ≤ f z + R * ‖f‖ + ε) :
    ∃ rp rm : E, rp + rm = w ∧ ‖rp‖ ≤ A ∧ ‖rm‖ ≤ B ∧
      ‖t - (rp-rm)‖ ≤ R := by
  let S := aggregateSet w A B + closedBall (0 : E) R
  have hc : IsCompact S := (isCompact_aggregateSet w A B).add (isCompact_closedBall 0 R)
  have hv : Convex ℝ S := (convex_aggregateSet w A B).add (convex_closedBall 0 R)
  have ht : t ∈ S := by
    by_contra hnot
    obtain ⟨f, u, hsep, hut⟩ := geometric_hahn_banach_closed_point hv hc.isClosed hnot
    obtain ⟨z, hz, hfz⟩ := hsupport f ((f t - u) / 2) (by linarith)
    obtain ⟨v, hv, hfv⟩ := exists_unitBall_dual_maximizer f
    have hRv : R • v ∈ closedBall (0 : E) R := by
      simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hR]
      simpa using mul_le_mul_of_nonneg_left hv hR
    have hmem : z + R • v ∈ S := Set.add_mem_add hz hRv
    have hh := hsep (z + R • v) hmem
    simp only [map_add, map_smul, smul_eq_mul, hfv] at hh
    linarith
  obtain ⟨z, ⟨rp, rm, hadd, hp, hm, rfl⟩, v, hv, he⟩ := Set.mem_add.mp ht
  refine ⟨rp, rm, hadd, hp, hm, ?_⟩
  have htv : t - (rp-rm) = v := by rw [← he]; abel
  simpa [htv] using hv

lemma median_of_aggregate_support [FiniteDimensional ℝ E] (x y : E)
    (hsupport : ∀ (f : E →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      ∃ z ∈ aggregateSet (x-y) ((‖x-y‖ + ‖x‖ - ‖y‖)/2)
        ((‖x-y‖ - ‖x‖ + ‖y‖)/2),
        f (x+y) ≤ f z + (‖x‖ + ‖y‖ - ‖x-y‖) * ‖f‖ + ε) :
    ∃ m : E, ‖x‖ = ‖m‖ + ‖x-m‖ ∧ ‖y‖ = ‖m‖ + ‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖ + ‖m-y‖ := by
  obtain ⟨rp, rm, hadd, hp, hm, hrem⟩ := aggregate_decomposition_of_support (x-y) (x+y)
    ((‖x-y‖ + ‖x‖ - ‖y‖)/2) ((‖x-y‖ - ‖x‖ + ‖y‖)/2)
    (‖x‖ + ‖y‖ - ‖x-y‖) (by linarith [norm_sub_le x y]) hsupport
  exact median_of_aggregate_decomposition x y rp rm hadd hp hm hrem

end

section
open Set Metric Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SignedUnitRepresentation
variable {q : E} {a T : ℝ} (R : SignedUnitRepresentation q a T)

lemma plus_add_minus : R.plus + R.minus = q := by
  calc
    R.plus + R.minus = ∑ i, R.weight i • R.point i := by
      rw [plus, minus, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      rw [← add_smul]
      congr 1
      ring
    _ = q := R.sum_point

lemma plus_norm : ‖R.plus‖ ≤ (T+a)/2 := by
  calc
    _ ≤ ∑ i, ‖((1+R.sign i)/2*R.weight i) • R.point i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1+R.sign i)/2 * R.weight i := by
      apply sum_le_sum
      intro i hi
      have hc : 0 ≤ (1+R.sign i)/2 * R.weight i := by
        rcases R.sign_eq i with h | h <;> rw [h] <;> nlinarith [R.weight_nonneg i]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (R.point_norm i) hc).trans_eq (mul_one _)
    _ = _ := by
      simp_rw [show ∀ i, (1+R.sign i)/2 * R.weight i =
        (R.weight i + R.weight i*R.sign i)/2 by intro i; ring]
      rw [← sum_div, sum_add_distrib, R.sum_weight, R.sum_sign]

lemma minus_norm : ‖R.minus‖ ≤ (T-a)/2 := by
  calc
    _ ≤ ∑ i, ‖((1-R.sign i)/2*R.weight i) • R.point i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1-R.sign i)/2 * R.weight i := by
      apply sum_le_sum
      intro i hi
      have hc : 0 ≤ (1-R.sign i)/2 * R.weight i := by
        rcases R.sign_eq i with h | h <;> rw [h] <;> nlinarith [R.weight_nonneg i]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (R.point_norm i) hc).trans_eq (mul_one _)
    _ = _ := by
      simp_rw [show ∀ i, (1-R.sign i)/2 * R.weight i =
        (R.weight i - R.weight i*R.sign i)/2 by intro i; ring]
      rw [← sum_div, sum_sub_distrib, R.sum_weight, R.sum_sign]

lemma eval_difference (u : E →L[ℝ] ℝ) :
    u (R.plus - R.minus) = ∑ i, R.weight i * R.sign i * u (R.point i) := by
  simp only [plus, minus, map_sub, map_sum, map_smul, smul_eq_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

lemma difference_mem : R.plus - R.minus ∈ aggregateSet q ((T+a)/2) ((T-a)/2) :=
  ⟨R.plus, R.minus, R.plus_add_minus, R.plus_norm, R.minus_norm, rfl⟩

end SignedUnitRepresentation

lemma endpoint_factor_mem {u : E →L[ℝ] ℝ} {b : E} {σ : ℝ}
    (hb : ‖b‖ ≤ 1) (hσ : σ = 1 ∨ σ = -1) :
    1-σ*u b ∈ Icc (1-‖u‖) (1+‖u‖) := by
  have hu : |u b| ≤ ‖u‖ := by
    exact (u.le_opNorm b).trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg u)).trans_eq
      (mul_one _))
  rcases abs_le.mp hu with ⟨hl,hr⟩
  rcases hσ with rfl | rfl <;> constructor <;> linarith

namespace SignedUnitRepresentation
variable {q : E} {a T : ℝ} (R : SignedUnitRepresentation q a T)

lemma cost_error {ell : ℝ → ℝ} {u : E →L[ℝ] ℝ} {δ ε : ℝ}
    (herr : ∀ c ∈ Icc (1-‖u‖) (1+‖u‖),
        |ell (1-δ*c) / ell (1-δ) - c| ≤ ε) :
    |R.cost ell u δ / ell (1-δ) - (T-u (R.plus-R.minus))| ≤ T * ε := by
  have he : R.cost ell u δ / ell (1-δ) - (T-u (R.plus-R.minus)) =
      ∑ i, R.weight i * (liftedLensCost ell u δ (R.point i) (R.sign i) / ell (1-δ) -
        (1-R.sign i*u (R.point i))) := by
    have hc : T-u (R.plus-R.minus) = ∑ i, R.weight i *
        (1-R.sign i*u (R.point i)) := by
      rw [R.eval_difference]
      simp only [mul_sub, mul_one, ← mul_assoc, sum_sub_distrib, R.sum_weight]
    rw [hc, cost, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |R.weight i * (liftedLensCost ell u δ (R.point i) (R.sign i) / ell (1-δ) -
        (1-R.sign i*u (R.point i)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, R.weight i * ε := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (R.weight_nonneg i)]
      exact mul_le_mul_of_nonneg_left
        (herr _ (endpoint_factor_mem (R.point_norm i) (R.sign_eq i))) (R.weight_nonneg i)
    _ = T*ε := by rw [← sum_mul, R.sum_weight]

end SignedUnitRepresentation

lemma medianCompetitor_difference {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    (medianCompetitor hx hy).plus - (medianCompetitor hx hy).minus = x+y := by
  dsimp [SignedUnitRepresentation.plus, SignedUnitRepresentation.minus, medianCompetitor]
  simp [Fin.sum_univ_two, smul_smul, hx, hy]

lemma aggregate_support_interior_of_optimal
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (u : E →L[ℝ] ℝ) (hu : ‖u‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ z ∈ aggregateSet (x-y) ((‖x-y‖+‖x‖-‖y‖)/2) ((‖x-y‖-‖x‖+‖y‖)/2),
      u (x+y) ≤ u z + (‖x‖+‖y‖-‖x-y‖) + ε := by
  have hp : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hs : 0 < ‖x‖+‖y‖+‖x-y‖ := by positivity
  let η := ε / (‖x‖+‖y‖+‖x-y‖)
  obtain ⟨δ,hδ,hδ1,hellδ,herr⟩ := hell (1-‖u‖) (1+‖u‖)
    (by linarith) (by linarith [norm_nonneg u]) η (div_pos hε hs)
  have hmax : max ‖x-y‖ |‖x‖-‖y‖| = ‖x-y‖ :=
    max_eq_left (abs_norm_sub_norm_le x y)
  obtain ⟨R,hR⟩ := hopt u hu δ hδ hδ1 (x-y) (‖x‖-‖y‖) (sub_ne_zero.mpr hxy)
  have hcost := div_le_div_of_nonneg_right (hR _ (medianCompetitor hx hy)) hellδ.le
  have hrerr := (abs_le.mp (R.cost_error herr)).1
  have hserr := (abs_le.mp ((medianCompetitor hx hy).cost_error herr)).2
  rw [medianCompetitor_difference] at hserr
  change R.cost ell u δ / ell (1-δ) ≤ (medianCompetitor hx hy).cost ell u δ / ell (1-δ) at hcost
  have hz := R.difference_mem
  simp only [hmax] at hz hrerr
  refine ⟨R.plus-R.minus, ?_, ?_⟩
  · convert hz using 1 ; congr 2 <;> ring
  · have he : (‖x‖+‖y‖+‖x-y‖)*η = ε := mul_div_cancel₀ _ hs.ne'
    nlinarith

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [inst459 : NormedSpace ℝ E]

lemma aggregate_support_of_optimal
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (f : E →L[ℝ] ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z ∈ aggregateSet (x-y) ((‖x-y‖+‖x‖-‖y‖)/2) ((‖x-y‖-‖x‖+‖y‖)/2),
      f (x+y) ≤ f z + (‖x‖+‖y‖-‖x-y‖)*‖f‖ + ε := by
  let R := ‖x‖+‖y‖-‖x-y‖
  have hR : 0 ≤ R := sub_nonneg.mpr (norm_sub_le x y)
  let d := ε / (2*(R+1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hd' : d*(R+1) = ε/2 := by dsimp [d]; field_simp
  let L := ‖f‖+d
  have hL : 0 < L := add_pos_of_nonneg_of_pos (norm_nonneg f) hd
  let u : E →L[ℝ] ℝ := L⁻¹ • f
  have hu : ‖u‖ < 1 := by
    rw [show ‖u‖ = L⁻¹ * ‖f‖ by simp [u, norm_smul, abs_of_pos hL]]
    rw [← div_eq_inv_mul]
    exact (div_lt_one hL).mpr (by dsimp [L]; linarith)
  let η := ε/(2*L)
  have hη : 0 < η := div_pos hε (by positivity)
  have hη' : L*η = ε/2 := by dsimp [η]; field_simp
  obtain ⟨z,hz,hbound⟩ := aggregate_support_interior_of_optimal hell hopt hx hy hxy u hu η hη
  have hev (v : E) : L*u v = f v := by simp [u, hL.ne']
  have hh : f (x+y) ≤ f z + L*R + ε/2 := by
    calc
      _ = L*u (x+y) := (hev _).symm
      _ ≤ L*(u z+R+η) := mul_le_mul_of_nonneg_left hbound hL.le
      _ = _ := by rw [mul_add, mul_add, hev, hη']
  refine ⟨z,hz,?_⟩
  dsimp only [L] at hh
  change f (x+y) ≤ f z + R*‖f‖ + ε
  nlinarith

theorem zero_median_of_optimal [FiniteDimensional ℝ E]
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    (x y : E) :
    ∃ m : E, ‖x‖ = ‖m‖+‖x-m‖ ∧ ‖y‖ = ‖m‖+‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖+‖m-y‖ := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp⟩
  by_cases hxy : x = y
  · subst y
    exact ⟨x, by simp⟩
  exact median_of_aggregate_support x y (aggregate_support_of_optimal hell hopt hx hy hxy)

omit inst459 in
lemma metricMedians_of_zero_medians [NormedSpace ℝ E]
    (h : ∀ x y : E, ∃ m : E, ‖x‖ = ‖m‖+‖x-m‖ ∧ ‖y‖ = ‖m‖+‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖+‖m-y‖) : HasMetricMedians E := by
  intro v
  obtain ⟨m,h1,h2,h12⟩ := h (v 1-v 0) (v 2-v 0)
  let M := m + v 0
  have h0 : ‖v 0-M‖ = ‖m‖ := by simp [M, show v 0-(m+v 0) = -m by abel]
  have hi (i : Fin 3) : v i-M = (v i-v 0)-m := by dsimp [M]; abel
  have he : (v 1-v 0)-(v 2-v 0) = v 1-v 2 := by abel
  have h01 : dist (v 0) (v 1) = dist (v 0) M + dist M (v 1) := by
    simpa only [dist_eq_norm, norm_sub_rev (v 0) (v 1), h0, norm_sub_rev M (v 1), hi, sub_self, zero_sub, norm_neg] using h1
  have h02 : dist (v 0) (v 2) = dist (v 0) M + dist M (v 2) := by
    simpa only [dist_eq_norm, norm_sub_rev (v 0) (v 2), h0, norm_sub_rev M (v 2), hi, sub_self, zero_sub, norm_neg] using h2
  have h1' : ‖m-(v 2-v 0)‖ = ‖M-v 2‖ := by congr 1; dsimp [M]; abel
  have h12' : dist (v 1) (v 2) = dist (v 1) M + dist M (v 2) := by
    simpa only [dist_eq_norm, hi, he, h1'] using h12
  have rev (a b : E) (h : dist a b = dist a M + dist M b) :
      dist b a = dist b M + dist M a := by
    calc
      dist b a = dist a b := dist_comm _ _
      _ = dist a M + dist M b := h
      _ = dist b M + dist M a := by rw [dist_comm a M, dist_comm M b, add_comm]
  refine ⟨M,?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hij rfl)
    | exact h01
    | exact h02
    | exact h12'
    | exact rev _ _ h01
    | exact rev _ _ h02
    | exact rev _ _ h12'

theorem metricMedians_of_optimal_lift [FiniteDimensional ℝ E]
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E) :
    HasMetricMedians E := metricMedians_of_zero_medians (zero_median_of_optimal hell hopt)

end SymmetricMahler
end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Lens
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

section
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SignedUnitRepresentation

lemma ofFintype_cost {ι : Type*} [Fintype ι] {q : E} {a T : ℝ}
    (b : ι → E) (s w : ι → ℝ) (hb : ∀ i, ‖b i‖ ≤ 1)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hw : ∀ i, 0 ≤ w i)
    (hq : ∑ i, w i • b i = q) (ha : ∑ i, w i*s i = a) (hT : ∑ i, w i = T)
    (ell : ℝ → ℝ) (u : E →L[ℝ] ℝ) (δ : ℝ) :
    (ofFintype b s w hb hs hw hq ha hT).cost ell u δ =
      ∑ i, w i * liftedLensCost ell u δ (b i) (s i) := by
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => w i * liftedLensCost ell u δ (b i) (s i))
end SignedUnitRepresentation

lemma lifted_cost_eq {ell : ℝ → ℝ} (heven : ∀ t, ell (-t) = ell t)
    (u : E →L[ℝ] ℝ) (δ : ℝ) (b : E) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    liftedLensCost ell u δ b s = ell (δ*u b+(1-δ)*s) := by
  rcases hs with rfl | rfl
  · dsimp [liftedLensCost]
    congr 1
    ring
  · rw [liftedLensCost, ← heven (δ*u b+(1-δ)*(-1))]
    congr 1; ring

lemma lens_face_interval (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {b : E} (hb : ‖b‖ ≤ 1)
    {s : ℝ} (hs : |s| ≤ 1) : δ*u b+(1-δ)*s ∈ Icc (-1:ℝ) 1 := by
  have hub : |u b| ≤ 1 := (u.le_opNorm b).trans
    ((mul_le_mul hu hb (norm_nonneg b) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _))
  have hbound : |δ*u b+(1-δ)*s| ≤ 1 := by
    calc
      _ ≤ |δ*u b|+|(1-δ)*s| := abs_add_le _ _
      _ = δ*|u b|+(1-δ)*|s| := by rw [abs_mul,abs_mul,abs_of_nonneg hδ,abs_of_nonneg (sub_nonneg.mpr hδ1)]
      _ ≤ δ*1+(1-δ)*1 := add_le_add (mul_le_mul_of_nonneg_left hub hδ)
        (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hδ1))
      _ = 1 := by ring
  exact abs_le.mp hbound

theorem optimal_signed_of_common_lens
    {ell : ℝ → ℝ} (heven : ∀ t, ell (-t) = ell t)
    (hconcave : ConcaveOn ℝ (Icc (-1:ℝ) 1) ell)
    (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {q : E} {a T : ℝ} (hT : 0 < T) (L : (E × ℝ) →ₗ[ℝ] ℝ)
    (hbound : ∀ b : E, ‖b‖ ≤ 1 → ∀ s : ℝ, |s| ≤ 1 →
      L (b,s) ≤ ell (δ*u b+(1-δ)*s))
    (hcontact : (T⁻¹ • q, T⁻¹*a) ∈ convexHull ℝ
      {z : E × ℝ | ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1 ∧ L z = ell (δ*u z.1+(1-δ)*z.2)}) :
    ∃ R : SignedUnitRepresentation q a T,
      ∀ U : ℝ, ∀ S : SignedUnitRepresentation q a U, R.cost ell u δ ≤ S.cost ell u δ := by
  classical
  obtain ⟨ι,_,z,w,hz,_,hw,hw1,heq⟩ := eq_pos_convex_span_of_mem_convexHull hcontact
  have hz' (i : ι) := hz (mem_range_self i)
  let b : ι × Fin 2 → E := fun i => (z i.1).1
  let s : ι × Fin 2 → ℝ := fun i => if i.2 = 0 then 1 else -1
  let v : ι × Fin 2 → ℝ := fun i => T*w i.1 * ((1+s i*(z i.1).2)/2)
  have hb (i : ι × Fin 2) : ‖b i‖ ≤ 1 := (hz' i.1).1
  have hs (i : ι × Fin 2) : s i = 1 ∨ s i = -1 := by
    dsimp [s]; split <;> simp
  have hv (i : ι × Fin 2) : 0 ≤ v i := by
    have hzi := abs_le.mp (hz' i.1).2.1
    rcases hs i with hh | hh <;> dsimp only [v] <;> rw [hh] <;>
      exact mul_nonneg (mul_nonneg hT.le (hw _).le) (by linarith)
  have heq1 : ∑ i, w i • (z i).1 = T⁻¹ • q := by
    simpa only [Prod.fst_sum,Prod.smul_fst] using congrArg Prod.fst heq
  have heq2 : ∑ i, w i*(z i).2 = T⁻¹*a := by
    simpa only [Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd heq
  have hvq : ∑ i, v i • b i = q := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,b,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul]
    simp_rw [← add_smul, show ∀ i, T*w i*((1+(z i).2)/2)+T*w i*((1+ -(z i).2)/2) = T*w i by intro i; ring]
    simp_rw [mul_smul]
    rw [← smul_sum, heq1, smul_smul, mul_inv_cancel₀ hT.ne',one_smul]
  have hva : ∑ i, v i*s i = a := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul,mul_one,mul_neg_one]
    simp_rw [show ∀ i, T*w i*((1+(z i).2)/2)+ -(T*w i*((1+ -(z i).2)/2)) = T*(w i*(z i).2) by intro i; ring]
    rw [← mul_sum,heq2,← mul_assoc,mul_inv_cancel₀ hT.ne',one_mul]
  have hvT : ∑ i, v i = T := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul]
    simp_rw [show ∀ i, T*w i*((1+(z i).2)/2)+T*w i*((1+ -(z i).2)/2) = T*w i by intro i; ring]
    rw [← mul_sum,hw1,mul_one]
  let R := SignedUnitRepresentation.ofFintype b s v hb hs hv hvq hva hvT
  have hR : R.cost ell u δ ≤ L (q,a) := by
    rw [SignedUnitRepresentation.ofFintype_cost]
    have hli (i : ι) :
        ((1+(z i).2)/2)*ell (δ*u (z i).1+(1-δ)) +
        ((1-(z i).2)/2)*ell (δ*u (z i).1-(1-δ)) ≤ L (z i) := by
      have hzi := abs_le.mp (hz' i).2.1
      have hh := hconcave.2
        (lens_face_interval u hu hδ hδ1 (hz' i).1 (by norm_num : |(1:ℝ)| ≤ 1))
        (lens_face_interval u hu hδ hδ1 (hz' i).1 (by norm_num : |(-1:ℝ)| ≤ 1))
        (show 0 ≤ (1+(z i).2)/2 by linarith) (show 0 ≤ (1-(z i).2)/2 by linarith)
        (show (1+(z i).2)/2+(1-(z i).2)/2 = 1 by ring)
      rw [(hz' i).2.2]
      simp only [smul_eq_mul, mul_one, mul_neg_one, ← sub_eq_add_neg] at hh
      convert hh using 1
      congr 1
      ring
    calc
      _ = ∑ i, T*w i*(((1+(z i).2)/2)*ell (δ*u (z i).1+(1-δ)) +
          ((1-(z i).2)/2)*ell (δ*u (z i).1-(1-δ))) := by
        simp_rw [lifted_cost_eq heven u δ _ (hs _)]
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro i hi
        simp only [Fin.sum_univ_two,b,v,s,ite_true,one_ne_zero,ite_false,one_mul,mul_one,neg_one_mul,mul_neg_one,← sub_eq_add_neg]
        ring
      _ ≤ ∑ i, T*w i * L (z i) := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hli i) (mul_nonneg hT.le (hw i).le))
      _ = L (q,a) := by
        have hh : ∑ i, (T*w i) • z i = (q,a) := by
          simp_rw [mul_smul]
          rw [← smul_sum,heq]
          ext <;> simp [smul_smul,hT.ne']
        simpa only [map_sum,map_smul,smul_eq_mul] using congrArg L hh
  refine ⟨R,?_⟩
  intro U S
  apply hR.trans
  have hsum : ∑ i, S.weight i • (S.point i,S.sign i) = (q,a) := by
    ext
    · simpa only [Prod.fst_sum,Prod.smul_fst] using S.sum_point
    · simpa only [Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using S.sum_sign
  calc
    L (q,a) = ∑ i, S.weight i * L (S.point i,S.sign i) := by rw [← hsum,map_sum]; simp only [map_smul,smul_eq_mul]
    _ ≤ S.cost ell u δ := by
      apply sum_le_sum
      intro i hi
      rw [lifted_cost_eq heven u δ _ (S.sign_eq i)]
      apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
      apply hbound _ (S.point_norm i)
      rcases S.sign_eq i with hh | hh <;> rw [hh] <;> norm_num

end

open Set Filter MeasureTheory
open scoped Topology ENNReal Pointwise

end SymmetricMahler

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric MeasureTheory Complex
open scoped Topology
namespace MahlerConformal

lemma summable_odd_square_inv : Summable (fun k : ℕ => 1 / ((2*k+1:ℕ):ℝ)^2) := by
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
    (by intro a b h; change 2*a+1 = 2*b+1 at h; omega)

lemma term_two_bound_closed (k : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖term 2 k w‖ ≤ 1 / ((2*k+1:ℕ):ℝ)^2 := by
  rw [term, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hw) (by positivity)

lemma continuousOn_F_closed : ContinuousOn F (closedBall (0:ℂ) 1) := by
  apply continuousOn_const.mul
  apply continuousOn_tsum (fun k => ?_) summable_odd_square_inv
  · intro k w hw
    exact term_two_bound_closed k (mem_closedBall_zero_iff.mp hw)
  · unfold term
    fun_prop

lemma closure_Omega_eq : closure Omega = F '' closedBall (0:ℂ) 1 := by
  apply subset_antisymm
  · apply closure_minimal (image_mono ball_subset_closedBall)
    exact (isCompact_closedBall (0:ℂ) 1).image_of_continuousOn continuousOn_F_closed |>.isClosed
  · have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball _ (by norm_num)
    rw [← hcl]
    exact (hcl ▸ continuousOn_F_closed).image_closure

lemma continuous_boundary_F : Continuous (fun θ : ℝ => F (polar 1 θ)) := by
  apply continuousOn_F_closed.comp_continuous
  · unfold polar
    fun_prop
  · intro θ
    simp only [mem_closedBall_zero_iff, norm_polar (by norm_num : (0:ℝ) ≤ 1), le_refl]

lemma tendsto_F_polar_boundary (θ : ℝ) :
    Tendsto (fun r : ℝ => F (polar r θ)) (𝓝[<] 1) (𝓝 (F (polar 1 θ))) := by
  apply (continuousOn_F_closed _ (by simp [norm_polar])).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have : Continuous (fun r : ℝ => polar r θ) := by unfold polar; fun_prop
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_radius] with r hr
    simpa only [mem_closedBall_zero_iff, norm_polar hr.1.le] using hr.2.le

lemma boundary_F_one : F 1 = 1 := by
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_F_polar_boundary 0)
  simp only [polar_zero, Complex.ofReal_one, Function.comp_def] at hlim
  have hreal : (F 1).re = 1 := tendsto_nhds_unique hlim F_real_tendsto_one
  apply Complex.ext
  · exact hreal
  · simpa using F_real_im 1

lemma integral_B_boundary {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Tendsto (fun r => ∫ t in (0:ℝ)..θ, B r t) (𝓝[<] 1) (𝓝 (2*θ/Real.pi)) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := θ) (F := B) (f := fun _ => 2/Real.pi)
    (fun _ => 2/Real.pi)
    (Filter.Eventually.of_forall fun r => (continuous_B r).aestronglyMeasurable)
    (by
      filter_upwards [eventually_radius] with r hr
      exact Filter.Eventually.of_forall fun t ht => by
        rw [uIoc_of_le hθ] at ht
        rw [Real.norm_eq_abs, abs_of_nonneg (B_nonneg hr.1 hr.2 ⟨ht.1.le,ht.2.trans hθπ⟩)]
        exact (B_lt_two_div_pi r t).le)
    intervalIntegrable_const
    (by
      filter_upwards [volume.ae_ne Real.pi] with t htπ
      intro ht
      rw [uIoc_of_le hθ] at ht
      exact B_tendsto_one ht.1 (lt_of_le_of_ne (ht.2.trans hθπ) htπ))
  convert ht using 1 ; simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] ; congr 1 ; ring

lemma Q_boundary {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Q 1 θ = 1 - 2*θ/Real.pi := by
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_F_polar_boundary θ)
  have hlim' := F_real_tendsto_one.sub (integral_B_boundary hθ hθπ)
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (F (r:ℂ)).re - (∫ t in (0:ℝ)..θ, B r t) = Q r θ := by
    filter_upwards [eventually_radius] with r hr
    rw [integral_B hr.1 hr.2, Q_zero]
    ring
  exact tendsto_nhds_unique hlim (hlim'.congr' he)

lemma continuous_lensWidth : Continuous lensWidth := by
  exact Complex.continuous_im.comp (continuous_boundary_F.comp (by fun_prop))

lemma lensWidth_one : lensWidth 1 = 0 := by simp [lensWidth, polar_zero, boundary_F_one]

lemma lensWidth_neg_one : lensWidth (-1) = 0 := by
  unfold lensWidth
  rw [show Real.pi/2*(1-(-1:ℝ)) = Real.pi by ring, polar_pi, F_odd]
  simp [boundary_F_one]

lemma lensWidth_even (t : ℝ) : lensWidth (-t) = lensWidth t := by
  have he : Real.pi/2*(1-(-t)) = Real.pi - Real.pi/2*(1-t) := by ring
  simp only [lensWidth, he, polar_pi_sub, F_odd, F_conj, Complex.neg_im, Complex.conj_im, neg_neg]

lemma cayley_im_of_ne {w : ℂ} (_ : w ≠ 1) :
    (cayley w).im = 2*w.im / Complex.normSq (1-w) := by
  simp only [cayley, Complex.div_im, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im]

  ring

lemma continuousAt_boundaryDerivative {w : ℂ} (hw₀ : w ≠ 0)
    (hw₁ : w ≠ 1) (hwi : (cayley w).im ≠ 0) :
    ContinuousAt boundaryDerivative w := by
  have hden : (1:ℂ)-w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw₁)
  have hc : ContinuousAt cayley w := by
    exact (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  have hl := (continuousAt_clog (Or.inr hwi)).comp hc
  unfold boundaryDerivative
  exact ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw₀)).mul hl).smul continuousAt_const

lemma hasFDerivWithinAt_F_closed {w : ℂ} (hw₀ : w ≠ 0)
    (hw₁ : w ≠ 1) (hwi : (cayley w).im ≠ 0) :
    HasFDerivWithinAt F (boundaryDerivative w) (closedBall (0:ℂ) 1) w := by
  have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball _ (by norm_num)
  rw [← hcl]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (differentiableOn_F.restrictScalars ℝ) (convex_ball (0:ℂ) 1) isOpen_ball
  · intro z hz
    exact (continuousOn_F_closed z (hcl ▸ hz)).mono ball_subset_closedBall
  · apply ((continuousAt_boundaryDerivative hw₀ hw₁ hwi).tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin, (eventually_ne_nhds hw₀).filter_mono nhdsWithin_le_nhds] with z hz hz₀
    have hd := (hasDerivAt_F_log (mem_ball_zero_iff.mp hz) hz₀).hasFDerivAt.restrictScalars ℝ
    rw [hd.fderiv]
    ext v
    simp [boundaryDerivative, ContinuousLinearMap.toSpanSingleton_apply, mul_comm, cayley]

lemma hasDerivAt_boundary_F {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    HasDerivAt (fun t : ℝ => F (polar 1 t))
      ((4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ))) θ := by
  have hwim : 0 < (polar 1 θ).im := by
    rw [polar_im, one_mul]
    exact Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hw₁ : polar 1 θ ≠ 1 := by intro h; simp [h] at hwim
  have hwi : (cayley (polar 1 θ)).im ≠ 0 := by
    rw [cayley_im_of_ne hw₁]
    exact ne_of_gt (div_pos (by positivity) (Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hw₁))))
  have hd := (hasFDerivWithinAt_F_closed (polar_ne_zero zero_lt_one θ) hw₁ hwi).comp_hasDerivAt θ
    (hasDerivAt_polar_complex 1 (θ:ℂ)).comp_ofReal
    (Filter.Eventually.of_forall fun t => by simp [norm_polar])
  change HasDerivAt (fun t : ℝ => F (polar 1 t))
    (boundaryDerivative (polar 1 θ) (I*polar 1 θ)) θ at hd
  have he : boundaryDerivative (polar 1 θ) (I*polar 1 θ) =
      (4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ)) := by
    simp only [boundaryDerivative, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp [polar_ne_zero zero_lt_one θ]
  rwa [he] at hd

lemma hasDerivAt_boundary_S {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    HasDerivAt (S 1) (4/Real.pi^2 * Real.log ‖cayley (polar 1 θ)‖) θ := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_boundary_F hθ hθπ)
  change HasDerivAt (S 1)
    (((4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ))).im) θ at hd
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.mul_im, Complex.log_re] using hd

lemma cayley_polar_boundary {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    cayley (polar 1 θ) = ((Real.cos (θ/2) / Real.sin (θ/2) : ℝ) : ℂ) * I := by
  have hs : Real.sin (θ/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hw : (1:ℂ)-polar 1 θ ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [polar_im] at hi
    exact (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne' hi
  unfold cayley
  apply (div_eq_iff hw).mpr
  have hsin : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using Real.sin_two_mul (θ/2)
  have hcos : Real.cos θ = Real.cos (θ/2)^2 - Real.sin (θ/2)^2 := by
    have h := Real.cos_two_mul (θ/2)
    rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, polar_re, polar_im, one_mul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_im,
      zero_mul, mul_zero, zero_sub, sub_zero, add_zero, mul_one]
    rw [hsin, hcos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (θ/2), congrArg (fun x : ℝ => x * Real.sin (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2)), congrArg (fun x : ℝ => x * Real.cos (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2))]
  · simp only [Complex.add_im, Complex.one_im, polar_im, one_mul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      polar_re, zero_mul, mul_zero, zero_sub, sub_zero, add_zero, zero_add, mul_one]
    rw [hsin, hcos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (θ/2), congrArg (fun x : ℝ => x * Real.sin (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2)), congrArg (fun x : ℝ => x * Real.cos (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2))]

lemma norm_cayley_polar_boundary {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ‖cayley (polar 1 θ)‖ = Real.cos (θ/2) / Real.sin (θ/2) := by
  rw [cayley_polar_boundary hθ hθπ, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

lemma concaveOn_boundary_S : ConcaveOn ℝ (Icc 0 Real.pi) (S 1) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    (Complex.continuous_im.comp continuous_boundary_F).continuousOn
  · rw [interior_Icc]
    intro θ hθ
    exact (hasDerivAt_boundary_S hθ.1 hθ.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    change deriv (S 1) y ≤ deriv (S 1) x
    rw [(hasDerivAt_boundary_S hx.1 hx.2).deriv, (hasDerivAt_boundary_S hy.1 hy.2).deriv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [norm_cayley_polar_boundary hx.1 hx.2, norm_cayley_polar_boundary hy.1 hy.2]
    apply Real.log_le_log
    · exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hy.1],by linarith [hy.2]⟩)
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hy.1]) (by linarith [hy.2,Real.pi_pos]))
    · apply div_le_div₀
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2]⟩
      · exact Real.antitoneOn_cos ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_pos]⟩
          ⟨by linarith [hy.1],by linarith [hy.2,Real.pi_pos]⟩ (by linarith)
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])
      · exact Real.monotoneOn_sin ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2]⟩
          ⟨by linarith [hy.1,Real.pi_pos],by linarith [hy.2]⟩ (by linarith)

lemma width_angle_mem {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    Real.pi/2*(1-t) ∈ Icc 0 Real.pi := by
  constructor
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr ht.2)
  · nlinarith [mul_nonneg Real.pi_pos.le (show 0 ≤ t+1 by linarith [ht.1])]

lemma concaveOn_lensWidth : ConcaveOn ℝ (Icc (-1:ℝ) 1) lensWidth := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := concaveOn_boundary_S.2 (width_angle_mem hx) (width_angle_mem hy) ha hb hab
  change a*S 1 (Real.pi/2*(1-x)) + b*S 1 (Real.pi/2*(1-y)) ≤
    S 1 (a*(Real.pi/2*(1-x))+b*(Real.pi/2*(1-y))) at h
  have he : a*(Real.pi/2*(1-x))+b*(Real.pi/2*(1-y)) =
      Real.pi/2*(1-(a*x+b*y)) := by
    calc
      _ = Real.pi/2*((a+b)-(a*x+b*y)) := by ring
      _ = _ := by rw [hab]
  simpa only [he, lensWidth, S, smul_eq_mul] using h

lemma lensWidth_nonneg {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) : 0 ≤ lensWidth t := by
  have h := concaveOn_lensWidth.2
    (show (-1:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    (show 0 ≤ (1-t)/2 by linarith [ht.2])
    (show 0 ≤ (1+t)/2 by linarith [ht.1])
    (show (1-t)/2 + (1+t)/2 = 1 by ring)
  simpa only [lensWidth_neg_one, lensWidth_one, smul_eq_mul, mul_zero, add_zero,
    show (1-t)/2*(-1)+(1+t)/2*1 = t by ring] using h

lemma boundary_width_upper {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    (F (polar 1 θ)).re ∈ Icc (-1:ℝ) 1 ∧
      (F (polar 1 θ)).im = lensWidth (F (polar 1 θ)).re := by
  have he := Q_boundary hθ.1 hθ.2
  change (F (polar 1 θ)).re = 1-2*θ/Real.pi at he
  have hq : (F (polar 1 θ)).re ∈ Icc (-1:ℝ) 1 := by
    rw [he]
    constructor
    · have := (div_le_iff₀ Real.pi_pos).mpr (show 2*θ ≤ 2*Real.pi by linarith [hθ.2])
      linarith
    · have := div_nonneg (show 0 ≤ 2*θ by linarith [hθ.1]) Real.pi_pos.le
      linarith
  refine ⟨hq, ?_⟩
  unfold lensWidth
  congr 3
  rw [he]
  field_simp
  ring

lemma boundary_width {w : ℂ} (hw : ‖w‖ = 1) :
    (F w).re ∈ Icc (-1:ℝ) 1 ∧ |(F w).im| = lensWidth (F w).re := by
  have hp : polar 1 w.arg = w := by
    have h : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    simpa only [hw] using h
  by_cases ha : 0 ≤ w.arg
  · have h := boundary_width_upper ⟨ha, Complex.arg_le_pi w⟩
    rw [hp] at h
    exact ⟨h.1, by rw [h.2, abs_of_nonneg (lensWidth_nonneg h.1)]⟩
  · have ham : -w.arg ∈ Icc 0 Real.pi :=
      ⟨by linarith, by linarith [Complex.neg_pi_lt_arg w]⟩
    have h := boundary_width_upper ham
    rw [polar_neg_angle, hp, F_conj] at h
    simp only [Complex.conj_re, Complex.conj_im] at h
    exact ⟨h.1, by rw [← abs_neg, h.2, abs_of_nonneg (lensWidth_nonneg h.1)]⟩

lemma isCompact_closure_Omega : IsCompact (closure Omega) := by
  rw [closure_Omega_eq]
  exact (isCompact_closedBall (0:ℂ) 1).image_of_continuousOn continuousOn_F_closed

lemma closure_Omega_im_le {u : ℂ} (hu : u ∈ closure Omega) :
    u.im ≤ lensWidth u.re := by
  let T : Set ℂ := closure Omega ∩ {v | v.re = u.re}
  have hT : IsCompact T := isCompact_closure_Omega.inter_right
    (isClosed_eq Complex.continuous_re continuous_const)
  have huT : u ∈ T := ⟨hu,rfl⟩
  obtain ⟨v,hv,hmax⟩ := hT.exists_isMaxOn ⟨u,huT⟩ Complex.continuous_im.continuousOn
  have hvn : v ∉ Omega := by
    intro hvO
    obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp isOpen_Omega v hvO
    let z : ℂ := v + (ε/2 : ℝ)*I
    have hz : z ∈ ball v ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [z, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hzr : z.re = u.re := by simpa [z] using hv.2
    have hzi : z.im = v.im+ε/2 := by simp [z]
    have hh := hmax ⟨subset_closure (hεO hz),hzr⟩
    change z.im ≤ v.im at hh
    linarith
  obtain ⟨w,hw,hwv⟩ := closure_Omega_eq ▸ hv.1
  have hwe : ‖w‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hw) (by
    by_contra! hn
    exact hvn (hwv ▸ (show F w ∈ Omega from ⟨w,mem_ball_zero_iff.mpr hn,rfl⟩)))
  have hb := (boundary_width hwe).2
  rw [hwv] at hb
  calc
    u.im ≤ v.im := hmax huT
    _ ≤ |v.im| := le_abs_self _
    _ = lensWidth v.re := hb
    _ = lensWidth u.re := congrArg lensWidth hv.2

lemma closure_Omega_conj {u : ℂ} (hu : u ∈ closure Omega) :
    starRingEnd ℂ u ∈ closure Omega := by
  obtain ⟨w,hw,rfl⟩ := closure_Omega_eq ▸ hu
  rw [closure_Omega_eq]
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa only [mem_closedBall_zero_iff, norm_conj] using hw

lemma closure_Omega_width_bound {u : ℂ} (hu : u ∈ closure Omega) :
    |u.im| ≤ lensWidth u.re := by
  apply abs_le.mpr
  constructor
  · have h := closure_Omega_im_le (closure_Omega_conj hu)
    simp only [Complex.conj_re, Complex.conj_im] at h
    linarith
  · exact closure_Omega_im_le hu

end MahlerConformal

open Set Filter
open scoped Topology
namespace MahlerEndpoint

lemma logCot_scaled_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => logCot (a*t) / Real.log t) (𝓝[>] 0) (𝓝 (-1)) := by
  let h : ℝ → ℝ := fun t => Real.cos (a*t) / (a * Real.sinc (a*t))
  have ht : Tendsto (fun t : ℝ => a*t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)))
  have hh : Tendsto h (𝓝[>] 0) (𝓝 (1/a)) := by
    simpa only [h, Real.cos_zero, Real.sinc_zero, mul_one, Function.comp_def, Pi.div_apply, Pi.mul_apply] using!
      (Real.continuous_cos.continuousAt.tendsto.comp ht).div
        (tendsto_const_nhds.mul (Real.continuous_sinc.continuousAt.tendsto.comp ht))
        (by simpa using ha.ne')
  have hh0 : (1/a:ℝ) ≠ 0 := one_div_ne_zero ha.ne'
  have hlim := ((hh.log hh0).div_atBot Real.tendsto_log_nhdsGT_zero).sub_const 1
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hh.eventually_ne hh0,
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (0:ℝ))] with t ht hh hl
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hlog : Real.log t ≠ 0 := hl.ne
  have hcot : Real.cos (a*t) / Real.sin (a*t) = h t / t := by
    dsimp [h]
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha.ne' ht0)]
    field_simp
  rw [logCot, hcot, Real.log_div hh ht0, sub_div, div_self hlog]

lemma logCot_scaled_ratio {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun t : ℝ => logCot (a*(c*t)) / logCot (a*t)) (𝓝[>] 0) (𝓝 1) := by
  have h1 := logCot_scaled_div_log (mul_pos ha hc)
  have h2 := logCot_scaled_div_log ha
  have hlim := h1.div h2 (by norm_num : (-1:ℝ) ≠ 0)
  simp only [div_self (by norm_num : (-1:ℝ) ≠ 0)] at hlim
  apply hlim.congr'
  filter_upwards [Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (0:ℝ))] with t ht
  have hlog := ht.ne
  change (logCot (a*c*t)/Real.log t) / (logCot (a*t)/Real.log t) = _
  rw [mul_assoc, div_div_div_cancel_right₀ hlog]

lemma profile_ratio {f : ℝ → ℝ} {a k r : ℝ}
    (ha : 0 < a) (hk : k ≠ 0) (hr : 0 < r)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hder : ∀ t ∈ Ioo 0 r, HasDerivAt f (k * logCot (a*t)) t)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => f (c*t) / f t) (𝓝[>] 0) (𝓝 c) := by
  have ht : Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hc ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  have hlog : ∀ᶠ t : ℝ in 𝓝[>] 0, logCot (a*t) ≠ 0 := by
    have hh := (logCot_scaled_div_log ha).eventually_ne (by norm_num : (-1:ℝ) ≠ 0)
    filter_upwards [hh] with t ht
    exact fun h => ht (by rw [h, zero_div])
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun t => (k * logCot (a*(c*t))) * c)
    (g' := fun t => k * logCot (a*t))
  · filter_upwards [ht.eventually hsmall] with t htt
    exact (hder (c*t) htt).comp t (by simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul c)
  · exact hsmall.mono (fun t ht => hder t ht)
  · exact hlog.mono (fun t ht => mul_ne_zero hk ht)
  · exact hf0.comp ht
  · exact hf0
  · have hh := (logCot_scaled_ratio ha hc).mul_const c
    simp only [one_mul] at hh
    convert hh using 1
    ext t
    field_simp

lemma concave_ratio_antitone {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0:ℝ) 2) f)
    (hf0 : f 0 = 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 2) :
    f y / y ≤ f x / x := by
  have hyp : 0 < y := hx.trans_le hxy
  have h := hf.2 (show (0:ℝ) ∈ Icc (0:ℝ) 2 by norm_num)
    (show y ∈ Icc (0:ℝ) 2 from ⟨hyp.le,hy⟩)
    (show 0 ≤ 1-x/y by apply sub_nonneg.mpr; exact (div_le_one hyp).mpr hxy)
    (div_nonneg hx.le hyp.le) (by ring : 1-x/y + x/y = 1)
  simp only [smul_eq_mul, hf0, mul_zero, zero_add, div_mul_cancel₀ x hyp.ne'] at h
  apply (div_le_div_iff₀ hyp hx).mpr
  have hh := mul_le_mul_of_nonneg_left h hyp.le
  field_simp at hh
  nlinarith

lemma uniform_profile_ratio {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc (0:ℝ) 2) f) (hf0 : f 0 = 0)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < f t)
    (hratio : ∀ c : ℝ, 0 < c →
      Tendsto (fun t : ℝ => f (c*t) / f t) (𝓝[>] 0) (𝓝 c))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < f δ ∧
      ∀ c ∈ Icc a b, |f (δ*c) / f δ - c| ≤ ε := by
  have hb : 0 < b := ha.trans_le hab
  have ha' := (hratio a ha).div_const a
  have hb' := (hratio b hb).div_const b
  rw [div_self ha.ne'] at ha'
  rw [div_self hb.ne'] at hb'
  have hea := (Metric.tendsto_nhds.mp ha') (ε/b) (div_pos hε hb)
  have heb := (Metric.tendsto_nhds.mp hb') (ε/b) (div_pos hε hb)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioo 0 (min 1 (2/b)) :=
    Ioo_mem_nhdsGT (by positivity)
  have hδ := hsmall.and (hea.and heb)
  obtain ⟨δ,hδ,hea,heb⟩ := hδ.exists
  have hδ0 := hδ.1
  have hδ1 := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ*b ≤ 2 := (le_div_iff₀ hb).mp (hδ.2.le.trans (min_le_right _ _))
  have hfp := hfpos δ ⟨hδ0,hδ1⟩
  refine ⟨δ,hδ0,hδ1,hfp,?_⟩
  intro c hc
  have hc0 : 0 < c := ha.trans_le hc.1
  have hlo := concave_ratio_antitone hf hf0 (mul_pos hδ0 hc0)
    (mul_le_mul_of_nonneg_left hc.2 hδ0.le) hδb
  have hhi := concave_ratio_antitone hf hf0 (mul_pos hδ0 ha)
    (mul_le_mul_of_nonneg_left hc.1 hδ0.le)
    ((mul_le_mul_of_nonneg_left hc.2 hδ0.le).trans hδb)
  have hlo' := mul_le_mul_of_nonneg_left hlo (div_nonneg hδ0.le hfp.le)
  have hhi' := mul_le_mul_of_nonneg_left hhi (div_nonneg hδ0.le hfp.le)
  have hlo'' : (f (b*δ)/ f δ)/ b ≤ (f (δ*c)/f δ)/c := by
    convert hlo' using 1 <;> try field_simp [hδ0.ne',hc0.ne',hb.ne',hfp.ne']
    all_goals try with_reducible_and_instances rfl

  have hhi'' : (f (δ*c)/f δ)/c ≤ (f (a*δ)/ f δ)/ a := by
    convert hhi' using 1 <;> try field_simp [hδ0.ne',hc0.ne',ha.ne',hfp.ne']
    all_goals try with_reducible_and_instances rfl

  rw [Real.dist_eq] at hea heb
  have hal := (abs_lt.mp hea).2
  have hbl := (abs_lt.mp heb).1
  have hrlo : 1-ε/b ≤ (f (δ*c)/f δ)/c := by linarith
  have hrhi : (f (δ*c)/f δ)/c ≤ 1+ε/b := by linarith
  have hlow := (le_div_iff₀ hc0).mp hrlo
  have hhigh := (div_le_iff₀ hc0).mp hrhi
  have hec : ε/b*c ≤ ε := by
    calc
      ε/b*c ≤ ε/b*b := mul_le_mul_of_nonneg_left hc.2 (div_nonneg hε.le hb.le)
      _ = ε := div_mul_cancel₀ ε hb.ne'
  rw [abs_le]
  constructor <;> nlinarith

end MahlerEndpoint

namespace MahlerConformal
open Set Filter Metric Complex
open scoped Topology

lemma lensWidth_zero_pos : 0 < lensWidth 0 := by
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp isOpen_Omega 0 zero_mem_Omega
  have hr2 : 0 < r/2 := half_pos hr
  have hu : ((r/2:ℝ):ℂ)*I ∈ closure Omega := subset_closure (hrO (by
    simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
    linarith))
  have hb := closure_Omega_width_bound hu
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_self, add_zero] at hb
  have hp : 0 < |r/2| := abs_pos.mpr (div_ne_zero hr.ne' (by norm_num))
  exact hp.trans_le hb

lemma lensWidth_endpoint_pos {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    0 < lensWidth (1-t) := by
  have hh := concaveOn_lensWidth.2
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
    (show (0:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1.le (by ring : 1-t+t=1)
  simp only [smul_eq_mul, lensWidth_one, mul_zero, zero_add, mul_one, add_zero] at hh
  exact (mul_pos ht.1 lensWidth_zero_pos).trans_le hh

lemma concaveOn_endpoint_profile :
    ConcaveOn ℝ (Icc (0:ℝ) 2) (fun t => lensWidth (1-t)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := concaveOn_lensWidth.2
    (show 1-x ∈ Icc (-1:ℝ) 1 by constructor <;> linarith [hx.1,hx.2])
    (show 1-y ∈ Icc (-1:ℝ) 1 by constructor <;> linarith [hy.1,hy.2]) ha hb hab
  have he : a*(1-x)+b*(1-y)=1-(a*x+b*y) := by nlinarith
  simpa only [smul_eq_mul, he] using hh

lemma hasDerivAt_endpoint_profile {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun t => lensWidth (1-t))
      ((2/Real.pi) * MahlerEndpoint.logCot ((Real.pi/4)*t)) t := by
  have hθ0 : 0 < Real.pi/2*t := mul_pos (by positivity) ht.1
  have hθπ : Real.pi/2*t < Real.pi := by nlinarith [Real.pi_pos, ht.2]
  have hh := (hasDerivAt_boundary_S hθ0 hθπ).comp t
    (by simpa only [mul_one,id_eq] using! (hasDerivAt_id t).const_mul (Real.pi/2))
  rw [norm_cayley_polar_boundary hθ0 hθπ] at hh
  convert hh using 1 <;> try rfl
  · ext t
    unfold lensWidth S
    congr 3
    ring
  · unfold MahlerEndpoint.logCot
    rw [show Real.pi/2*t/2=Real.pi/4*t by ring]
    field_simp
    ring

lemma lensWidth_endpoint_scaling :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < lensWidth (1-δ) ∧
        ∀ c ∈ Icc a b, |lensWidth (1-δ*c) / lensWidth (1-δ) - c| ≤ ε := by
  apply MahlerEndpoint.uniform_profile_ratio concaveOn_endpoint_profile
    (by simpa using lensWidth_one) (fun t ht => lensWidth_endpoint_pos ht)
  intro c hc
  apply MahlerEndpoint.profile_ratio (a := Real.pi/4) (k := 2/Real.pi)
    (r := 2) (by positivity) (by positivity) (by norm_num) _
    (fun t ht => hasDerivAt_endpoint_profile ht) hc
  have hh : Tendsto (fun t : ℝ => lensWidth (1-t)) (𝓝[>] 0) (𝓝 (lensWidth 1)) := by
    apply continuous_lensWidth.continuousAt.tendsto.comp
    simpa only [sub_zero,id_eq] using! tendsto_const_nhds.sub
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
  simpa only [lensWidth_one] using hh

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.StdSimplexCompat
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ2_Mah.Mahler_EqualityMedians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Filter Finset Metric
open scoped Topology

lemma mem_convexHull_zero_fiber {P E : Type*}
    [AddCommGroup E] [Module ℝ E] {S : Set P}
    (f : P → E) (g : P → ℝ) (hg : ∀ p ∈ S, 0 ≤ g p) {e : E}
    (he : (e, (0:ℝ)) ∈ convexHull ℝ ((fun p => (f p, g p)) '' S)) :
    e ∈ convexHull ℝ (f '' {p ∈ S | g p = 0}) := by
  classical
  obtain ⟨ι,_,z,w,hz,_,hw,hs,heq⟩ := eq_pos_convex_span_of_mem_convexHull he
  have hz' (i : ι) := hz (mem_range_self i)
  choose p hp hpeq using hz'
  have hsumg : ∑ i, w i * g (p i) = 0 := by
    have h := congrArg Prod.snd heq
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, ← hpeq] using h
  have hg0 (i : ι) : g (p i) = 0 := by
    have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le (hg _ (hp j)))).mp hsumg i (mem_univ i)
    exact (mul_eq_zero.mp hh).resolve_left (hw i).ne'
  have heqf : ∑ i, w i • f (p i) = e := by
    have h := congrArg Prod.fst heq
    simpa only [Prod.fst_sum, Prod.smul_fst, ← hpeq] using h
  exact mem_convexHull_of_exists_fintype w (fun i => f (p i)) (fun i => (hw i).le) hs
    (fun i => ⟨p i,⟨hp i,hg0 i⟩,rfl⟩) heqf

lemma isCompact_convexHull_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let D := Module.finrank ℝ E + 1
  let T (k : ℕ) : Set ((Fin k → ℝ) × (Fin k → E)) :=
    {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} ×ˢ
      Set.pi Set.univ (fun _ => S)
  let f (k : ℕ) (p : (Fin k → ℝ) × (Fin k → E)) := ∑ i, p.1 i • p.2 i
  have hWeights (k : ℕ) :
      IsCompact {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧
        ∑ index, weights index = 1} := by
    have compact := isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).continuous
    rw [Convexity.StdSimplex.range_toFun_comp_weights] at compact
    simpa only [Set.iInter_ofPred, Set.ofPred_inter_eq_sep, Set.mem_ofPred_eq,
      and_comm] using compact
  have hT (k : ℕ) : IsCompact (T k) :=
    (hWeights k).prod (by
      convert (isCompact_pi_infinite (ι := Fin k) (fun _ => hS)) using 1
      ext x
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq])
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have he : convexHull ℝ S = ⋃ k : Fin (D+1), f k '' T k := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨ι,_,z,w,hz,hind,hw,hs,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      let e := Fintype.equivFin ι
      have hk : Fintype.card ι < D+1 := by
        have hh := hind.card_le_finrank_succ
        have hb := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        dsimp [D]
        omega
      apply Set.mem_iUnion.mpr
      refine ⟨⟨Fintype.card ι,hk⟩, (w ∘ e.symm,z ∘ e.symm), ?_, ?_⟩
      · refine ⟨⟨fun i => (hw (e.symm i)).le, ?_⟩, ?_⟩
        · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
        · intro i hi
          exact hz (mem_range_self _)
      · dsimp only [f,Function.comp_apply]
        exact (e.symm.sum_comp (fun i => w i • z i)).trans hx
    · intro x hx
      obtain ⟨k,p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [he]
  exact isCompact_iUnion (fun k => (hT k).image (hf k))

lemma mem_convexHull_zero_fiber_of_tendsto {P E : Type*}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set P} (hS : IsCompact S)
    (f : P → E) (g : P → ℝ) (hf : ContinuousOn f S) (hgc : ContinuousOn g S)
    (hg : ∀ p ∈ S, 0 ≤ g p)
    (v : ℕ → E) (c : ℕ → ℝ)
    (hv : ∀ j, (v j,c j) ∈ convexHull ℝ ((fun p => (f p,g p)) '' S))
    {e : E} (hve : Tendsto v atTop (𝓝 e)) (hcz : Tendsto c atTop (𝓝 0)) :
    e ∈ convexHull ℝ (f '' {p ∈ S | g p = 0}) := by
  apply mem_convexHull_zero_fiber f g hg
  have hc := isCompact_convexHull_of_isCompact (hS.image_of_continuousOn (hf.prodMk hgc))
  exact hc.isClosed.mem_of_tendsto (hve.prodMk_nhds hcz) (Eventually.of_forall hv)

open Set Filter Finset Metric Complex
open scoped Topology
open MahlerConformal

lemma continuous_rowPair {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => rowPair p.1 p.2) := by
  unfold rowPair
  fun_prop

lemma continuous_rowComplex {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      rowComplex p.1 p.2) := by
  unfold rowComplex rowPair
  fun_prop

theorem common_boundary_witness_of_concentration {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    {Z : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hZ : IsCompact Z)
    (J : ℕ → Type) [∀ j, Fintype (J j)]
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ))) (hz : ∀ j, z j ∈ Z)
    (h : ∀ j, J j → Fin n → ℝ) (w : ∀ j, J j → ℝ) (ζ : ∀ j, J j → ℂ)
    (hh : ∀ j i, h j i ∈ C) (hw : ∀ j i, 0 ≤ w j i)
    (hs : ∀ j, ∑ i, w j i = 1)
    (hd : ∀ j i, ‖ζ j i‖ ≤ 1)
    (hF : ∀ j i, F (ζ j i) = rowComplex (h j i) (z j))
    (hy : ∀ j i, 0 ≤ rowPair (h j i) (z j).2)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : Tendsto z atTop (𝓝 z₀))
    {e : Fin n → ℝ} (he : Tendsto (fun j => ∑ i, w j i • h j i) atTop (𝓝 e))
    (hdef : Tendsto (fun j => ∑ i, w j i * (1-‖ζ j i‖)) atTop (𝓝 0)) :
    e ∈ convexHull ℝ {a ∈ C | rowPair a z₀.2 = lensWidth (rowPair a z₀.1)} := by
  classical
  let P : Type := C × (closedBall (0:ℂ) 1) × Z
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : CompactSpace (closedBall (0:ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let f : P → (Fin n → ℝ) := fun p => p.1.val
  let g : P → ℝ := fun p => (1-‖p.2.1.val‖) +
    ‖F p.2.1.val - rowComplex p.1.val p.2.2.val‖ +
    max 0 (-rowPair p.1.val p.2.2.val.2) + ‖p.2.2.val-z₀‖
  have hc : Continuous (fun p : P => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hdisk : Continuous (fun p : P => p.2.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hzz : Continuous (fun p : P => p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hf : Continuous f := hc
  have hcF : Continuous (fun p : P => F p.2.1.val) :=
    continuousOn_F_closed.comp_continuous hdisk (fun p => p.2.1.property)
  have hg : Continuous g :=
    (((continuous_const.sub hdisk.norm).add
      (hcF.sub (continuous_rowComplex.comp (hc.prodMk hzz))).norm).add
      (continuous_const.max ((continuous_rowPair.comp (hc.prodMk hzz.snd)).neg))).add
      (hzz.sub continuous_const).norm
  have hgn (p : P) : 0 ≤ g p := by
    dsimp only [g]
    exact add_nonneg (add_nonneg
      (add_nonneg (sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.2.1.property))
        (norm_nonneg _)) (le_max_left _ _)) (norm_nonneg _)
  let p (j : ℕ) (i : J j) : P :=
    (⟨h j i,hh j i⟩,⟨ζ j i,mem_closedBall_zero_iff.mpr (hd j i)⟩,⟨z j,hz j⟩)
  have hgp (j : ℕ) (i : J j) :
      g (p j i) = (1-‖ζ j i‖) + ‖z j-z₀‖ := by
    simp only [g,p,hF j i,sub_self,norm_zero,add_zero,
      max_eq_left (neg_nonpos.mpr (hy j i))]
  have hgs (j : ℕ) : ∑ i, w j i * g (p j i) =
      (∑ i, w j i * (1-‖ζ j i‖)) + ‖z j-z₀‖ := by
    simp_rw [hgp, mul_add]
    rw [sum_add_distrib, ← sum_mul, hs, one_mul]
  have hconv (j : ℕ) :
      (∑ i, w j i • h j i, ∑ i, w j i*g (p j i)) ∈
        convexHull ℝ ((fun p => (f p,g p)) '' (univ : Set P)) := by
    refine mem_convexHull_of_exists_fintype (w j) (fun i => (f (p j i),g (p j i)))
      (hw j) (hs j) (fun i => ?_) ?_
    · exact ⟨p j i,mem_univ _,rfl⟩
    · apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
        Prod.smul_snd, f, p, smul_eq_mul]
  have hgl : Tendsto (fun j => ∑ i, w j i*g (p j i)) atTop (𝓝 0) := by
    simp only [hgs]
    have hh := hdef.add ((hz₀.sub_const z₀).norm)
    simpa only [sub_self,norm_zero,add_zero] using hh
  have hmem := mem_convexHull_zero_fiber_of_tendsto (isCompact_univ : IsCompact (univ:Set P))
    f g hf.continuousOn hg.continuousOn (fun p _ => hgn p)
    _ _ hconv he hgl
  apply (convexHull_mono ?_) hmem
  rintro a ⟨p,⟨_,hpg⟩,rfl⟩
  have hd0 := sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.2.1.property)
  have hn1 := norm_nonneg (F p.2.1.val - rowComplex p.1.val p.2.2.val)
  have hn2 := le_max_left 0 (-rowPair p.1.val p.2.2.val.2)
  have hn3 := norm_nonneg (p.2.2.val-z₀)
  dsimp only [g] at hpg
  have heqz : p.2.2.val = z₀ := sub_eq_zero.mp (norm_eq_zero.mp (by linarith))
  have heqF : F p.2.1.val = rowComplex p.1.val z₀ := by
    rw [← heqz]
    exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith))
  have hbd : ‖p.2.1.val‖ = 1 := by linarith
  have hpos : 0 ≤ rowPair p.1.val z₀.2 := by
    have hm : max 0 (-rowPair p.1.val p.2.2.val.2) = 0 := by linarith
    have ht := le_max_right 0 (-rowPair p.1.val p.2.2.val.2)
    rw [hm,heqz] at ht
    linarith
  have hb := (boundary_width hbd).2
  rw [heqF] at hb
  simp only [rowComplex, Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_add,add_zero,sub_self,abs_of_nonneg hpos] at hb
  exact ⟨p.1.property,hb⟩

lemma rowPair_neg {n : ℕ} (a x : Fin n → ℝ) : rowPair (-a) x = -rowPair a x := by
  simp only [rowPair, Pi.neg_apply, neg_mul, sum_neg_distrib]

lemma rowComplex_neg {n : ℕ} (a : Fin n → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    rowComplex (-a) z = -rowComplex a z := by
  simp only [rowComplex, rowPair_neg, Complex.ofReal_neg, neg_mul, neg_add_rev]
  ring

lemma planarPrimitive_nonneg_iff {m : ℕ} (hm : 0 < m) {q t : ℝ}
    (ht : t ∈ verticalFiber q) : 0 ≤ planarPrimitive m q t ↔ 0 ≤ t := by
  have hz := (verticalFiber_interval (verticalFiber_realPart ht)).2.2
  have hh := (strictMonoOn_planarPrimitive_any hm q).le_iff_le hz ht
  simpa only [planarPrimitive_zero] using hh

lemma exists_positive_strip_sample {n : ℕ} {C : Set (Fin n → ℝ)}
    (hsym : ∀ a ∈ C, -a ∈ C) {a : Fin n → ℝ} (ha : a ∈ C)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : rowComplex a z ∈ Omega)
    {m : ℕ} (hm : 0 < m) :
    ∃ b ∈ C, ∃ ζ : ℂ,
      ‖ζ‖ = ‖inverseF (rowComplex a z)‖ ∧
      F ζ = rowComplex b z ∧ 0 ≤ rowPair b z.2 ∧
      |planarPrimitive m (rowPair a z.1) (rowPair a z.2)| • b =
        (planarPrimitive m (rowPair a z.1) (rowPair a z.2)) • a := by
  have ht : rowPair a z.2 ∈ verticalFiber (rowPair a z.1) := hz
  by_cases hpos : 0 ≤ rowPair a z.2
  · refine ⟨a,ha,inverseF (rowComplex a z),rfl,inverseF_right hz,hpos,?_⟩
    rw [abs_of_nonneg ((planarPrimitive_nonneg_iff hm ht).mpr hpos)]
  · have hneg : rowPair a z.2 < 0 := lt_of_not_ge hpos
    have hp : planarPrimitive m (rowPair a z.1) (rowPair a z.2) ≤ 0 :=
      le_of_not_ge (mt (planarPrimitive_nonneg_iff hm ht).mp hpos)
    refine ⟨-a,hsym a ha,-inverseF (rowComplex a z),norm_neg _,?_,?_,?_⟩
    · rw [F_odd,inverseF_right hz,rowComplex_neg]
    · rw [rowPair_neg]; linarith
    · rw [abs_of_nonpos hp, neg_smul, smul_neg, neg_neg]

lemma exists_fast_strip_degrees (N : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, (∀ j, 2 ≤ m j) ∧
      Tendsto (fun j => (N j:ℝ)*planarError (m j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (N j:ℝ)/((2*m j:ℕ)+1:ℝ)) atTop (𝓝 0) := by
  have hlim (j : ℕ) : Tendsto
      (fun m : ℕ => (N j:ℝ)*planarError m + (N j:ℝ)/((2*m:ℕ)+1:ℝ)) atTop (𝓝 0) := by
    have hf : Tendsto (fun m : ℕ => (2*m:ℕ)+1) atTop atTop := by
      apply tendsto_atTop_mono (fun m => show m ≤ 2*m+1 by omega) tendsto_id
    have hid : Tendsto (fun m : ℕ => (N j:ℝ) / ((2*m:ℕ)+1:ℝ)) atTop (𝓝 0) :=
      by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_const_nhds (x := (N j:ℝ))).div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hf)
    simpa only [mul_zero,add_zero] using
      ((planarError_nat_tendsto_zero.const_mul (N j:ℝ)).add hid)
  have hex (j : ℕ) : ∃ m : ℕ, 2 ≤ m ∧
      (N j:ℝ)*planarError m + (N j:ℝ)/((2*m:ℕ)+1:ℝ) < 1/((j:ℝ)+1) := by
    have hh := (hlim j).eventually (Iio_mem_nhds (show (0:ℝ) < 1/((j:ℝ)+1) by positivity))
    obtain ⟨m,hm,hm2⟩ := (hh.and (eventually_ge_atTop 2)).exists
    exact ⟨m,hm2,hm⟩
  choose m hm hbound using hex
  refine ⟨m,hm,?_,?_⟩
  · apply squeeze_zero (fun j => mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))
      (fun j => le_trans (le_add_of_nonneg_right (by positivity)) (hbound j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply squeeze_zero (fun j => by positivity)
      (fun j => le_trans (le_add_of_nonneg_left
        (mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))) (hbound j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma rowPair_sum_smul {n : ℕ} {J : Type*} [Fintype J]
    (w : J → ℝ) (h : J → Fin n → ℝ) (b : Fin n → ℝ) :
    rowPair (∑ i, w i • h i) b = ∑ i, w i * rowPair (h i) b := by
  simp only [rowPair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    sum_mul, mul_sum]
  rw [sum_comm]
  congr 1
  funext i
  apply sum_congr rfl
  intro k _
  ring

theorem common_boundary_witness_of_unnormalized {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    {Z : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hZ : IsCompact Z)
    (J : ℕ → Type) [∀ j, Fintype (J j)]
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ))) (hz : ∀ j, z j ∈ Z)
    (h : ∀ j, J j → Fin n → ℝ) (w : ∀ j, J j → ℝ) (ζ : ∀ j, J j → ℂ)
    (hh : ∀ j i, h j i ∈ C) (hw : ∀ j i, 0 ≤ w j i)
    (hd : ∀ j i, ‖ζ j i‖ ≤ 1)
    (hF : ∀ j i, F (ζ j i) = rowComplex (h j i) (z j))
    (hy : ∀ j i, 0 ≤ rowPair (h j i) (z j).2)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : Tendsto z atTop (𝓝 z₀))
    {e : Fin n → ℝ} (he : Tendsto (fun j => ∑ i, w j i • h j i) atTop (𝓝 e))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hs : ∀ j, ∑ i, w j i ≤ 1+err j)
    (hdef : Tendsto (fun j => ∑ i, w j i * (1-‖ζ j i‖)) atTop (𝓝 0))
    (b : Fin n → ℝ) (hb : ∀ a ∈ C, rowPair a b ≤ 1) (heb : rowPair e b = 1) :
    e ∈ convexHull ℝ {a ∈ C | rowPair a z₀.2 = lensWidth (rowPair a z₀.1)} := by
  classical
  let σ (j : ℕ) : ℝ := ∑ i, w j i
  have hσ : Tendsto σ atTop (𝓝 1) := by
    have hlo (j : ℕ) : rowPair (∑ i, w j i • h j i) b ≤ σ j := by
      rw [rowPair_sum_smul]
      apply sum_le_sum
      intro i _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb _ (hh j i)) (hw j i)
    have hlow : Tendsto (fun j => rowPair (∑ i, w j i • h j i) b) atTop (𝓝 1) := by
      rw [← heb]
      exact (continuous_rowPair.tendsto (e,b)).comp (he.prodMk_nhds tendsto_const_nhds)
    have hupp : Tendsto (fun j => 1+err j) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add herr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp hlo hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hσ.eventually (Ioi_mem_nhds zero_lt_one))
  let t (k : ℕ) := k+N
  have ht : Tendsto t atTop atTop := tendsto_add_atTop_nat N
  have hpos (k : ℕ) : 0 < σ (t k) := hN _ (Nat.le_add_left _ _)
  let wn (k : ℕ) (i : J (t k)) := (σ (t k))⁻¹ * w (t k) i
  have hnorm (k : ℕ) : ∑ i, wn k i = 1 := by
    rw [show (∑ i, wn k i) = (σ (t k))⁻¹ * σ (t k) by simp only [wn,σ,mul_sum]]
    exact inv_mul_cancel₀ (hpos k).ne'
  have hinv : Tendsto (fun k => (σ (t k))⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one,Function.comp_def] using (hσ.comp ht).inv₀ (one_ne_zero : (1:ℝ) ≠ 0)
  apply common_boundary_witness_of_concentration hC hZ (fun k => J (t k))
    (fun k => z (t k)) (fun k => hz (t k)) (fun k => h (t k)) wn
    (fun k => ζ (t k)) (fun k => hh (t k))
    (fun k i => mul_nonneg (inv_nonneg.mpr (hpos k).le) (hw _ _)) hnorm
    (fun k => hd (t k)) (fun k => hF (t k)) (fun k => hy (t k)) (hz₀.comp ht)
  · have he' := hinv.smul (he.comp ht)
    simpa only [Function.comp_def,one_smul, wn, mul_smul, smul_sum,smul_eq_mul] using he'
  · have he' := hinv.mul (hdef.comp ht)
    simpa only [Function.comp_def,mul_zero, wn, mul_assoc, mul_sum] using he'

open Set Filter Finset Metric Complex MeasureTheory
open scoped Topology
open MahlerConformal

lemma rowComplex_eq_stripCoordinate {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin N) :
    rowComplex (A i) z = stripCoordinate A z i := rfl

lemma push_eq_sum_smul {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ℝ) (p : J → ℝ) : push A p = ∑ i, p i • A i := by
  ext k
  simp only [push,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]

lemma strip_prefix_compact {n : ℕ} (C : Set (Fin n → ℝ)) (a : ℕ → C)
    (ha : Function.Injective (measurement (fun i : Fin n => (a i).val))) :
    ∃ Z : Set ((Fin n → ℝ) × (Fin n → ℝ)), IsCompact Z ∧
      ∀ N : ℕ, stripDomain (fun i : Fin (n+N) => (a i).val) ⊆ Z := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i => (a i).val
  refine ⟨stripCoordinate A ⁻¹' {f | ∀ i, f i ∈ closure Omega},
    stripCoordinate_compact_preimage A ha (isCompact_pi_infinite (fun _ => isCompact_closure_Omega)),?_⟩
  intro N z hz i
  exact subset_closure (hz ⟨i.val,by omega⟩)

lemma closed_lens_constraints_of_dense_prefix_limit {n : ℕ}
    (C : Set (Fin n → ℝ)) (a : ℕ → C) (hdense : DenseRange a)
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)))
    (hz : ∀ k, z k ∈ stripDomain (fun i : Fin (n+j k) => (a i).val))
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hlim : Tendsto z atTop (𝓝 z₀)) :
    ∀ h ∈ C, rowComplex h z₀ ∈ closure Omega := by
  intro h hh
  have hs : IsClosed {h : C | rowComplex h.val z₀ ∈ closure Omega} :=
    isClosed_closure.preimage
      (continuous_rowComplex.comp (continuous_subtype_val.prodMk continuous_const))
  refine hdense.induction_on (p := fun h : C => rowComplex h.val z₀ ∈ closure Omega)
    (⟨h,hh⟩ : C) hs ?_
  intro i
  apply isClosed_closure.mem_of_tendsto
    ((continuous_rowComplex.tendsto ((a i).val,z₀)).comp
      (tendsto_const_nhds.prodMk_nhds hlim))
  filter_upwards [hj.eventually (eventually_ge_atTop (i+1))] with k hk
  exact subset_closure (hz k ⟨i,by omega⟩)

theorem equality_common_lens_witness {n : ℕ} (hn : 1 ≤ n)
    {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
    (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
    (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
      (4:ℝ)^n/(Nat.factorial n:ℝ))
    {x e b : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B)
    (hb : b ∈ B) (heb : rowPair e b = 1) :
    ∃ y : Fin n → ℝ,
      (∀ a ∈ coordinatePolar B, |rowPair a y| ≤ lensWidth (rowPair a x)) ∧
      e ∈ convexHull ℝ {a ∈ coordinatePolar B | rowPair a y = lensWidth (rowPair a x)} := by
  classical
  let C := coordinatePolar B
  obtain ⟨hC,hCc,hCs,hCi⟩ := coordinatePolar_is_symmetric_convex_body hB hconv hsym hint
  obtain ⟨a,hadense,_,hainj,hacomp,_,hasub,_,havol,_⟩ :=
    exists_finite_strip_approximation hn hB hconv hsym hint
  obtain ⟨m,hm,herr,hinterior⟩ := exists_fast_strip_degrees (fun j => n+j)
  obtain ⟨j,z,hj,hz,hmaplim⟩ := equality_strip_images_dense_eq hn hB hconv hsym hint heq
    a hainj (fun j => (hacomp j).1) hasub havol m hm herr hx he
  have ha0 : Function.Injective (measurement (fun i : Fin n => (a i).val)) := by
    simpa only [Nat.add_zero] using hainj 0
  obtain ⟨Z,hZ,hcontain⟩ := strip_prefix_compact C a ha0
  obtain ⟨z₀,hz₀Z,φ,hφ,hφlim⟩ := hZ.tendsto_subseq (fun k => hcontain (j k) (hz k).1)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let t (k : ℕ) := j (φ k)
  let v (k : ℕ) := z (φ k)
  let A (k : ℕ) : Matrix (Fin (n+t k)) (Fin n) ℝ := fun i => (a i).val
  let J (k : ℕ) := Fin (n+t k)
  have hv (k : ℕ) : v k ∈ stripSublevel (A k) (m (t k)) := hz (φ k)
  have hvlim : Tendsto v atTop (𝓝 z₀) := hφlim
  have ht : Tendsto t atTop atTop := hj.comp hφtop
  have hmap : Tendsto (fun k => stripMap (A k) (m (t k)) (v k)) atTop (𝓝 (x,e)) :=
    hmaplim.comp hφtop
  have hvfst : Tendsto (fun k => (v k).1) atTop (𝓝 x) := by
    simpa only [Function.comp_def,stripMap] using (continuous_fst.tendsto (x,e)).comp hmap
  have hzx : z₀.1 = x := tendsto_nhds_unique ((continuous_fst.tendsto z₀).comp hvlim) hvfst
  have hsamples (k : ℕ) (i : J k) :
      ∃ b ∈ C, ∃ ζ : ℂ,
        ‖ζ‖ = ‖inverseF (rowComplex (A k i) (v k))‖ ∧
        F ζ = rowComplex b (v k) ∧ 0 ≤ rowPair b (v k).2 ∧
        |planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2)| • b =
          planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2) • A k i :=
    exists_positive_strip_sample hCs (a i).property ((hv k).1 i) (by have := hm (t k); omega)
  choose h hh ζ hnorm hF hy hsigned using hsamples
  let w (k : ℕ) (i : J k) : ℝ :=
    |planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2)|
  have hsum (k : ℕ) : (∑ i, w k i • h k i) = (stripMap (A k) (m (t k)) (v k)).2 := by
    simp only [w,hsigned,stripMap]
    rw [push_eq_sum_smul]
    rfl
  have hwlim : Tendsto (fun k => ∑ i, w k i • h k i) atTop (𝓝 e) := by
    simpa only [hsum,Function.comp_def] using ((continuous_snd.tendsto (x,e)).comp hmap)
  have hwupper (k : ℕ) : ∑ i, w k i ≤ 1+((n+t k:ℕ):ℝ)*planarError (m (t k)) :=
    strip_weights_bound_eq (A k) (hm (t k)) (hv k)
  have hdef : Tendsto (fun k => ∑ i, w k i * (1-‖ζ k i‖)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k => sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr ?_)))
      (fun k => ?_)
      (show Tendsto (fun k => ((n+t k:ℕ):ℝ)/((2*m (t k):ℕ)+1:ℝ) +
          ((n+t k:ℕ):ℝ)*planarError (m (t k))) atTop (𝓝 0) from
        by simpa only [add_zero,Function.comp_def] using (hinterior.comp ht).add (herr.comp ht))
    · rw [hnorm]
      exact (mem_ball_zero_iff.mp (inverseF_mem ((hv _).1 _))).le
    · simpa only [hnorm,w,rowComplex_eq_stripCoordinate,rowPair,measurement] using
        strip_concentration_bound_eq (A k) (hm (t k)) (hv k).1
  have hboundary := common_boundary_witness_of_unnormalized hC hZ J v
    (fun k => hcontain _ (hv k).1) h w ζ hh (fun _ _ => abs_nonneg _) (fun k i =>
      (hnorm k i).trans_le (mem_ball_zero_iff.mp (inverseF_mem ((hv k).1 i))).le)
    hF hy hvlim hwlim _ (herr.comp ht) hwupper hdef b
    (fun a ha => ha b hb) heb
  have hall := closed_lens_constraints_of_dense_prefix_limit C a hadense t ht v
    (fun k => (hv k).1) hvlim
  refine ⟨z₀.2,?_,?_⟩
  · intro a ha
    have hh := closure_Omega_width_bound (hall a ha)
    simpa [rowComplex,hzx] using hh
  · simpa only [hzx] using hboundary

open Set Finset MeasureTheory
open MahlerConformal
namespace RealNormData

lemma lifted_pair {n : ℕ} (h : RealNormData (Fin n → ℝ)) (p : h.Space) (a : ℝ)
    (v : Fin n → ℝ) (t : ℝ) :
    rowPair (h.segmentEquiv (p,a)) (Fin.append v (fun _ : Fin 1 => t)) =
      (∑ i, (h.spaceEquiv p) i*v i)+a*t := by
  simp only [rowPair,segmentEquiv_apply,dot_append,Fin.sum_univ_one]

theorem optimal_lift_of_equality {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    HasOptimalLiftRepresentations lensWidth h.Space := by
  intro u hu δ hδ hδ1 q a hq
  obtain ⟨v,hv,huv⟩ := coordinate_of_dual hd u
  let c := interval 1 (by norm_num : (0:ℝ) < 1)
  let G := g.coordSum c
  let H := h.coordMax c
  obtain ⟨hdual,heqlift⟩ := equality_segment_lift hn hd heq
  change G.IsDual H at hdual
  change (volume G.unit).toReal * (volume H.unit).toReal = _ at heqlift
  let T : ℝ := Max.max ‖q‖ |a|
  have hT : 0 < T := (norm_pos_iff.mpr hq).trans_le (le_max_left _ _)
  let e := T⁻¹ • h.segmentEquiv (q,a)
  let x : Fin (n+1) → ℝ := Fin.append (δ • v) (fun _ => 1-δ)
  have hx : x ∈ G.unit := by
    change g.coordSum c (Fin.append (δ • v) (fun _ => 1-δ)) ≤ 1
    rw [coordSum_append,g.smul_eq,abs_of_pos hδ,interval_apply,div_one,
      abs_of_nonneg (sub_nonneg.mpr hδ1.le)]
    have hh := mul_le_mul_of_nonneg_left (hv.trans hu.le) hδ.le
    linarith
  have hHe : H e = 1 := by
    change H (T⁻¹ • h.segmentEquiv (q,a)) = 1
    rw [H.smul_eq, abs_of_pos (inv_pos.mpr hT)]
    have hh : H (h.segmentEquiv (q,a)) = T := by
      simp only [H,segmentEquiv_apply,coordMax_append,c,interval_apply,div_one,T,space_norm]
    rw [hh,inv_mul_cancel₀ hT.ne']
  obtain ⟨b,hb,heb⟩ := hdual.2 e
  have he : e ∈ coordinatePolar G.unit := by
    rw [hdual.polar_unit]
    exact hHe.le
  obtain ⟨y,hy,hcontact⟩ := equality_common_lens_witness (show 1 ≤ n+1 by omega)
    G.isCompact_unit G.convex_unit G.symmetric_unit G.interior_unit_nonempty
    (by rw [hdual.polar_unit]; exact heqlift) hx he hb (heb.trans hHe)
  let doty : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun z => rowPair z y
    map_add' := by intro z w; simp [rowPair,add_mul,sum_add_distrib]
    map_smul' := by intro r z; simp [rowPair,mul_assoc,← mul_sum] }
  let L := doty.comp h.segmentEquiv.toLinearMap
  have hL (z : h.Space × ℝ) : L z = rowPair (h.segmentEquiv z) y := rfl
  have hnorm (z : h.Space × ℝ) : h.segmentEquiv z ∈ coordinatePolar G.unit ↔
      ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1 := by
    rcases z with ⟨p,s⟩
    rw [hdual.polar_unit]
    simp only [unit,segmentEquiv_apply,H,coordMax_append,c,interval_apply,div_one,space_norm,Set.mem_ofPred_eq,max_le_iff]
  have hpair (z : h.Space × ℝ) : rowPair (h.segmentEquiv z) x = δ*u z.1+(1-δ)*z.2 := by
    rw [lifted_pair,huv]
    simp only [Pi.smul_apply,smul_eq_mul]
    simp_rw [show ∀ i, (h.spaceEquiv z.1) i*(δ*v i) = δ*((h.spaceEquiv z.1) i*v i) by intro i; ring]
    rw [← mul_sum]
    ring
  apply optimal_signed_of_common_lens lensWidth_even concaveOn_lensWidth u hu.le hδ.le hδ1.le hT L
  · intro p hp s hs
    rw [hL,← hpair (p,s)]
    exact (le_abs_self _).trans (hy _ ((hnorm (p,s)).mpr ⟨hp,hs⟩))
  · have hmem : h.segmentEquiv.symm e ∈ convexHull ℝ
        (h.segmentEquiv.symm '' {z ∈ coordinatePolar G.unit | rowPair z y = lensWidth (rowPair z x)}) := by
      change _ ∈ convexHull ℝ (h.segmentEquiv.symm.toLinearMap '' _)
      rw [← h.segmentEquiv.symm.toLinearMap.image_convexHull]
      exact mem_image_of_mem _ hcontact
    have hem : h.segmentEquiv.symm e = (T⁻¹ • q,T⁻¹*a) := by
      simp only [e,map_smul,LinearEquiv.symm_apply_apply,Prod.smul_mk,smul_eq_mul]
    rw [hem] at hmem
    apply (convexHull_mono ?_) hmem
    rintro _ ⟨z,⟨hz,hze⟩,rfl⟩
    have hm := (hnorm (h.segmentEquiv.symm z)).mp (by simpa using hz)
    refine ⟨hm.1,hm.2,?_⟩
    rw [hL,LinearEquiv.apply_symm_apply,hze,← hpair,LinearEquiv.apply_symm_apply]

theorem medians_of_equality {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    HasMetricMedians h.Space :=
  metricMedians_of_optimal_lift lensWidth_endpoint_scaling (optimal_lift_of_equality hn hd heq)

end RealNormData

open Set MeasureTheory Metric

theorem equality_polar_gauge_medians_eq_oai {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (hi : (interior K).Nonempty)
    (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n/Nat.factorial n) :
    ∃ g h : RealNormData (Fin n → ℝ), g.unit = K ∧ h.unit = coordinatePolar K ∧
      g.IsDual h ∧ HasMetricMedians h.Space ∧ HasMetricMedians g.Space := by
  obtain ⟨hP,hPc,hPs,hPi⟩ := coordinatePolar_is_symmetric_convex_body hK hc hs hi
  let g := bodyNorm hK hc hs hi
  let h := bodyNorm hP hPc hPs hPi
  have hg : g.unit = K := bodyNorm_unit hK hc hs hi
  have hh : h.unit = coordinatePolar K := bodyNorm_unit hP hPc hPs hPi
  have hd := g.isDual_of_polar h (by rw [hg,hh])
  have hv : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n := by
    rwa [hg,hh]
  refine ⟨g,h,hg,hh,hd,RealNormData.medians_of_equality hn hd hv,?_⟩
  exact RealNormData.medians_of_equality hn hd.symm (by simpa only [mul_comm] using hv)

end SymmetricMahler

end

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.equality_polar_gauge_medians_eq_oai := @OAI.SymmetricMahler.equality_polar_gauge_medians_eq_oai
