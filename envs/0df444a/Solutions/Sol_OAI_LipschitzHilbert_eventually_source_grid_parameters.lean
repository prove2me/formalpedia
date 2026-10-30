-- Prove2me | solution 1 for OAI.LipschitzHilbert.eventually_source_grid_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:36:36.605338+00:00
-- url     : https://prove2.me/submissions/6b2bdd20-2462-4125-aa58-496adbc9f661

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_exists_source_supported_grid_prediction

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

theorem rpow_predecessor_le_one_add {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    x ^ (p - 1) ≤ 1 + x ^ p := by
  by_cases hx1 : x ≤ 1
  · have hpow := Real.rpow_le_one hx hx1 (sub_nonneg.mpr hp)
    exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (show p - 1 ≤ p by linarith)
    exact hpow.trans (le_add_of_nonneg_left zero_le_one)

theorem hasDerivAt_scalar_logEnergy {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ p))
      (p * x ^ (p - 1) / (1 + x ^ p)) x := by
  exact ((Real.hasDerivAt_rpow_const (Or.inr hp)).const_add 1).log
    (ne_of_gt (by positivity))

theorem scalar_logEnergy_derivative_bound {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    ‖deriv (fun y : ℝ => Real.log (1 + y ^ p)) x‖ ≤ p := by
  rw [(hasDerivAt_scalar_logEnergy hp hx).deriv, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx _)) (by positivity))]
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ p)).2
  exact mul_le_mul_of_nonneg_left (rpow_predecessor_le_one_add hp hx) (by linarith)

theorem scalar_logEnergy_lipschitz {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.log (1 + a ^ p) - Real.log (1 + b ^ p)| ≤ p * |a - b| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hasDerivAt_scalar_logEnergy hp hx).differentiableAt)
    (fun x hx => scalar_logEnergy_derivative_bound hp hx) hb ha
  simpa only [Real.norm_eq_abs] using h

/-- The exact global logarithmic-energy Lipschitz estimate, requiring only
that the vectors lie in a normed additive group. -/
theorem logEnergy_lipschitz {p : ℝ} (hp : 1 ≤ p) (x y : E) :
    |logEnergy p x - logEnergy p y| ≤ p * ‖x - y‖ := by
  exact (scalar_logEnergy_lipschitz hp (norm_nonneg x) (norm_nonneg y)).trans
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by linarith))

theorem energyRatio_pos {p denominator : ℝ} (hd : 0 < denominator) (x : E) :
    0 < energyRatio p denominator x := div_pos (by positivity) hd

theorem log_energyRatio_sub (p denominator : ℝ) (hd : 0 < denominator) (x y : E) :
    Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y) =
      logEnergy p x - logEnergy p y := by
  rw [energyRatio, energyRatio, Real.log_div (by positivity) hd.ne',
    Real.log_div (by positivity) hd.ne']
  unfold logEnergy
  ring

theorem log_energyRatio_lipschitz {p denominator : ℝ} (hp : 1 ≤ p) (hd : 0 < denominator)
    (x y : E) :
    |Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y)| ≤
      p * ‖x - y‖ := by
  rw [log_energyRatio_sub p denominator hd]
  exact logEnergy_lipschitz hp x y

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform Lipschitz bound for the logarithmic-energy derivative

The dimension-free derivative bound from §9 is proved using the radial
coefficient and its one-dimensional derivative. It supplies the cancellation
between the path numerator and denominator when the path child is dominant.
-/

noncomputable section

namespace LipschitzHilbert

theorem rpow_lower_exponent_le_one_add {p r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hap : a ≤ p) : r ^ a ≤ 1 + r ^ p := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_one hr hr1 ha).trans (le_add_of_nonneg_right (Real.rpow_nonneg hr _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hap).trans
      (le_add_of_nonneg_left zero_le_one)

theorem radialLogCoefficient_nonneg {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    0 ≤ radialLogCoefficient p r := by
  unfold radialLogCoefficient
  positivity

theorem radialLogCoefficient_le {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    radialLogCoefficient p r ≤ p := by
  unfold radialLogCoefficient
  apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ p)).2
  exact mul_le_mul_of_nonneg_left
    (rpow_lower_exponent_le_one_add hr (by linarith : 0 ≤ p - 2) (by linarith))
    (by linarith)

theorem radialLogCoefficient_mul {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    radialLogCoefficient p r * r = radialLogSlope p r := by
  have hpower : r ^ (p - 2) * r = r ^ (p - 1) := by
    rw [← Real.rpow_add_one' hr (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  unfold radialLogCoefficient radialLogSlope
  rw [div_mul_eq_mul_div, mul_assoc, hpower]

theorem hasDerivAt_radialLogSlope {p r : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) :
    HasDerivAt (radialLogSlope p)
      (p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) -
        (p * r ^ (p - 1) / (1 + r ^ p)) ^ 2) r := by
  have ha := (Real.hasDerivAt_rpow_const (x := r) (p := p - 1) (Or.inr (by linarith))).const_mul p
  have hb := (Real.hasDerivAt_rpow_const (x := r) (p := p) (Or.inr (by linarith))).const_add 1
  have hd := ha.div hb (by positivity : 1 + r ^ p ≠ 0)
  refine hd.congr_deriv ?_
  · field_simp
    rw [show p - 1 - 1 = p - 2 by ring]
    ring

theorem radialLogSlope_derivative_bound {p r : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) :
    ‖deriv (radialLogSlope p) r‖ ≤ 2 * p ^ 2 := by
  rw [(hasDerivAt_radialLogSlope hp hr).deriv, Real.norm_eq_abs]
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hden : 0 < 1 + r ^ p := by positivity
  have hhigh : r ^ (p - 2) / (1 + r ^ p) ≤ 1 := by
    apply (div_le_one hden).2
    exact rpow_lower_exponent_le_one_add hr (by linarith) (by linarith)
  have hs0 : 0 ≤ p * r ^ (p - 1) / (1 + r ^ p) := by positivity
  have hs1 : p * r ^ (p - 1) / (1 + r ^ p) ≤ p := by
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left (rpow_predecessor_le_one_add (by linarith) hr) (by linarith)
  have hfirst0 : 0 ≤ p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) := by positivity
  have hfirst1 : p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) ≤ p * (p - 1) := by
    calc
      _ = p * (p - 1) * (r ^ (p - 2) / (1 + r ^ p)) := by ring
      _ ≤ p * (p - 1) * 1 := mul_le_mul_of_nonneg_left hhigh (by positivity)
      _ = _ := mul_one _
  have hsquare : (p * r ^ (p - 1) / (1 + r ^ p)) ^ 2 ≤ p ^ 2 :=
    sq_le_sq₀ hs0 (by linarith) |>.mpr hs1
  apply abs_le.mpr
  constructor <;> nlinarith

theorem radialLogSlope_lipschitz {p r s : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |radialLogSlope p r - radialLogSlope p s| ≤ 2 * p ^ 2 * |r - s| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (hasDerivAt_radialLogSlope hp hr).differentiableAt)
    (fun r hr => radialLogSlope_derivative_bound hp hr) hs hr
  simpa only [Real.norm_eq_abs] using h

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded radial coefficient whose radial size is Lipschitz gives a
Lipschitz radial vector field. This proof never divides by a vector norm. -/
theorem radial_vector_lipschitz (k : ℝ → ℝ) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hk : ∀ r, 0 ≤ r → |k r| ≤ C)
    (hsize : ∀ r s, 0 ≤ r → 0 ≤ s → |k r * r - k s * s| ≤ L * |r - s|)
    (x y : E) : ‖k ‖x‖ • x - k ‖y‖ • y‖ ≤ (L + 2 * C) * ‖x - y‖ := by
  have hcoef : |k ‖x‖ - k ‖y‖| * ‖x‖ ≤ (L + C) * |‖x‖ - ‖y‖| := by
    calc
      _ = |(k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖) + k ‖y‖ * (‖y‖ - ‖x‖)| := by
        have hid : (k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖) + k ‖y‖ * (‖y‖ - ‖x‖) =
            (k ‖x‖ - k ‖y‖) * ‖x‖ := by ring
        rw [hid, abs_mul, abs_of_nonneg (norm_nonneg x)]
      _ ≤ |k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖| + |k ‖y‖ * (‖y‖ - ‖x‖)| := abs_add_le _ _
      _ ≤ L * |‖x‖ - ‖y‖| + C * |‖x‖ - ‖y‖| := by
        rw [abs_mul, abs_sub_comm ‖y‖ ‖x‖]
        exact add_le_add (hsize _ _ (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hk _ (norm_nonneg _)) (abs_nonneg _))
      _ = _ := by ring
  have heq : k ‖x‖ • x - k ‖y‖ • y =
      k ‖y‖ • (x - y) + (k ‖x‖ - k ‖y‖) • x := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖k ‖y‖ • (x - y)‖ + ‖(k ‖x‖ - k ‖y‖) • x‖ := norm_add_le _ _
    _ = |k ‖y‖| * ‖x - y‖ + |k ‖x‖ - k ‖y‖| * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ C * ‖x - y‖ + (L + C) * |‖x‖ - ‖y‖| :=
      add_le_add (mul_le_mul_of_nonneg_right (hk _ (norm_nonneg _)) (norm_nonneg _)) hcoef
    _ ≤ C * ‖x - y‖ + (L + C) * ‖x - y‖ := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity)) _
    _ = _ := by ring

end Radial

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_logEnergy {p : ℝ} (hp : 1 < p) (x : E) :
    HasFDerivAt (logEnergy p) (logEnergyDerivative p x) x := by
  have h := ((hasFDerivAt_norm_rpow x hp).const_add 1).log
    (by positivity : 1 + ‖x‖ ^ p ≠ 0)
  refine h.congr_fderiv ?_
  · simp only [logEnergyDerivative, radialLogCoefficient, smul_smul]
    congr 1
    ring

/-- The first derivative has the sharp global bound `p`. -/
theorem norm_logEnergyDerivative_le {p : ℝ} (hp : 2 ≤ p) (x : E) :
    ‖logEnergyDerivative p x‖ ≤ p := by
  rw [logEnergyDerivative, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radialLogCoefficient_nonneg (by linarith) (norm_nonneg x)),
    innerSL_apply_norm, radialLogCoefficient_mul hp (norm_nonneg x)]
  unfold radialLogSlope
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖x‖ ^ p)).2
  exact mul_le_mul_of_nonneg_left
    (rpow_predecessor_le_one_add (by linarith) (norm_nonneg x)) (by linarith)

/-- The global derivative is Lipschitz with a dimension-free `4 p²` constant. -/
theorem logEnergyDerivative_lipschitz {p : ℝ} (hp : 4 ≤ p) (x y : E) :
    ‖logEnergyDerivative p x - logEnergyDerivative p y‖ ≤ 4 * p ^ 2 * ‖x - y‖ := by
  have h := radial_vector_lipschitz (radialLogCoefficient p)
    (show 0 ≤ p by linarith) (show 0 ≤ 2 * p ^ 2 by positivity)
    (fun r hr => by
      rw [abs_of_nonneg (radialLogCoefficient_nonneg (by linarith) hr)]
      exact radialLogCoefficient_le (by linarith) hr)
    (fun r s hr hs => by
      rw [radialLogCoefficient_mul (by linarith) hr,
        radialLogCoefficient_mul (by linarith) hs]
      exact radialLogSlope_lipschitz hp hr hs) x y
  have heq : logEnergyDerivative p x - logEnergyDerivative p y =
      innerSL ℝ (radialLogCoefficient p ‖x‖ • x - radialLogCoefficient p ‖y‖ • y) := by
    simp only [logEnergyDerivative, map_sub, map_smul]
  rw [heq, innerSL_apply_norm]
  exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith : 2 * p ^ 2 + 2 * p ≤ 4 * p ^ 2)
    (norm_nonneg _))

end Hilbert

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RadialShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial snapshot shrinkage and the balanced prediction comparison

Section 9 shrinks each snapshot amplitude radially by a controlled distance.
The exact norm formula makes its denominator smaller than every nearby moved
denominator. The numerator motion and the logarithmic-energy Lipschitz bound
then give the balanced-case comparison, with its relative path-drop factor.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial truncation removes exactly the smaller of `δ` and the norm. -/
theorem norm_radialShrink {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x‖ = max (‖x‖ - δ) 0 := by
  by_cases hx : x = 0
  · subst x
    simp [max_eq_right (neg_nonpos.mpr hδ)]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [radialShrink, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  by_cases hsmall : δ ≤ ‖x‖
  · have hfactor : 0 ≤ 1 - δ / ‖x‖ := by
      exact sub_nonneg.mpr ((div_le_one hxnorm).2 hsmall)
    rw [max_eq_left hfactor, max_eq_left (sub_nonneg.mpr hsmall)]
    field_simp
  · have hlarge : ‖x‖ ≤ δ := le_of_lt (lt_of_not_ge hsmall)
    have hfactor : 1 - δ / ‖x‖ ≤ 0 := by
      exact sub_nonpos.mpr ((one_le_div hxnorm).2 hlarge)
    rw [max_eq_right hfactor, max_eq_right (sub_nonpos.mpr hlarge), zero_mul]

theorem norm_radialShrink_le {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x‖ ≤ ‖x‖ := by
  rw [norm_radialShrink hδ]
  exact max_le (sub_le_self _ hδ) (norm_nonneg _)

/-- The change in the amplitude never exceeds the requested shrinkage distance. -/
theorem norm_radialShrink_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x - x‖ ≤ δ := by
  let c := max (1 - δ / ‖x‖) 0
  have hc1 : c ≤ 1 := max_le (sub_le_self _ (div_nonneg hδ (norm_nonneg x))) zero_le_one
  have hnorm : c * ‖x‖ = max (‖x‖ - δ) 0 := by
    have h := norm_radialShrink hδ x
    rw [radialShrink, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (1 - δ / ‖x‖) 0)] at h
    exact h
  have heq : radialShrink δ x - x = (c - 1) • x := by
    simp only [radialShrink, sub_smul, one_smul, c]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hc1)]
  nlinarith [le_max_left (‖x‖ - δ) 0]

/-- A nearby moved vector has norm at least the scaled, radially shrunken
snapshot. `z` allows an arbitrary norm-preserving rotation of the snapshot. -/
theorem scaled_radialShrink_norm_le_of_error {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (x y z : E) (hz : ‖z‖ = c * ‖x‖) (hmotion : ‖y - z‖ ≤ c * δ) :
    ‖c • radialShrink δ x‖ ≤ ‖y‖ := by
  have hreverse : c * ‖x‖ ≤ ‖y‖ + c * δ := by
    have h := norm_sub_le y (y - z)
    rw [sub_sub_cancel, hz] at h
    exact h.trans (add_le_add_right hmotion _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, norm_radialShrink hδ]
  by_cases hsmall : δ ≤ ‖x‖
  · rw [max_eq_left (sub_nonneg.mpr hsmall)]
    nlinarith
  · rw [max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hsmall))), mul_zero]
    exact norm_nonneg _

/-- Raising the denominator comparison to any nonnegative real power preserves it. -/
theorem scaled_radialShrink_power_le_of_error {δ c p : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (x y z : E) (hz : ‖z‖ = c * ‖x‖) (hmotion : ‖y - z‖ ≤ c * δ) :
    ‖c • radialShrink δ x‖ ^ p ≤ ‖y‖ ^ p :=
  Real.rpow_le_rpow (norm_nonneg _) (scaled_radialShrink_norm_le_of_error hδ hc x y z hz hmotion) hp

theorem norm_weighted_smul_rpow {p l : ℝ} (hp : 0 < p) (hl : 0 ≤ l) (x : E) :
    ‖(l ^ (1 / p)) • x‖ ^ p = l * ‖x‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl _),
    Real.mul_rpow (Real.rpow_nonneg hl _) (norm_nonneg _), ← Real.rpow_mul hl]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

omit [NormedSpace ℝ E] in
/-- With the model denominator below the actual denominator, only numerator
motion contributes positively to the logarithmic ratio comparison. -/
theorem prediction_log_comparison {p dActual dModel : ℝ} (hp : 1 ≤ p)
    (hdModel : 0 < dModel) (hden : dModel ≤ dActual) (actual model : E) :
    Real.log (energyRatio p dActual actual) - Real.log (energyRatio p dModel model) ≤
      p * ‖actual - model‖ := by
  have hdActual : 0 < dActual := hdModel.trans_le hden
  have hlogden : Real.log dModel ≤ Real.log dActual := Real.log_le_log hdModel hden
  have hnum := (abs_le.mp (logEnergy_lipschitz hp actual model)).2
  rw [energyRatio, energyRatio, Real.log_div (by positivity) hdActual.ne',
    Real.log_div (by positivity) hdModel.ne']
  unfold logEnergy at hnum
  linarith

variable {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ E] in
/-- The balanced case of `pred:balanced-comparison`. Each child contributes
`ε K lᵢ` to numerator motion, the weights have total mass at most one, and
`u ≥ 1/2` recovers the relative path-drop factor at the cost of exactly two. -/
theorem balanced_prediction_log_comparison
    {p dActual dModel ε K u : ℝ} (hp : 1 ≤ p)
    (hdModel : 0 < dModel) (hden : dModel ≤ dActual)
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (hu : 1 / 2 ≤ u)
    (l : ι → ℝ) (hsum : ∑ i, l i ≤ 1)
    (actual model : ι → E) (hmotion : ∀ i, ‖actual i - model i‖ ≤ ε * K * l i) :
    Real.log (energyRatio p dActual (∑ i, actual i)) -
      Real.log (energyRatio p dModel (∑ i, model i)) ≤ 2 * p * ε * K * u := by
  have hmotionSum : ‖(∑ i, actual i) - ∑ i, model i‖ ≤ ε * K := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (actual i - model i)‖ ≤ ∑ i, ‖actual i - model i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ε * K * l i := Finset.sum_le_sum (fun i _ => hmotion i)
      _ = ε * K * ∑ i, l i := (Finset.mul_sum _ _ _).symm
      _ ≤ ε * K := by nlinarith [mul_nonneg hε hK]
  have h := (prediction_log_comparison hp hdModel hden (∑ i, actual i) (∑ i, model i)).trans
    (mul_le_mul_of_nonneg_left hmotionSum (by linarith))
  have hpεK : 0 ≤ p * ε * K := mul_nonneg (mul_nonneg (by linarith) hε) hK
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourth moments of separated finite Fourier sums

The exact finite expansion and Fourier-support reduction used in §7,
proof of Proposition `phase:finite-fourier`. The annihilation hypothesis
is a property of the averaging probability measure, not a new axiom.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem character_mul (a b t : ℝ) : character a t * character b t = character (a + b) t := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalPhaseSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging diagonal Hilbert-valued phases

The weighted prediction bound of §9 for finite-dimensional Hilbert vectors and
coordinate-dependent frequencies. The retained-set estimate is the proved
constant-one diagonal Fourier gain; the marginal cancellation is exact.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype Ω] [Fintype ι] [Fintype κ] in
theorem euclidean_sum_apply {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ κ) (j : κ) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

omit [Fintype Ω] [Fintype κ] in
theorem diagonalFourierSum_eq_sum (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    diagonalFourierSum frequency a t = ∑ i, diagonalModulation (frequency i) (a i) t := by
  apply PiLp.ext
  intro j
  rw [euclidean_sum_apply]
  rfl

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantPathComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dominant-path logarithmic comparison

The numerator and path denominator are compared together, as in §9,
`pred:path-errors` and equation (src-26). The derivative cancellation is
proved from the actual logarithmic-energy derivative; the residual
child denominator is retained with its exact fractional weight.
-/

noncomputable section

namespace LipschitzHilbert

section Residual

theorem hasDerivAt_residualLogCorrection {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    HasDerivAt (residualLogCorrection R) (R / (Real.exp a + R)) a := by
  have h := (hasDerivAt_id a).sub
    (((Real.hasDerivAt_exp a).add_const R).log (by positivity : Real.exp a + R ≠ 0))
  refine h.congr_deriv ?_
  · field_simp
    ring

/-- Throughout a logarithmic-energy interval of radius `d`, the derivative
of the residual correction is at most `exp d` times its initial fraction. -/
theorem residualLogCorrection_lipschitz {R a b d : ℝ} (hR : 0 ≤ R)
    (hd : 0 ≤ d) (hab : |b - a| ≤ d) :
    |residualLogCorrection R b - residualLogCorrection R a| ≤
      (Real.exp d * R / (Real.exp a + R)) * |b - a| := by
  have hbound (v : ℝ) (hv : v ∈ Set.Icc (a - d) (a + d)) :
      ‖deriv (residualLogCorrection R) v‖ ≤ Real.exp d * R / (Real.exp a + R) := by
    rw [(hasDerivAt_residualLogCorrection hR v).deriv, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (by positivity))]
    have hexp : Real.exp a ≤ Real.exp d * Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hv.1])
    have hexpd : 1 ≤ Real.exp d := Real.one_le_exp_iff.mpr hd
    apply (div_le_div_iff₀ (by positivity : 0 < Real.exp v + R)
      (by positivity : 0 < Real.exp a + R)).2
    have hden : Real.exp a + R ≤ Real.exp d * (Real.exp v + R) := by
      nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpd)]
    nlinarith [mul_le_mul_of_nonneg_left hden hR]
  have ha : a ∈ Set.Icc (a - d) (a + d) := ⟨by linarith, by linarith⟩
  have hb : b ∈ Set.Icc (a - d) (a + d) := by
    have h := abs_le.mp hab
    constructor <;> linarith
  have h := (convex_Icc (a - d) (a + d)).norm_image_sub_le_of_norm_deriv_le
    (fun v _ => (hasDerivAt_residualLogCorrection hR v).differentiableAt) hbound ha hb
  simpa only [Real.norm_eq_abs] using h

theorem residualLogCorrection_le {R a : ℝ} (hR : 0 ≤ R) :
    residualLogCorrection R a ≤ -R / (Real.exp a + R) := by
  have h := Real.log_le_sub_one_of_pos
    (div_pos (Real.exp_pos a) (by positivity : 0 < Real.exp a + R))
  rw [Real.log_div (Real.exp_pos a).ne' (by positivity : Real.exp a + R ≠ 0),
    Real.log_exp] at h
  have heq : Real.exp a / (Real.exp a + R) - 1 = -R / (Real.exp a + R) := by
    field_simp
    ring
  simpa only [residualLogCorrection, heq] using h

end Residual

section Normed

variable {E : Type*} [NormedAddCommGroup E]

theorem residualFraction_nonneg {p R : ℝ} (hR : 0 ≤ R) (Y : E) :
    0 ≤ residualFraction p R Y := by
  unfold residualFraction
  positivity

theorem residual_log_energy_change {p R : ℝ} (hp : 1 ≤ p) (hR : 0 ≤ R) (Y Y' : E) :
    residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y) ≤
      Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y := by
  have hp0 : 0 ≤ p := by linarith
  have hlog := logEnergy_lipschitz hp Y' Y
  have h := residualLogCorrection_lipschitz hR (mul_nonneg hp0 (norm_nonneg _)) hlog
  have hexp : Real.exp (logEnergy p Y) = 1 + ‖Y‖ ^ p := by
    unfold logEnergy
    exact Real.exp_log (by positivity)
  rw [hexp] at h
  have hnonneg : 0 ≤ Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R) := by positivity
  calc
    _ ≤ |residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y)| := le_abs_self _
    _ ≤ (Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R)) * |logEnergy p Y' - logEnergy p Y| := h
    _ ≤ (Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R)) * (p * ‖Y' - Y‖) :=
      mul_le_mul_of_nonneg_left hlog hnonneg
    _ = _ := by unfold residualFraction; ring

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact separation of the path denominator and the residual child mass. -/
theorem log_path_ratio_eq {p C R : ℝ} (hR : 0 ≤ R) (Y Z : E) :
    Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) =
      pathCancelledLogEnergy p C Z Y + residualLogCorrection R (logEnergy p Y) := by
  rw [energyRatio, Real.log_div (by positivity) (by positivity)]
  unfold pathCancelledLogEnergy residualLogCorrection logEnergy
  rw [Real.exp_log (by positivity : 0 < 1 + ‖Y‖ ^ p)]
  ring

/-- The model deficit controls the residual fraction, up to the off-path
numerator amplitude, exactly as in the second line of (src-26). -/
theorem dominant_model_deficit {p C R : ℝ} (hp : 1 ≤ p) (hR : 0 ≤ R)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Y Z : E) :
    residualFraction p R Y - p * ‖Z‖ ≤
      -Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) := by
  have hnorm : ‖C • Y‖ ≤ ‖Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_of_le_one_left (norm_nonneg _) hC1
  have hbase : logEnergy p (C • Y) ≤ logEnergy p Y := by
    unfold logEnergy
    apply Real.log_le_log (by positivity)
    exact add_le_add_right (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)) _
  have hperturb := (abs_le.mp (logEnergy_lipschitz hp (C • Y + Z) (C • Y))).2
  simp only [add_sub_cancel_left] at hperturb
  have hres := residualLogCorrection_le (a := logEnergy p Y) hR
  have hexp : Real.exp (logEnergy p Y) = 1 + ‖Y‖ ^ p := by
    exact Real.exp_log (by positivity)
  rw [hexp, neg_div] at hres
  rw [log_path_ratio_eq hR]
  unfold pathCancelledLogEnergy residualFraction
  linarith

theorem hasFDerivAt_pathCancelledLogEnergy {p C : ℝ} (hp : 1 < p) (Z V : E) :
    HasFDerivAt (pathCancelledLogEnergy p C Z)
      (C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V) V := by
  have h := ((hasFDerivAt_logEnergy hp (C • V + Z)).comp V
    (((hasFDerivAt_id V).const_smul C).add_const Z)).sub (hasFDerivAt_logEnergy hp V)
  refine h.congr_fderiv ?_
  · ext w
    simp

theorem norm_pathCancelledLogEnergy_derivative_le {p C K : ℝ} (hp : 4 ≤ p)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Z V : E) (hV : ‖V‖ ≤ K) :
    ‖C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ ≤
      p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) := by
  have hmove : ‖C • V + Z - V‖ ≤ (1 - C) * K + ‖Z‖ := by
    have heq : C • V + Z - V = (C - 1) • V + Z := by simp [sub_smul]; abel
    rw [heq]
    calc
      _ ≤ ‖(C - 1) • V‖ + ‖Z‖ := norm_add_le _ _
      _ = (1 - C) * ‖V‖ + ‖Z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : C - 1 ≤ 0)]
        ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hV (by linarith)) _
  have hdiff := (logEnergyDerivative_lipschitz hp (C • V + Z) V).trans
    (mul_le_mul_of_nonneg_left hmove (by positivity))
  have heq : C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V =
      C • (logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V) +
        (C - 1) • logEnergyDerivative p V := by
    ext w
    change C * (logEnergyDerivative p (C • V + Z)) w - (logEnergyDerivative p V) w =
      C * ((logEnergyDerivative p (C • V + Z)) w - (logEnergyDerivative p V) w) +
        (C - 1) * (logEnergyDerivative p V) w
    ring
  rw [heq]
  calc
    _ ≤ ‖C • (logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V)‖ +
        ‖(C - 1) • logEnergyDerivative p V‖ := norm_add_le _ _
    _ = C * ‖logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ +
        (1 - C) * ‖logEnergyDerivative p V‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hC0, abs_of_nonpos (by linarith : C - 1 ≤ 0)]
      ring
    _ ≤ ‖logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ + (1 - C) * p := by
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hC1)
        (mul_le_mul_of_nonneg_left (norm_logEnergyDerivative_le (by linarith) V) (by linarith))
    _ ≤ _ := by linarith

/-- The path numerator and path denominator change together. The resulting
motion is proportional to `1-C` and the off-path amplitude. -/
theorem pathCancelledLogEnergy_lipschitz {p C K : ℝ} (hp : 4 ≤ p)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Z Y Y' : E) (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K) :
    |pathCancelledLogEnergy p C Z Y' - pathCancelledLogEnergy p C Z Y| ≤
      (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ := by
  have h := (convex_closedBall (0 : E) K).norm_image_sub_le_of_norm_fderiv_le
    (fun V _ => (hasFDerivAt_pathCancelledLogEnergy (by linarith : 1 < p) Z V).differentiableAt)
    (fun V hV => by
      rw [(hasFDerivAt_pathCancelledLogEnergy (by linarith : 1 < p) Z V).fderiv]
      exact norm_pathCancelledLogEnergy_derivative_le hp hC0 hC1 Z V
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hV))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hY)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hY')
  simpa only [Real.norm_eq_abs] using h

/-- The first line of (src-26), before inserting the hierarchy's motion
constants. The numerator, path cancellation, and residual fraction have
separate exact coefficients. Increasing the actual residual only helps. -/
theorem dominant_prediction_log_comparison {p C C' R R' K : ℝ}
    (hp : 4 ≤ p) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hR : 0 ≤ R) (hRR' : R ≤ R')
    (Y Y' Z Z' : E) (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K) :
    Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) ≤
      p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) +
        (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ +
        Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hR' : 0 ≤ R' := hR.trans hRR'
  have hden : 1 + ‖Y'‖ ^ p + R ≤ 1 + ‖Y'‖ ^ p + R' := by linarith
  have hmon := prediction_log_comparison hp1
    (by positivity : 0 < 1 + ‖Y'‖ ^ p + R) hden (C' • Y' + Z') (C' • Y' + Z')
  simp only [sub_self, norm_zero, mul_zero] at hmon
  have hnumMotion : ‖(C' • Y' + Z') - (C • Y' + Z)‖ ≤
      |C' - C| * ‖Y'‖ + ‖Z' - Z‖ := by
    have heq : (C' • Y' + Z') - (C • Y' + Z) = (C' - C) • Y' + (Z' - Z) := by
      simp only [sub_smul]
      abel
    rw [heq]
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le ((C' - C) • Y') (Z' - Z)
  have hnum := ((abs_le.mp (logEnergy_lipschitz hp1 (C' • Y' + Z') (C • Y' + Z))).2).trans
    (mul_le_mul_of_nonneg_left hnumMotion hp0)
  have hpath := (abs_le.mp (pathCancelledLogEnergy_lipschitz hp hC0 hC1 Z Y Y' hY hY')).2
  have hres := residual_log_energy_change hp1 hR Y Y'
  have hid : Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R) (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) =
      (logEnergy p (C' • Y' + Z') - logEnergy p (C • Y' + Z)) +
      (pathCancelledLogEnergy p C Z Y' - pathCancelledLogEnergy p C Z Y) +
      (residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y)) := by
    rw [log_path_ratio_eq hR, log_path_ratio_eq hR]
    unfold pathCancelledLogEnergy
    ring
  linarith

end Hilbert

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the residual denominator error by the actual convex blend. -/

noncomputable section

namespace LipschitzHilbert

theorem blended_prediction_pos {b θ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 < (1 - θ) * b + θ := by
  by_cases hθ : θ = 1
  · simp [hθ]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)) hb) hθ0

/-- Concavity provides a gain measured by the negative logarithm of the
unblended prediction. -/
theorem blended_prediction_log_gain {b θ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    -θ * Real.log b ≤ Real.log ((1 - θ) * b + θ) - Real.log b := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hb (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (sub_nonneg.mpr hθ1) hθ0 (by ring : (1 - θ) + θ = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at h
  linarith

/-- The coefficient of the residual denominator can be canceled by choosing
the blending weight at least as large as its error coefficient. -/
theorem blended_prediction_domination {β b θ a e r d u : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hr : 0 ≤ r) (he : e ≤ θ)
    (hcomparison : Real.log β - Real.log b ≤ a * u + e * r)
    (hdeficit : r - d * u ≤ -Real.log b) :
    β ≤ Real.exp ((a + θ * d) * u) * ((1 - θ) * b + θ) := by
  have hgain := blended_prediction_log_gain hb hθ0 hθ1
  have hscaled := mul_le_mul_of_nonneg_left hdeficit hθ0
  have herr := mul_le_mul_of_nonneg_right he hr
  have hlog : Real.log β ≤ (a + θ * d) * u + Real.log ((1 - θ) * b + θ) := by
    nlinarith
  calc
    β = Real.exp (Real.log β) := (Real.exp_log hβ).symm
    _ ≤ Real.exp ((a + θ * d) * u + Real.log ((1 - θ) * b + θ)) :=
      Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add, Real.exp_log (blended_prediction_pos hb hθ0 hθ1)]

/-- In the balanced case `u ≥ 1/2`, a bounded model logarithm has the same
relative-drop form after blending. -/
theorem balanced_blended_prediction_domination {β b θ a d u : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : 0 ≤ d) (hu : 1 / 2 ≤ u)
    (hcomparison : Real.log β - Real.log b ≤ a * u)
    (hupper : Real.log b ≤ d) :
    β ≤ Real.exp ((a + 2 * θ * d) * u) * ((1 - θ) * b + θ) := by
  have hdeficit : (0 : ℝ) - (2 * d) * u ≤ -Real.log b := by
    nlinarith [mul_le_mul_of_nonneg_left hu hd]
  have h := blended_prediction_domination hβ hb hθ0 hθ1 (le_refl (0 : ℝ)) hθ0
    (show Real.log β - Real.log b ≤ a * u + 0 * 0 by simpa using hcomparison)
    hdeficit
  have heq : a + θ * (2 * d) = a + 2 * θ * d := by ring
  rw [heq] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantPredictionBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Relative-drop comparison and absorption for the dominant path

The concrete path-motion bounds from §9 are substituted in the proved
logarithmic comparison. The residual fraction is then absorbed by the actual
convex blend, giving a multiplicative error proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equation (src-26) with explicit universal constants. `A` accounts for the
absolute constants in the hierarchy motion estimates. -/
theorem dominant_prediction_log_comparison_of_errors
    {p C C' R R' K A ε u : ℝ} (hp : 4 ≤ p) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hR : 0 ≤ R) (hRR' : R ≤ R') (Y Y' Z Z' : E)
    (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K)
    (hCdrop : 1 - C ≤ A * u) (hZ : ‖Z‖ ≤ K * u)
    (hYmove : ‖Y' - Y‖ ≤ A * ε * K) (hCmove : |C' - C| ≤ A * ε * u)
    (hZmove : ‖Z' - Z‖ ≤ A * ε * K * u)
    (hsmall : Real.exp (A * p * ε * K) ≤ 2) :
    Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) ≤
      (12 * A ^ 2 * p ^ 2 * K ^ 2 * ε) * u +
        (2 * A * p * ε * K) * residualFraction p R Y := by
  have hp0 : 0 ≤ p := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hCbar : 0 ≤ 1 - C := by linarith
  have hnum : p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) ≤ 2 * A * p * ε * K * u := by
    have hprod := mul_le_mul hCmove hY' (norm_nonneg Y') (by positivity : 0 ≤ A * ε * u)
    calc
      _ ≤ p * ((A * ε * u) * K + A * ε * K * u) :=
        mul_le_mul_of_nonneg_left (add_le_add hprod hZmove) hp0
      _ = _ := by ring
  have hpK : p ≤ p ^ 2 * K := by
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hK)]
  have hfirst : p * (1 - C) ≤ A * p ^ 2 * K * u := by
    calc
      _ ≤ p * (A * u) := mul_le_mul_of_nonneg_left hCdrop hp0
      _ ≤ p ^ 2 * K * (A * u) := mul_le_mul_of_nonneg_right hpK (mul_nonneg hA0 hu)
      _ = _ := by ring
  have hsecond : 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) ≤ 8 * A * p ^ 2 * K * u := by
    have hinner : (1 - C) * K + ‖Z‖ ≤ 2 * A * K * u := by
      have hc := mul_le_mul_of_nonneg_right hCdrop hK0
      have ha := mul_le_mul_of_nonneg_right hA (mul_nonneg hK0 hu)
      nlinarith
    calc
      _ ≤ 4 * p ^ 2 * (2 * A * K * u) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  have hcore : p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) ≤ 9 * A * p ^ 2 * K * u := by
    linarith
  have hcoreTotal : (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ ≤
      9 * A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by
    calc
      _ ≤ (9 * A * p ^ 2 * K * u) * (A * ε * K) :=
        mul_le_mul hcore hYmove (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hApK : 1 ≤ A * p * K := by
    calc
      1 ≤ A * p := by nlinarith
      _ ≤ A * p * K := by nlinarith [mul_nonneg (mul_nonneg hA0 hp0) (sub_nonneg.mpr hK)]
  have hnumTotal : p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) ≤
      2 * A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by
    refine hnum.trans ?_
    nlinarith [mul_nonneg (show 0 ≤ 2 * A * p * ε * K * u by positivity) (sub_nonneg.mpr hApK)]
  have hmove : p * ‖Y' - Y‖ ≤ A * p * ε * K := by
    nlinarith [mul_le_mul_of_nonneg_left hYmove hp0]
  have hexp : Real.exp (p * ‖Y' - Y‖) ≤ 2 :=
    (Real.exp_le_exp.mpr hmove).trans hsmall
  have hres : Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y ≤
      (2 * A * p * ε * K) * residualFraction p R Y := by
    calc
      _ = Real.exp (p * ‖Y' - Y‖) * (p * ‖Y' - Y‖) * residualFraction p R Y := by ring
      _ ≤ 2 * (A * p * ε * K) * residualFraction p R Y :=
        mul_le_mul_of_nonneg_right (mul_le_mul hexp hmove (by positivity) (by norm_num))
          (residualFraction_nonneg hR Y)
      _ = _ := by ring
  have h := dominant_prediction_log_comparison (C' := C') hp hC0 hC1 hR hRR' Y Y' Z Z' hY hY'
  have hnonneg : 0 ≤ A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by positivity
  nlinarith

/-- The actual dominant-path prediction is bounded by the normalized model
blend, with no surviving error proportional to the residual denominator. -/
theorem dominant_prediction_blended_domination
    {p C C' R R' K A ε u θ : ℝ} (hp : 4 ≤ p) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hR : 0 ≤ R) (hRR' : R ≤ R') (Y Y' Z Z' : E)
    (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K)
    (hCdrop : 1 - C ≤ A * u) (hZ : ‖Z‖ ≤ K * u)
    (hYmove : ‖Y' - Y‖ ≤ A * ε * K) (hCmove : |C' - C| ≤ A * ε * u)
    (hZmove : ‖Z' - Z‖ ≤ A * ε * K * u)
    (hsmall : Real.exp (A * p * ε * K) ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (habsorb : 2 * A * p * ε * K ≤ θ) :
    energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z') ≤
      Real.exp ((12 * A ^ 2 * p ^ 2 * K ^ 2 * ε + θ * (p * K)) * u) *
        ((1 - θ) * energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z) + θ) := by
  have hR' : 0 ≤ R' := hR.trans hRR'
  have hβ := energyRatio_pos (p := p) (by positivity : 0 < 1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')
  have hb := energyRatio_pos (p := p) (by positivity : 0 < 1 + ‖Y‖ ^ p + R) (C • Y + Z)
  apply blended_prediction_domination hβ hb hθ0 hθ1 (residualFraction_nonneg hR Y) habsorb
  · exact dominant_prediction_log_comparison_of_errors hp hA hK hε hu hC0 hC1 hR hRR'
      Y Y' Z Z' hY hY' hCdrop hZ hYmove hCmove hZmove hsmall
  · have hdeficit := dominant_model_deficit (by linarith : 1 ≤ p) hR hC0 hC1 Y Z
    have hmove := mul_le_mul_of_nonneg_left hZ (by linarith : 0 ≤ p)
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized child identity

Exact algebra for §8, equation (src-25): the ratio of the parent amount
(with the residual omitted) to its child denominator equals the weighted
prediction ratio. No estimates or hierarchy hypotheses enter this identity.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem child_normalization_coefficient {n m μ : ℝ} (hn : 0 < n) (hm : 0 < m) :
    (m / n) ^ (1 - μ) * m ^ (μ - 1) = n ^ (μ - 1) := by
  rw [Real.div_rpow hm.le hn.le]
  have hm' : m ^ (1 - μ) * m ^ (μ - 1) = 1 := by
    rw [← Real.rpow_add hm, show (1 - μ) + (μ - 1) = 0 by ring, Real.rpow_zero]
  have hn' : (n ^ (1 - μ))⁻¹ = n ^ (μ - 1) := by
    rw [← Real.rpow_neg hn.le]
    congr 1
    ring
  calc
    _ = (m ^ (1 - μ) * m ^ (μ - 1)) * (n ^ (1 - μ))⁻¹ := by ring
    _ = _ := by rw [hm', one_mul, hn']

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GraphPhasePrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The mass-normalized node prediction

The explicitly constructed graph selection law and the diagonal Fourier gain
bound the original parent/child ratio from §8, after the exact normalization
identity. This is the normalized prediction estimate used in §9.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Fintype κ] in
theorem diagonalModulation_smul (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ)
    (c : ℂ) (t : ℝ) : diagonalModulation frequency (c • a) t =
      c • diagonalModulation frequency a t := by
  apply PiLp.ext
  intro j
  simp only [diagonalModulation, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit [Fintype κ] in
theorem diagonalFourierSum_coefficients (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (c : ι → ℂ) (t : ℝ) :
    diagonalFourierSum frequency (fun i => c i • a i) t =
      ∑ i, c i • diagonalModulation (frequency i) (a i) t := by
  rw [diagonalFourierSum_eq_sum]
  simp only [diagonalModulation_smul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ScalarPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the removed scalar phase

The dominant-path comparison in §9 removes the scalar phase of its path
weight. Relative motion of a nonzero complex weight gives controlled motion
of that phase, and hence of the rotated off-path vector.
-/

noncomputable section

namespace LipschitzHilbert

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit-vector normalization has a two-over-the-reference-norm bound. -/
theorem normalize_motion (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * ‖y - x‖ / ‖x‖ := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have heq : ‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x) =
      (y - x) + (‖x‖ - ‖y‖) • NormedSpace.normalize y := by
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hnorm : ‖x‖ * ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * ‖y - x‖ := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxnorm]
      _ ≤ ‖y - x‖ + ‖(‖x‖ - ‖y‖) • NormedSpace.normalize y‖ := by rw [heq]; exact norm_add_le _ _
      _ = ‖y - x‖ + |‖x‖ - ‖y‖| := by
        rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hy, mul_one]
      _ ≤ ‖y - x‖ + ‖y - x‖ := by
        exact add_le_add_right (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le x y) _
      _ = _ := by ring
  apply (le_div_iff₀ hxnorm).2
  nlinarith

end Normalize

theorem scalarPhase_eq_div (z : ℂ) : scalarPhase z = z / (‖z‖ : ℂ) := by
  simp only [scalarPhase, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem norm_scalarPhase {z : ℂ} (hz : z ≠ 0) : ‖scalarPhase z‖ = 1 :=
  NormedSpace.norm_normalize hz

theorem scalarPhase_ne_zero {z : ℂ} (hz : z ≠ 0) : scalarPhase z ≠ 0 := by
  intro h
  have hn := norm_scalarPhase hz
  rw [h, norm_zero] at hn
  norm_num at hn

/-- A relative complex-weight perturbation less than one preserves its
nonzero value and moves its unit phase by at most twice that perturbation. -/
theorem scalarPhase_relative_motion {z z' : ℂ} {ε : ℝ}
    (hz : z ≠ 0) (hε : ε < 1) (hmotion : ‖z' - z‖ ≤ ε * ‖z‖) :
    z' ≠ 0 ∧ ‖scalarPhase z' - scalarPhase z‖ ≤ 2 * ε := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : z' ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hmotion
    nlinarith
  refine ⟨hz', ?_⟩
  have h := normalize_motion z z' hz hz'
  change ‖scalarPhase z' - scalarPhase z‖ ≤ 2 * ‖z' - z‖ / ‖z‖ at h
  refine h.trans ?_
  apply (div_le_iff₀ hznorm).2
  nlinarith

theorem scalarPhase_inverse_motion {z z' : ℂ} {ε : ℝ}
    (hz : z ≠ 0) (hε : ε < 1) (hmotion : ‖z' - z‖ ≤ ε * ‖z‖) :
    ‖(scalarPhase z')⁻¹ - (scalarPhase z)⁻¹‖ ≤ 2 * ε := by
  obtain ⟨hz', hphase⟩ := scalarPhase_relative_motion hz hε hmotion
  have h := dist_inv_inv₀ (scalarPhase_ne_zero hz') (scalarPhase_ne_zero hz)
  simp only [norm_scalarPhase hz', norm_scalarPhase hz, one_mul, div_one, dist_eq_norm] at h
  rw [h]
  exact hphase

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass rescaling and block-transition motion for the snapshot prediction.
Every estimate is relative to the positive snapshot masses; no positive
lower cutoff is imposed on a mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem massPowerScale_pos {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    0 < massPowerScale n c a b := mul_pos (Real.rpow_pos_of_pos hn a) (Real.rpow_pos_of_pos hc b)

/-- The scalar in `pred:scaled-motion` times the snapshot child mass. -/
theorem prediction_mass_scale_identity {n c : ℝ} (hn : 0 < n) (hc : 0 < c)
    (p μ : ℝ) :
    massPowerScale n c (-(1/p)) (μ-1+1/p)*c = (c/n)^(1/p)*c^μ := by
  rw [massPowerScale,Real.rpow_neg hn.le,Real.div_rpow hc.le hn.le]
  have heq : c^(μ-1+1/p)*c = c^(1/p)*c^μ := by
    calc
      _ = c^(μ-1+1/p)*c^(1:ℝ) := by rw [Real.rpow_one]
      _ = c^((μ-1+1/p)+1) := (Real.rpow_add hc _ _).symm
      _ = c^(1/p+μ) := by congr 1; ring
      _ = _ := Real.rpow_add hc _ _
  calc
    (n^(1/p))⁻¹*c^(μ-1+1/p)*c = (n^(1/p))⁻¹*(c^(μ-1+1/p)*c) := by ring
    _ = (n^(1/p))⁻¹*(c^(1/p)*c^μ) := by rw [heq]
    _ = _ := by ring

theorem prediction_numerator_scale_identity {n c : ℝ} (hn : 0 < n) (μ : ℝ) :
    n^(μ-1)*c = n^μ*(c/n) := by
  rw [Real.rpow_sub hn,Real.rpow_one]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source snapshot shrinkage gives the one-sided denominator
comparison and preserves numerator motion with its child-mass factor. -/

noncomputable section
namespace LipschitzHilbert

theorem prediction_mass_scale_factor {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (p μ : ℝ) :
    massPowerScale n c (-(1/p)) (μ-1+1/p) = (c/n)^(1/p)*c^(μ-1) := by
  rw [massPowerScale, Real.rpow_neg hn.le, Real.div_rpow hc.le hn.le,
    Real.rpow_add hc]
  ring

section RealVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply the source shrinkage to the original amplitude, before mass
normalization. The resulting model denominator is below every moved one. -/
theorem source_prediction_denominator_shrink {n n' c c' p μ ε : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hp : 0 < p) (hε : 0 ≤ ε) (U : E →ₗᵢ[ℝ] E) (A A' : E)
    (hmotion : ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        U (massPowerScale n c (-(1/p)) (μ-1+1/p) • A)‖ ≤
      ε*(c/n)^(1/p)*c^μ) :
    (c/n)*‖c^(μ-1) • radialShrink (2*ε*c) A‖^p ≤
      (c'/n')*‖c'^(μ-1) • A'‖^p := by
  let s := massPowerScale n c (-(1/p)) (μ-1+1/p)
  let s' := massPowerScale n' c' (-(1/p)) (μ-1+1/p)
  have hs : 0 ≤ s := (massPowerScale_pos hn hc _ _).le
  have hmotion' : ‖s' • A'-U (s • A)‖ ≤ s*(2*ε*c) := by
    apply hmotion.trans
    have heq := prediction_mass_scale_identity hn hc p μ
    have heq' : ε*(c/n)^(1/p)*c^μ = s*(ε*c) := by
      calc
        _ = ε*((c/n)^(1/p)*c^μ) := by ring
        _ = ε*(s*c) := by rw [← heq]
        _ = _ := by ring
    rw [heq']
    exact mul_le_mul_of_nonneg_left (by nlinarith) hs
  have hnorm : ‖U (s • A)‖ = s*‖A‖ := by
    rw [U.norm_map, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hb := scaled_radialShrink_power_le_of_error
    (show 0 ≤ 2*ε*c by positivity) hs hp.le A (s' • A') (U (s • A)) hnorm hmotion'
  have hleft : s • radialShrink (2*ε*c) A =
      (c/n)^(1/p) • (c^(μ-1) • radialShrink (2*ε*c) A) := by
    rw [← mul_smul]
    exact congrArg (fun r : ℝ => r • radialShrink (2*ε*c) A)
      (prediction_mass_scale_factor hn hc p μ)
  have hright : s' • A' = (c'/n')^(1/p) • (c'^(μ-1) • A') := by
    rw [← mul_smul]
    exact congrArg (fun r : ℝ => r • A') (prediction_mass_scale_factor hn' hc' p μ)
  rw [hleft,hright,norm_weighted_smul_rpow hp (div_pos hc hn).le,
    norm_weighted_smul_rpow hp (div_pos hc' hn').le] at hb
  exact hb

end RealVector

section ComplexVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shrinking the snapshot costs another two copies of the same
relative-child-mass error. The common diagonal carrier stays explicit. -/
theorem source_prediction_shrunk_numerator {n c μ ε K : ℝ}
    (hn : 0 < n) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hK : n^μ ≤ K)
    (U : E →ₗᵢ[ℂ] E) (A actual : E) (lam : ℂ) (hlam : ‖lam‖ ≤ 1)
    (hmotion : ‖actual-((n^(μ-1):ℝ):ℂ) • (lam • U A)‖ ≤ ε*K*(c/n)) :
    ‖actual-((n^(μ-1):ℝ):ℂ) •
      (lam • U (radialShrink (2*ε*c) A))‖ ≤ (3*ε*K)*(c/n) := by
  have hscalar : 0 ≤ n^(μ-1) := Real.rpow_nonneg hn.le _
  have hshrink : ‖A-radialShrink (2*ε*c) A‖ ≤ 2*ε*c := by
    rw [norm_sub_rev]
    exact norm_radialShrink_sub_le (by positivity) A
  have herror : ‖((n^(μ-1):ℝ):ℂ) • (lam • U A)-
      ((n^(μ-1):ℝ):ℂ) • (lam • U (radialShrink (2*ε*c) A))‖ ≤
      2*ε*K*(c/n) := by
    rw [← smul_sub, ← smul_sub, ← map_sub, norm_smul, norm_smul, U.norm_map,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscalar]
    calc
      _ ≤ n^(μ-1)*(1*(2*ε*c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hlam hshrink (norm_nonneg _) zero_le_one) hscalar
      _ = (2*ε)*(n^μ*(c/n)) := by
        rw [← prediction_numerator_scale_identity hn]
        ring
      _ ≤ (2*ε)*(K*(c/n)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (div_nonneg hc hn.le)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖actual-((n^(μ-1):ℝ):ℂ) • (lam • U A)‖+
        ‖((n^(μ-1):ℝ):ℂ) • (lam • U A)-
          ((n^(μ-1):ℝ):ℂ) • (lam • U (radialShrink (2*ε*c) A))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε*K*(c/n)+2*ε*K*(c/n) := add_le_add hmotion herror
    _ = _ := by ring

end ComplexVector
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceBalancedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The balanced branch of §9 for actual mass-normalized child amplitudes.
The one-sided denominator comparison is derived from scaled amplitude
motion, and the numerator uses the original child-mass error budget. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics

theorem source_normalized_numerator_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (μ : ℝ) (lam : ℂ) (A : E) :
    (((c/n)^(1-μ):ℝ):ℂ) • (lam • (c^(μ-1) • A)) =
      ((n^(μ-1):ℝ):ℂ) • (lam • A) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,smul_smul,smul_smul]
  congr 1
  have hscalar := congrArg (fun r : ℝ => (r : ℂ))
    (child_normalization_coefficient (μ := μ) hn hc)
  push_cast at hscalar
  calc
    _ = (↑((c/n)^(1-μ)) * ↑(c^(μ-1))) * lam := mul_right_comm _ _ _
    _ = _ := by rw [hscalar]

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_normalized_modulated_numerator_eq
    {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (μ : ℝ) (lam : ℂ)
    (frequency : κ → ℝ) (b : ℝ) (A : EuclideanSpace ℂ κ) :
    (((c/n)^(1-μ):ℝ):ℂ) •
      (lam • diagonalModulation frequency (c^(μ-1) • A) b) =
      ((n^(μ-1):ℝ):ℂ) • (lam • diagonalModulation frequency A b) := by
  have hcomm : diagonalModulation frequency (c^(μ-1) • A) b =
      c^(μ-1) • diagonalModulation frequency A b :=
    (diagonalModulationRealIsometry frequency b).map_smul _ _
  rw [hcomm,source_normalized_numerator_eq hn hc]

/-- Each child's actual radial shrink gives the summed denominator
ordering, without an additional denominator hypothesis. -/
theorem source_prediction_denominator_sum_shrink
    {n n' p μ ε : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 0 < p) (hε : 0 ≤ ε)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ) :
    1+∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p ≤
      1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
  apply add_le_add_right
  exact Finset.sum_le_sum fun i _ =>
    source_prediction_denominator_shrink hn hn' (hc i) (hc' i) hp hε
      (diagonalModulationRealIsometry (frequency i) b) (A i) (A' i) (hscaled i)

/-- In the balanced branch the normalized moving prediction is controlled
by the actual shrunken snapshot, with an error proportional to `u`. -/
theorem source_balanced_prediction_comparison
    {n n' p μ ε K u : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n)) :
    let X := fun i => (c i)^(μ-1) • radialShrink (2*ε*c i) (A i)
    let X' := fun i => (c' i)^(μ-1) • A' i
    let actual := energyRatio p (1+∑ i, (c' i/n')*‖X' i‖^p)
      (∑ i, ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • X' i)))
    let model := energyRatio p (1+∑ i, (c i/n)*‖X i‖^p)
      (∑ i, ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i) (X i) b)))
    Real.log actual-Real.log model ≤ 6*p*ε*K*u ∧
      actual ≤ Real.exp (6*p*ε*K*u)*model := by
  dsimp only
  let actualTerm := fun i => ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)
  let modelTerm := fun i => ((n^(μ-1):ℝ):ℂ) •
    (lam i • diagonalModulation (frequency i) (radialShrink (2*ε*c i) (A i)) b)
  have hden := source_prediction_denominator_sum_shrink hn hn' c c' hc hc'
    (by linarith : 0 < p) hε frequency b A A' hscaled
  have hdModel : 0 < 1+∑ i, (c i/n)*
      ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p := by
    have hs : 0 ≤ ∑ i, (c i/n)*
        ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (div_pos (hc i) hn).le
        (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  have hterms (i : ι) : ‖actualTerm i-modelTerm i‖ ≤ (3*ε)*K*(c i/n) := by
    have hb := source_prediction_shrunk_numerator hn (hc i).le hε hpower
      (diagonalModulationIsometry (frequency i) b) (A i) (actualTerm i) (lam i)
      (hlam i) (hnumerator i)
    simpa only [modelTerm,diagonalModulationIsometry_apply,mul_assoc] using hb
  have hlog := balanced_prediction_log_comparison hp hdModel hden
    (show 0 ≤ 3*ε by positivity) hK hu (fun i => c i/n) hsum actualTerm modelTerm hterms
  have hactual (i : ι) :
      ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • ((c' i)^(μ-1) • A' i))) =
      actualTerm i := source_normalized_numerator_eq hn' (hc' i) μ (lam' i) (A' i)
  have hmodel (i : ι) :
      ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i)
          ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)) = modelTerm i :=
    source_normalized_modulated_numerator_eq hn (hc i) μ (lam i) (frequency i) b _
  simp_rw [hactual,hmodel]
  have hlog' : Real.log (energyRatio p (1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p)
      (∑ i, actualTerm i))-
      Real.log (energyRatio p (1+∑ i, (c i/n)*
        ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) (∑ i, modelTerm i)) ≤
      6*p*ε*K*u := by nlinarith [hlog]
  refine ⟨hlog', ?_⟩
  have hposActual := energyRatio_pos (p := p) (hdModel.trans_le hden) (∑ i, actualTerm i)
  have hposModel := energyRatio_pos (p := p) hdModel (∑ i, modelTerm i)
  have hexp := Real.exp_le_exp.mpr (show
    Real.log (energyRatio p (1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p)
      (∑ i, actualTerm i)) ≤ 6*p*ε*K*u+
    Real.log (energyRatio p (1+∑ i, (c i/n)*
      ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) (∑ i, modelTerm i)) by linarith)
  simpa only [Real.exp_add,Real.exp_log hposActual,Real.exp_log hposModel] using hexp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePathPhaseMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the actual path phase in §9, `pred:path-errors`.
The scalar phase costs only the off-path mass, including when it is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- Sum the individual numerator errors before removing the moving path
phase. The two errors may have different sizes. -/
theorem finite_rotated_off_path_motion {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (l : ι → ℝ) (W W' : ι → E)
    {lam lam' : ℂ} {q η K u : ℝ}
    (hlam : lam ≠ 0) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hweight : ‖lam'-lam‖ ≤ q*‖lam‖)
    (hsum : ∑ i ∈ s, l i ≤ u)
    (hW : ∀ i ∈ s, ‖W i‖ ≤ K*l i)
    (hmove : ∀ i ∈ s, ‖W' i-W i‖ ≤ η*K*l i) :
    ‖(scalarPhase lam')⁻¹ • (∑ i ∈ s, W' i) -
      (scalarPhase lam)⁻¹ • (∑ i ∈ s, W i)‖ ≤ (η+2*q)*K*u := by
  have hlam' := (scalarPhase_relative_motion hlam hq1 hweight).1
  have hphase := scalarPhase_inverse_motion hlam hq1 hweight
  have hsumW : ‖∑ i ∈ s, W i‖ ≤ K*u := by
    calc
      _ ≤ ∑ i ∈ s, ‖W i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, K*l i := Finset.sum_le_sum hW
      _ = K*(∑ i ∈ s, l i) := (Finset.mul_sum ..).symm
      _ ≤ K*u := mul_le_mul_of_nonneg_left hsum hK
  have hsumMove : ‖(∑ i ∈ s, W' i)-(∑ i ∈ s, W i)‖ ≤ η*K*u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ s, ‖W' i-W i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, η*K*l i := Finset.sum_le_sum hmove
      _ = (η*K)*(∑ i ∈ s, l i) := (Finset.mul_sum ..).symm
      _ ≤ η*K*u := mul_le_mul_of_nonneg_left hsum (mul_nonneg hη hK)
  have heq : (scalarPhase lam')⁻¹ • (∑ i ∈ s, W' i) -
      (scalarPhase lam)⁻¹ • (∑ i ∈ s, W i) =
      (scalarPhase lam')⁻¹ • ((∑ i ∈ s, W' i)-(∑ i ∈ s, W i)) +
      ((scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹) • (∑ i ∈ s, W i) := by
    simp only [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(scalarPhase lam')⁻¹ • ((∑ i ∈ s, W' i)-(∑ i ∈ s, W i))‖ +
        ‖((scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹) • (∑ i ∈ s, W i)‖ :=
      norm_add_le _ _
    _ = ‖(∑ i ∈ s, W' i)-(∑ i ∈ s, W i)‖ +
        ‖(scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹‖*‖∑ i ∈ s, W i‖ := by
      rw [norm_smul,norm_inv,norm_scalarPhase hlam',inv_one,one_mul,norm_smul]
    _ ≤ η*K*u+(2*q)*(K*u) := add_le_add hsumMove
      (mul_le_mul hphase hsumW (norm_nonneg _) (by positivity))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_GraphPathBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact dominant-path coordinates for the graph prediction

The distinguished diagonal carrier and scalar phase are removed explicitly.
The graph prediction then has the path baseline used in §9, with constant
path vector and residual denominator and an oscillating off-path numerator.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Fintype κ] in
theorem phase_inverse_mul (z : ℂ) (hz : z ≠ 0) : (scalarPhase z)⁻¹ * z = (‖z‖ : ℂ) := by
  rw [scalarPhase_eq_div, inv_div]
  field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceDominantPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dominant-path coordinates for the source prediction. The path
amplitude stays unshrunk; only the complementary children are shrunk. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- Removing the snapshot path carrier is an exact isometry. -/
theorem diagonalModulation_inverse (f : κ → ℝ) (v : EuclideanSpace ℂ κ) (b : ℝ) :
    diagonalModulation (fun k => -f k) (diagonalModulation f v b) b = v := by
  apply PiLp.ext
  intro k
  change (v k * character (f k) b) * character (-f k) b = v k
  rw [mul_assoc,character_mul]
  simp [character]

/-- Exact dominant coordinates for a finite normalized prediction. The
rotation may be the inverse of the actual path carrier. -/
theorem source_path_prediction_identity
    (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {p μ : ℝ} (hp : 0 < p) (hl : 0 < l i₀) (hlam : lam i₀ ≠ 0) :
    let Y := (l i₀)^(1/p) • U (X i₀)
    let C := (l i₀)^(1-μ-1/p)*‖lam i₀‖
    let R := ∑ i : RemainderIndex i₀, l i*‖X i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i))
    energyRatio p (1+∑ i, l i*‖X i‖^p)
      (∑ i, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) =
      energyRatio p (1+‖Y‖^p+R) (C • Y+Z) := by
  classical
  dsimp only
  have hscale : ((l i₀)^(1-μ-1/p)*‖lam i₀‖)*(l i₀)^(1/p) =
      (l i₀)^(1-μ)*‖lam i₀‖ := by
    calc
      _ = ((l i₀)^(1-μ-1/p)*(l i₀)^(1/p))*‖lam i₀‖ := by ring
      _ = (l i₀)^((1-μ-1/p)+(1/p))*‖lam i₀‖ := by rw [← Real.rpow_add hl]
      _ = _ := by congr 2; ring
  have hpath : (scalarPhase (lam i₀))⁻¹ •
      U ((((l i₀)^(1-μ):ℝ):ℂ) • (lam i₀ • X i₀)) =
      ((l i₀)^(1-μ-1/p)*‖lam i₀‖) • ((l i₀)^(1/p) • U (X i₀)) := by
    rw [U.map_smul,U.map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
    congr 1
    calc
      _ = (((l i₀)^(1-μ):ℝ):ℂ)*((scalarPhase (lam i₀))⁻¹*lam i₀) := by ring
      _ = _ := by
        rw [phase_inverse_mul _ hlam]
        apply Complex.ext <;> simp only [RCLike.ofReal_eq_complex_ofReal,Complex.mul_re,Complex.mul_im,
          Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
        exact hscale.symm
  have hvector :
      ((l i₀)^(1-μ-1/p)*‖lam i₀‖) • ((l i₀)^(1/p) • U (X i₀))+
        (scalarPhase (lam i₀))⁻¹ • U
          (∑ i : RemainderIndex i₀, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) =
      (scalarPhase (lam i₀))⁻¹ • U
        (∑ i, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀,U.map_add,smul_add,hpath]
  have hden : 1+∑ i, l i*‖X i‖^p =
      1+‖(l i₀)^(1/p) • U (X i₀)‖^p+
        ∑ i : RemainderIndex i₀, l i*‖X i‖^p := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀,
      norm_weighted_smul_rpow hp hl.le,U.norm_map]
    ring
  rw [hden,hvector]
  unfold energyRatio
  simp only [norm_smul,norm_inv,norm_scalarPhase hlam,inv_one,one_mul,U.norm_map]

/-- The scaled source amplitude is the actual path vector, including
its child fraction. No lower bound on that fraction is needed. -/
theorem source_path_vector_motion {n n' c c' p μ ε K : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hcn : c ≤ n) (hp : 0 < p) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hK : n^μ ≤ K) (f : κ → ℝ) (b : ℝ) (A A' : EuclideanSpace ℂ κ)
    (hscaled : ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
      diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ ≤
      ε*(c/n)^(1/p)*c^μ) :
    ‖(c'/n')^(1/p) • diagonalModulation (fun k => -f k) (c'^(μ-1) • A') b-
      (c/n)^(1/p) • (c^(μ-1) • A)‖ ≤ ε*K := by
  have hnrm : ‖diagonalModulation (fun k => -f k)
      (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
      massPowerScale n c (-(1/p)) (μ-1+1/p) • A‖ =
      ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ := by
    calc
      _ = ‖diagonalModulation (fun k => -f k)
          (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
          diagonalModulation (fun k => -f k)
            (diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b) b‖ := by
        rw [diagonalModulation_inverse]
      _ = ‖diagonalModulation (fun k => -f k)
          (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
            diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b) b‖ := by
        exact congrArg norm ((diagonalModulationIsometry (fun k => -f k) b).map_sub _ _).symm
      _ = _ := norm_diagonalModulation _ _ _
  have hfrac : (c/n)^(1/p) ≤ 1 := Real.rpow_le_one
    (div_pos hc hn).le ((div_le_one hn).mpr hcn) (by positivity)
  have hpower : c^μ ≤ K := (Real.rpow_le_rpow hc.le hcn hμ).trans hK
  calc
    _ = ‖diagonalModulation (fun k => -f k)
        (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
        massPowerScale n c (-(1/p)) (μ-1+1/p) • A‖ := by
      rw [prediction_mass_scale_factor hn hc, prediction_mass_scale_factor hn' hc']
      rw [mul_smul,mul_smul]
      have hmap : diagonalModulation (fun k => -f k)
          ((c'/n')^(1/p) • (c'^(μ-1) • A')) b =
          (c'/n')^(1/p) • diagonalModulation (fun k => -f k) (c'^(μ-1) • A') b :=
        (diagonalModulationRealIsometry (fun k => -f k) b).map_smul _ _
      rw [hmap]
    _ ≤ ε*(c/n)^(1/p)*c^μ := hnrm.le.trans hscaled
    _ ≤ ε*1*K := mul_le_mul
      (mul_le_mul_of_nonneg_left hfrac hε) hpower
      (Real.rpow_nonneg hc.le μ) (by positivity)
    _ = ε*K := by ring

/-- Snapshot path size and its moved counterpart use the same parent
mass scale as the off-path coefficient budget. -/
theorem source_path_vector_size {n c p μ C K : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hcn : c ≤ n) (hp : 0 < p)
    (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hsize : C*n^μ ≤ K)
    (A : EuclideanSpace ℂ κ) (hA : ‖A‖ ≤ C*c) :
    ‖(c/n)^(1/p) • (c^(μ-1) • A)‖ ≤ K := by
  have hx : ‖c^(μ-1) • A‖ ≤ C*n^μ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hc.le _)]
    calc
      _ ≤ c^(μ-1)*(C*c) := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hc.le _)
      _ = C*c^μ := by
        rw [Real.rpow_sub hc,Real.rpow_one]
        field_simp
      _ ≤ C*n^μ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcn hμ) hC
  have hf : (c/n)^(1/p) ≤ 1 := Real.rpow_le_one (div_pos hc hn).le
    ((div_le_one hn).mpr hcn) (by positivity)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (div_pos hc hn).le _)]
  calc
    _ ≤ 1*(C*n^μ) := mul_le_mul hf hx (norm_nonneg _) zero_le_one
    _ ≤ K := by simpa only [one_mul] using hsize

/-- The one-sided source shrink bounds add over precisely the complementary
children; no comparison of the full path denominator is assumed. -/
theorem source_off_path_residual_order
    {n n' p μ ε : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 0 < p) (hε : 0 ≤ ε) (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ) :
    (∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) ≤
      ∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
  have hb := source_prediction_denominator_sum_shrink hn hn' c c' hc hc' hp hε f b A A' hscaled
  linarith

theorem source_numerator_term_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n c μ C : ℝ} (hn : 0 < n) (_hc : 0 < c) (_hC : 0 ≤ C)
    (A : E) (lam : ℂ) (hA : ‖A‖ ≤ C*c) (hlam : ‖lam‖ ≤ 1) :
    ‖((n^(μ-1):ℝ):ℂ) • (lam • A)‖ ≤ (C*n^μ)*(c/n) := by
  rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _)]
  calc
    _ ≤ n^(μ-1)*(1*(C*c)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hlam hA (norm_nonneg _) zero_le_one) (Real.rpow_nonneg hn.le _)
    _ = C*(n^(μ-1)*c) := by ring
    _ = _ := by rw [prediction_numerator_scale_identity hn]; ring

/-- The removed path phase and carrier do not change the off-path size. -/
theorem source_off_path_coordinate_size {n μ ε K C u : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hC : 0 ≤ C) (hsize : C*n^μ ≤ K)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hmass : ∑ i, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (pathLam : ℂ) (hpath : pathLam ≠ 0) :
    ‖(scalarPhase pathLam)⁻¹ • U (∑ i, ((n^(μ-1):ℝ):ℂ) •
      (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))‖ ≤ K*u := by
  have hterm (i : ι) : ‖((n^(μ-1):ℝ):ℂ) •
      (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b)‖ ≤ K*(c i/n) := by
    have ha : ‖diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b‖ ≤ C*c i := by
      rw [norm_diagonalModulation]
      exact (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  rw [norm_smul,norm_inv,norm_scalarPhase hpath,inv_one,one_mul,U.norm_map]
  calc
    _ ≤ ∑ i, ‖((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b)‖ := norm_sum_le _ _
    _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
    _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
    _ ≤ K*u := mul_le_mul_of_nonneg_left hmass hK

/-- Simultaneously rotate all complementary children into the path frame.
The coefficient of the error still vanishes with their total mass. -/
theorem source_off_path_coordinate_motion
    {n n' μ ε K C q u : ℝ} (hn : 0 < n) (_hn' : 0 < n')
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (_hC : 0 ≤ C) (hpower : n^μ ≤ K)
    (hsize : C*n^μ ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hmass : ∑ i, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (pathLam pathLam' : ℂ) (hpath : pathLam ≠ 0)
    (hphase : ‖pathLam'-pathLam‖ ≤ q*‖pathLam‖) :
    ‖(scalarPhase pathLam')⁻¹ •
        U (∑ i, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))-
      (scalarPhase pathLam)⁻¹ •
        U (∑ i, ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i)
          (radialShrink (2*ε*c i) (A i)) b))‖ ≤ (3*ε+2*q)*K*u := by
  let W := fun i => U (((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i)
    (radialShrink (2*ε*c i) (A i)) b))
  let W' := fun i => U (((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
  have hterm (i : ι) : ‖W' i-W i‖ ≤ (3*ε)*K*(c i/n) := by
    dsimp only [W,W']
    rw [← U.map_sub,U.norm_map]
    simpa only [diagonalModulationIsometry_apply,mul_assoc] using source_prediction_shrunk_numerator hn (hc i).le hε hpower
      (diagonalModulationIsometry (f i) b) (A i)
      (((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)) (lam i) (hlam i) (hmove i)
  have hnorm (i : ι) : ‖W i‖ ≤ K*(c i/n) := by
    have hs : ‖radialShrink (2*ε*c i) (A i)‖ ≤ ‖A i‖ :=
      norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _
    dsimp only [W]
    rw [U.norm_map,norm_smul,norm_smul,norm_diagonalModulation,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hn.le _)]
    calc
      _ ≤ n^(μ-1)*(1*(C*c i)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hlam i) (hs.trans (hA i)) (norm_nonneg _) zero_le_one)
        (Real.rpow_nonneg hn.le _)
      _ = C*(n^(μ-1)*c i) := by ring
      _ = (C*n^μ)*(c i/n) := by rw [prediction_numerator_scale_identity hn]; ring
      _ ≤ K*(c i/n) := mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le
  have hb := finite_rotated_off_path_motion Finset.univ (fun i => c i/n) W W'
    hpath hq0 hq1 (show 0 ≤ 3*ε by positivity) hK hphase hmass
    (fun i _ => hnorm i) (fun i _ => hterm i)
  simpa only [W,W',map_sum] using hb

/-- The original child-mass error bounds imply all dominant-path errors
at once, with no assumed residual ordering. The scalar-coefficient bounds
are supplied by the complementary-mass theorem. -/
theorem source_dominant_coordinate_control
    {n n' p μ ε K C q u : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (hp : 0 < p) (hμ : 0 ≤ μ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hpower : n^μ ≤ K) (hsize : C*n^μ ≤ K)
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (i₀ : ι) (hcn : c i₀ ≤ n)
    (hmass : ∑ i : RemainderIndex i₀, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hpath : lam i₀ ≠ 0)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hqε : q ≤ ε)
    (hphase : ‖lam' i₀-lam i₀‖ ≤ q*‖lam i₀‖)
    (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n)) :
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    let Y := (c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)
    let Y' := (c' i₀/n')^(1/p) • U ((c' i₀)^(μ-1) • A' i₀)
    let R := ∑ i : RemainderIndex i₀,
      (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p
    let R' := ∑ i : RemainderIndex i₀, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))
    let Z' := (scalarPhase (lam' i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
    ‖Y‖ ≤ K ∧ ‖Y'‖ ≤ 2*K ∧ ‖Y'-Y‖ ≤ ε*K ∧ R ≤ R' ∧
      ‖Z'-Z‖ ≤ 5*ε*K*u ∧ ‖Z‖ ≤ K*u := by
  dsimp only
  have hy := source_path_vector_size hn (hc i₀) hcn hp hμ hC hsize (A i₀) (hA i₀)
  have hmoveY := source_path_vector_motion hn hn' (hc i₀) (hc' i₀) hcn hp hμ hε0
    hpower (f i₀) b (A i₀) (A' i₀) (hscaled i₀)
  have hy' : ‖(c' i₀/n')^(1/p) • diagonalModulation (fun k => -f i₀ k)
      ((c' i₀)^(μ-1) • A' i₀) b‖ ≤ 2*K := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      ((c' i₀/n')^(1/p) • diagonalModulation (fun k => -f i₀ k)
        ((c' i₀)^(μ-1) • A' i₀) b)
      ((c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)) 0
    simp only [sub_zero] at ht
    have he := mul_le_mul_of_nonneg_right hε1 hK
    linarith
  have hr := source_off_path_residual_order hn hn' (fun i : RemainderIndex i₀ => c i)
    (fun i : RemainderIndex i₀ => c' i) (fun i => hc i) (fun i => hc' i)
    hp hε0 (fun i => f i) b (fun i => A i) (fun i => A' i) (fun i => hscaled i)
  have hz := source_off_path_coordinate_motion hn hn' hε0 hK hC hpower hsize hq0 hq1
    (fun i : RemainderIndex i₀ => c i) (fun i => hc i) hmass (fun i => f i) b
    (diagonalModulationIsometry (fun k => -f i₀ k) b) (fun i => A i) (fun i => A' i)
    (fun i => lam i) (fun i => lam' i) (fun i => hlam i) (fun i => hA i)
    (fun i => hmove i) (lam i₀) (lam' i₀) hpath hphase
  have hs0 : 0 ≤ ∑ i : RemainderIndex i₀, c i/n :=
    Finset.sum_nonneg (fun i _ => (div_pos (hc i) hn).le)
  have hu : 0 ≤ u := hs0.trans hmass
  refine ⟨hy,hy',hmoveY,hr,hz.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 3*ε+2*q ≤ 5*ε) hK) hu
  · exact source_off_path_coordinate_size hn hε0 hK hC hsize
      (fun i : RemainderIndex i₀ => c i) (fun i => hc i) hmass (fun i => f i) b
      (diagonalModulationIsometry (fun k => -f i₀ k) b) (fun i => A i)
      (fun i => lam i) (fun i => hlam i) (fun i => hA i) (lam i₀) hpath

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceDominantBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant branch of the actual source comparison. Raw amplitude
motion and complementary-mass coefficient motion feed the proved logarithmic
comparison; the residual error is absorbed by the prescribed blend. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_dominant_prediction_comparison
    {n n' p μ ε K C q u θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (hp : 0 < p) (hμ : 0 ≤ μ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hpower : n^μ ≤ K) (hsize : C*n^μ ≤ K)
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (i₀ : ι) (hcn : c i₀ ≤ n)
    (hmass : ∑ i : RemainderIndex i₀, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hpath : lam i₀ ≠ 0)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hqε : q ≤ ε)
    (hphase : ‖lam' i₀-lam i₀‖ ≤ q*‖lam i₀‖)
    (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC0 : 0 ≤ (c i₀/n)^(1-μ-1/p)*‖lam i₀‖)
    (hC1 : (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 1)
    (hdrop : 1-(c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 2*u)
    (hcmove : |(c' i₀/n')^(1-μ-1/p)*‖lam' i₀‖-
      (c i₀/n)^(1-μ-1/p)*‖lam i₀‖| ≤ 24*ε*u)
    (hp4 : 4 ≤ p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : Real.exp (24*p*ε*(2*K)) ≤ 2)
    (habsorb : 2*24*p*ε*(2*K) ≤ θ) :
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    let Y := (c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)
    let Y' := (c' i₀/n')^(1/p) • U ((c' i₀)^(μ-1) • A' i₀)
    let R := ∑ i : RemainderIndex i₀,
      (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p
    let R' := ∑ i : RemainderIndex i₀, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))
    let Z' := (scalarPhase (lam' i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
    let cp := (c i₀/n)^(1-μ-1/p)*‖lam i₀‖
    let cp' := (c' i₀/n')^(1-μ-1/p)*‖lam' i₀‖
    energyRatio p (1+‖Y'‖^p+R') (cp' • Y'+Z') ≤
      Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*energyRatio p (1+‖Y‖^p+R) (cp • Y+Z)+θ) := by
  dsimp only
  have hK0 : 0 ≤ K := by linarith
  have hs0 : 0 ≤ ∑ i : RemainderIndex i₀, c i/n :=
    Finset.sum_nonneg (fun i _ => (div_pos (hc i) hn).le)
  have hu : 0 ≤ u := hs0.trans hmass
  obtain ⟨hY,hY',hYm,hR,hZm,hZ⟩ := source_dominant_coordinate_control hn hn' hp hμ
    hε0 hε1 hK0 hC hpower hsize c c' hc hc' i₀ hcn hmass f b A A' lam lam'
    hlam hpath hq0 hq1 hqε hphase hA hscaled hmove
  apply dominant_prediction_blended_domination hp4 (by norm_num : (1:ℝ) ≤ 24)
    (show 1 ≤ 2*K by linarith) hε0 hu hC0 hC1 _ hR _ _ _ _ _ hY' _ _ _ _ _ hsmall hθ0 hθ1 habsorb
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (div_pos (hc i) hn).le
      (Real.rpow_nonneg (norm_nonneg _) _))
  · exact hY.trans (by linarith)
  · exact hdrop.trans (by nlinarith)
  · exact hZ.trans (by nlinarith)
  · exact hYm.trans (by nlinarith [mul_nonneg hε0 hK0])
  · exact hcmove
  · exact hZm.trans (by nlinarith [mul_nonneg (mul_nonneg hε0 hK0) hu])

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed near-uniform averaging at the actual rounded source scale. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem source_step_tendsto_atTop : Tendsto SourceParameters.step atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ ((Real.tendsto_exp_atTop).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have h := Real.exp_le_exp.mpr (SourceParameters.log_step_bounds hL).1
  simpa only [Function.comp_apply, Real.exp_log (SourceParameters.step_pos L)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBalancedBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The balanced source prediction after blending with one. All denominator
and numerator bounds are obtained from the actual finite child data. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics

/-- A denominator at least one leaves the same logarithmic numerator bound. -/
theorem source_energyRatio_log_upper {E : Type*} [NormedAddCommGroup E]
    {p d K : ℝ} (hp : 1 ≤ p) (hd : 1 ≤ d) {x : E} (hx : ‖x‖ ≤ K) :
    Real.log (energyRatio p d x) ≤ p*K := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hzero : energyRatio p d (0:E) ≤ 1 := by
    rw [energyRatio,norm_zero,Real.zero_rpow (by linarith : p ≠ 0),add_zero]
    exact (div_le_one hd0).mpr hd
  have hzlog : Real.log (energyRatio p d (0:E)) ≤ 0 :=
    Real.log_nonpos (energyRatio_pos hd0 (0:E)).le hzero
  have hlog := (abs_le.mp (log_energyRatio_lipschitz hp hd0 x (0:E))).2
  simp only [sub_zero] at hlog
  have hb := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ p)
  linarith

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_balanced_prediction_blend
    {n n' p μ ε K u C θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC : 0 ≤ C) (hsize : C*n^μ ≤ K) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let X := fun i => (c i)^(μ-1) • radialShrink (2*ε*c i) (A i)
    let X' := fun i => (c' i)^(μ-1) • A' i
    let actual := energyRatio p (1+∑ i, (c' i/n')*‖X' i‖^p)
      (∑ i, ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • X' i)))
    let model := energyRatio p (1+∑ i, (c i/n)*‖X i‖^p)
      (∑ i, ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i) (X i) b)))
    actual ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*((1-θ)*model+θ) := by
  dsimp only
  have hcomparison := source_balanced_prediction_comparison hn hn' c c' hc hc' hp hε hK hpower
    hu hsum frequency b A A' lam lam' hlam hscaled hnumerator
  dsimp only at hcomparison
  have hterm (i : ι) :
      ‖(((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
        ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ ≤ K*(c i/n) := by
    rw [source_normalized_modulated_numerator_eq hn (hc i)]
    have ha : ‖diagonalModulation (frequency i) (radialShrink (2*ε*c i) (A i)) b‖ ≤ C*c i := by
      rw [norm_diagonalModulation]
      exact (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  have hnorm : ‖∑ i, (((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
      ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ ≤ K := by
    calc
      _ ≤ ∑ i, ‖(((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
        ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ := norm_sum_le _ _
      _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
      _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
      _ ≤ K*1 := mul_le_mul_of_nonneg_left hsum hK
      _ = K := mul_one K
  have hd : 1 ≤ 1+∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_pos (hc i) hn).le (Real.rpow_nonneg (norm_nonneg _) _))
  have hd' : 1 ≤ 1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_pos (hc' i) hn').le (Real.rpow_nonneg (norm_nonneg _) _))
  exact balanced_blended_prediction_domination
    (energyRatio_pos (zero_lt_one.trans_le hd') _)
    (energyRatio_pos (zero_lt_one.trans_le hd) _) hθ0 hθ1 (mul_nonneg (by linarith) hK) hu
    hcomparison.1 (source_energyRatio_log_upper hp hd hnorm)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source node ratio and its snapshot graph predictor, with the original
child amplitudes and masses kept explicit. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The graph averaging theorem applies to exactly the source snapshot. -/
theorem source_snapshot_graph_identity (p D n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) :
    sourceSnapshotPrediction p (phaseMu D p) n c A lam frequency b =
      graphPredictionValue frequency (fun i => c i/n)
        (fun i => (c i)^(phaseMu D p-1) • A i) lam D p b := by
  unfold sourceSnapshotPrediction graphPredictionValue predictionCoefficients
  rw [diagonalFourierSum_coefficients]
  simp only [mul_smul]

/-- The coefficient sum used by the line-grid theorem follows from the
original amplitudes and actual child fractions, including after shrinkage. -/
theorem source_snapshot_graph_coefficient_sum {p D n ε C K u : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : C*n^(phaseMu D p) ≤ K)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (hA : ∀ i, ‖A i‖ ≤ C*c i) (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hmass : ∑ i, c i/n ≤ u) :
    (∑ i, ‖predictionCoefficients (fun i => c i/n)
      (fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)) lam D p i‖) ≤ K*u := by
  have hterm (i : ι) : ‖predictionCoefficients (fun i => c i/n)
      (fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)) lam D p i‖ ≤
      K*(c i/n) := by
    unfold predictionCoefficients
    rw [mul_smul,source_normalized_numerator_eq hn (hc i)]
    have ha : ‖radialShrink (2*ε*c i) (A i)‖ ≤ C*c i :=
      (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  calc
    _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
    _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
    _ ≤ K*u := mul_le_mul_of_nonneg_left hmass hK

/-- The shrunken source comparison in the value notation used for assembly. -/
theorem source_balanced_values_blend
    {n n' p μ ε K u C θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC : 0 ≤ C) (hsize : C*n^μ ≤ K) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    sourcePredictionValue p μ n' c' A' lam' ≤
      Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        ((1-θ)*sourceSnapshotPrediction p μ n c
          (fun i => radialShrink (2*ε*c i) (A i)) lam frequency b+θ) :=
  source_balanced_prediction_blend hn hn' c c' hc hc' hp hε hK hpower hu hsum frequency b
    A A' lam lam' hlam hscaled hnumerator hC hsize hA hθ0 hθ1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source values in dominant-path coordinates, before estimates. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem diagonalModulation_real_smul (f : κ → ℝ) (a : ℝ)
    (A : EuclideanSpace ℂ κ) (b : ℝ) :
    diagonalModulation f (a • A) b = a • diagonalModulation f A b :=
  (diagonalModulationRealIsometry f b).map_smul _ _

theorem source_snapshot_value_as_prediction (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) :
    sourceSnapshotPrediction p μ n c A lam frequency b =
      sourcePredictionValue p μ n c (fun i => diagonalModulation (frequency i) (A i) b) lam := by
  unfold sourceSnapshotPrediction sourcePredictionValue
  simp only [← diagonalModulation_real_smul,norm_diagonalModulation]

/-- The source actual ratio in any common unitary path frame. -/
theorem source_prediction_path_value {n p μ : ℝ} (hn : 0 < n) (hp : 0 < p)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (hlam : lam i₀ ≠ 0) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    sourcePredictionValue p μ n c A lam =
      energyRatio p
        (1+‖(c i₀/n)^(1/p) • U ((c i₀)^(μ-1) • A i₀)‖^p+
          ∑ i : RemainderIndex i₀, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
        (((c i₀/n)^(1-μ-1/p)*‖lam i₀‖) •
          ((c i₀/n)^(1/p) • U ((c i₀)^(μ-1) • A i₀))+
          (scalarPhase (lam i₀))⁻¹ • U
            (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) • (lam i • A i))) := by
  have h := source_path_prediction_identity (μ := μ) (fun i => c i/n)
    (fun i => (c i)^(μ-1) • A i) lam i₀ U hp (div_pos (hc i₀) hn) hlam
  dsimp only at h
  have heq (i : ι) := source_normalized_numerator_eq hn (hc i) μ (lam i) (A i)
  unfold sourcePredictionValue
  simp_rw [heq] at h ⊢
  exact h

/-- The model leaves precisely the distinguished path unshrunk. -/
theorem source_snapshot_path_value {n p μ ε : ℝ} (hn : 0 < n) (hp : 0 < p)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (hlam : lam i₀ ≠ 0) (f : ι → κ → ℝ) (b : ℝ) :
    let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    sourceSnapshotPrediction p μ n c shrink lam f b =
      energyRatio p
        (1+‖(c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)‖^p+
          ∑ i : RemainderIndex i₀, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p)
        (((c i₀/n)^(1-μ-1/p)*‖lam i₀‖) •
          ((c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀))+
          (scalarPhase (lam i₀))⁻¹ • U
            (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
              (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))) := by
  dsimp only
  rw [source_snapshot_value_as_prediction]
  have h := source_prediction_path_value (μ := μ) hn hp c hc
    (fun i => diagonalModulation (f i)
      (if i = i₀ then A i else radialShrink (2*ε*c i) (A i)) b)
    lam i₀ hlam (diagonalModulationIsometry (fun k => -f i₀ k) b)
  have hoff (i : RemainderIndex i₀) :
      (if (i:ι) = i₀ then A i else radialShrink (2*ε*c i) (A i)) =
        radialShrink (2*ε*c i) (A i) := ite_eq_right i.property
  simpa only [ite_eq_left rfl,ite_true, if_true,hoff,← diagonalModulation_real_smul,norm_diagonalModulation,
    diagonalModulationIsometry_apply,diagonalModulation_inverse] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceDominantValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant comparison for the original source ratio, with the exact
coordinate changes discharged by the path identities. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_dominant_values_blend
    {n n' p μ ε K C q u θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (hp : 0 < p) (hμ : 0 ≤ μ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hpower : n^μ ≤ K) (hsize : C*n^μ ≤ K)
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (i₀ : ι) (hcn : c i₀ ≤ n)
    (hmass : ∑ i : RemainderIndex i₀, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hpath : lam i₀ ≠ 0)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hqε : q ≤ ε)
    (hphase : ‖lam' i₀-lam i₀‖ ≤ q*‖lam i₀‖)
    (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC0 : 0 ≤ (c i₀/n)^(1-μ-1/p)*‖lam i₀‖)
    (hC1 : (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 1)
    (hdrop : 1-(c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 2*u)
    (hcmove : |(c' i₀/n')^(1-μ-1/p)*‖lam' i₀‖-
      (c i₀/n)^(1-μ-1/p)*‖lam i₀‖| ≤ 24*ε*u)
    (hp4 : 4 ≤ p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : Real.exp (24*p*ε*(2*K)) ≤ 2)
    (habsorb : 2*24*p*ε*(2*K) ≤ θ) :
    let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
    sourcePredictionValue p μ n' c' A' lam' ≤
      Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*sourceSnapshotPrediction p μ n c shrink lam f b+θ) := by
  dsimp only
  have hlam' : lam' i₀ ≠ 0 := (scalarPhase_relative_motion hpath hq1 hphase).1
  rw [source_prediction_path_value hn' hp c' hc' A' lam' i₀ hlam'
    (diagonalModulationIsometry (fun k => -f i₀ k) b),
    source_snapshot_path_value hn hp c hc A lam i₀ hpath f b]
  exact source_dominant_prediction_comparison hn hn' hp hμ hε0 hε1 hK hC hpower hsize
    c c' hc hc' i₀ hcn hmass f b A A' lam lam' hlam hpath hq0 hq1 hqε hphase hA
    hscaled hmove hC0 hC1 hdrop hcmove hp4 hθ0 hθ1 hsmall habsorb

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

/-- The source's global top-mass bound grows by at most `exp(3 sqrt L)`
after taking the phase power, uniformly in the direction-count parameter. -/
theorem source_phase_mass_bound {D L N : ℝ}
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hN : 0 < N) (hlogN : Real.log N ≤ 2 * L) :
    N ^ phaseMu D (Real.sqrt L) ≤ Real.exp (3 * Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hμ := phaseMu_positive_le hD hp
  have hsq := Real.sq_sqrt hL0
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N * phaseMu D (Real.sqrt L) ≤ (2 * L) * phaseMu D (Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlogN hμ.1.le
    _ ≤ (2 * L) * ((4 / 3 : ℝ) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hμ.2 (by positivity)
    _ = (8 / 3 : ℝ) * Real.sqrt L := by
      field_simp [hp.ne']
      nlinarith
    _ ≤ 3 * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]

/-- The amplitude scale `L^C (1+N^mu)` is smaller than every fixed
positive power of the actual rounded dyadic step. This is the source's
subpower estimate used to absorb all marked-cell comparison errors. -/
theorem eventually_source_subpower_amplitude (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2 * L →
      L ^ C * (1 + N ^ phaseMu D (Real.sqrt L)) ≤ SourceParameters.step L ^ δ := by
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)
  have hlog : Tendsto (fun L : ℝ => Real.log L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).tendsto_div_nhds_zero
  have hroot : Tendsto (fun L : ℝ => Real.sqrt L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
    norm_num
  have hconst : Tendsto (fun L : ℝ => Real.log 2 / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Real.log 2)).mul (tendsto_inv_atTop_zero.comp hpow)
  have hsum := ((hlog.const_mul C).add hconst).add (hroot.const_mul 3)
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsum.eventually (gt_mem_nhds hδ)] with L hL hsmall
  intro D N hD hN hlogN
  have hL0 : 0 < L := by linarith
  have hpower : 0 < L ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hbudget : C * Real.log L + Real.log 2 + 3 * Real.sqrt L ≤ δ * L ^ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ hpower).mp
    convert hsmall.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmass := source_phase_mass_bound hD hL hN hlogN
  have hone : 1 ≤ Real.exp (3 * Real.sqrt L) := Real.one_le_exp (by positivity)
  calc
    _ ≤ L ^ C * (2 * Real.exp (3 * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (C * Real.log L + Real.log 2 + 3 * Real.sqrt L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hL0]
      rw [mul_comm C (Real.log L)]
      ring
    _ ≤ Real.exp (δ * L ^ (7 / 10 : ℝ)) := Real.exp_le_exp.mpr hbudget
    _ ≤ SourceParameters.step L ^ δ := by
      rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left (SourceParameters.log_step_bounds hL0.le).1 hδ.le).trans_eq
        (mul_comm δ _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceDominantGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual marked-cell factor in the dominant branch, combining
source amplitude comparison with the proved near-uniform graph averaging. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_dominant_grid_prediction :
    ∃ Cav L0 : ℝ, 1 ≤ Cav ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
      (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (D p K C ε θ freqBound u q : ℝ),
      1 ≤ D → 4 ≤ p → 1 ≤ K → 0 ≤ C → 0 ≤ ε → ε ≤ 1 → 0 ≤ θ → θ ≤ 1 →
      0 ≤ freqBound → 0 ≤ u → n^(phaseMu D p) ≤ K → C*n^(phaseMu D p) ≤ K →
      (∀ i, ‖A i‖ ≤ C*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      lam i₀ ≠ 0 → 0 ≤ q → q < 1 → q ≤ ε →
      0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ →
      (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 →
      1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u →
      Real.exp (24*p*ε*(2*K)) ≤ 2 → 2*24*p*ε*(2*K) ≤ θ →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ)
      (A' : ℝ → ι → EuclideanSpace ℂ κ) (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^(phaseMu D p)) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) →
      (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
            (4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
              p*freqBound*K*(grid.width/(grid.branching:ℝ)^level)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_supported_grid_prediction
  refine ⟨Cav,L0,hCav,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG c m n hc hn hm htotal frequency A lam
    i₀ D p K C ε θ freqBound u q hD hp hK hC hε hε1 hθ0 hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hpath hq0 hq1 hqε hC0 hC1 hdrop hsmall habsorb hsep hcard hfreqBound
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
  let X := fun i => (c i)^(phaseMu D p-1) • shrink i
  have hK0 : 0 ≤ K := by linarith
  have hx (i : RemainderIndex i₀) : X i =
      (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i) := by
    dsimp only [X,shrink]
    rw [ite_eq_right i.property]
  have hcoeffBase := source_snapshot_graph_coefficient_sum hn hε hC hK0 hsize
    (fun i : RemainderIndex i₀ => c i) (fun i => hc i) (fun i => A i) (fun i => lam i)
    (fun i => hA i) (fun i => hlam i) hoff
  have hcoeff : (∑ i : RemainderIndex i₀,
      ‖predictionCoefficients (fun i => c i/n) X lam D p i‖) ≤ K*u := by
    simpa only [predictionCoefficients,hx] using hcoeffBase
  have hcard' (S : Finset ι) (hs : ∀ i ∈ S, X i ≠ 0 ∨ i = i₀)
      (hind : (S:Set ι).Pairwise (fun i j => ¬G i j)) : (S.card:ℝ) ≤ D := by
    apply hcard S _ hind
    intro i hi
    by_cases he : i = i₀
    · exact Or.inr he
    · rcases hs i hi with hx | he'
      · exact Or.inl (fun hz => hx (by simp only [X,shrink,ite_eq_right he,hz,smul_zero]))
      · exact (he he').elim
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hG c m hc hm
    frequency (fun i => c i/n) X lam i₀ D p K u freqBound θ hD hp hsep hcard'
    (fun i => (div_pos (hc i) hn).le) htotal hlamGraph hK0 hu hfreq hcoeff
    hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  intro b hb
  have hsingle : c i₀/n ≤ ∑ i, c i/n :=
    Finset.single_le_sum (fun i _ => (div_pos (hc i) hn).le) (Finset.mem_univ i₀)
  have hcn : c i₀ ≤ n := (div_le_one hn).mp (hsingle.trans htotal)
  have hμ0 : 0 ≤ phaseMu D p := (phaseMu_positive_le hD (by linarith)).1.le
  have hcompare := source_dominant_values_blend hn (hn' b hb) (by linarith : 0 < p) hμ0
    hε hε1 hK hC hpower hsize c (c' b) hc (hc' b hb) i₀ hcn hoff frequency b
    A (A' b) lam (lam' b) hlam hpath hq0 hq1 hqε (hphase b hb) hA
    (hscaled b hb) (hnum b hb) hC0 hC1 hdrop (hcmove b hb) hp hθ0 hθ1 hsmall habsorb
  dsimp only at hcompare
  rw [source_snapshot_graph_identity] at hcompare
  calc
    _ ≤ Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*graphPredictionValue frequency (fun i => c i/n) X lam D p b+θ) := hcompare
    _ ≤ Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        (Real.exp ((4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
          p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ b) :=
      mul_le_mul_of_nonneg_left (hpoint b hb) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical parameters for the source prediction comparison.
All thresholds are uniform in the top family, phase dimension and mass. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

/-- A single small positive power controls the path comparison,
the convex blend and the mesh/mixture error. -/
theorem prediction_budget_of_subpower {G V F : ℝ}
    (hG : 1 ≤ G) (hV0 : 0 ≤ V) (hV : V ≤ G^(1/128:ℝ)) (hF : 0 ≤ F)
    (hsmall : 96 ≤ G^(7/128:ℝ)) (hcost : 27650+F ≤ G^(3/128:ℝ)) :
    Real.exp (48*V*G^(-(1/8:ℝ))) ≤ 2 ∧
      96*V*G^(-(1/8:ℝ)) ≤ G^(-(1/16:ℝ)) ∧
      27648*V^2*G^(-(1/8:ℝ))+(2+F)*V*G^(-(1/16:ℝ)) ≤ G^(-(1/32:ℝ)) := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hvε : V*G^(-(1/8:ℝ)) ≤ G^(-(15/128:ℝ)) := by
    calc
      _ ≤ G^(1/128:ℝ)*G^(-(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  have habsorb : 96*V*G^(-(1/8:ℝ)) ≤ G^(-(1/16:ℝ)) := by
    calc
      _ = 96*(V*G^(-(1/8:ℝ))) := by ring
      _ ≤ 96*G^(-(15/128:ℝ)) := mul_le_mul_of_nonneg_left hvε (by norm_num)
      _ ≤ G^(7/128:ℝ)*G^(-(15/128:ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  have htheta : G^(-(1/16:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hlog : (1/2:ℝ) ≤ Real.log 2 := by
    have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hb
    exact hb
  have hexp : Real.exp (48*V*G^(-(1/8:ℝ))) ≤ 2 := by
    have hx : 48*V*G^(-(1/8:ℝ)) ≤ Real.log 2 := by
      have hh := habsorb.trans htheta
      linarith
    exact (Real.exp_le_exp.mpr hx).trans_eq (Real.exp_log (by norm_num))
  have hsq : V^2 ≤ G^(1/128:ℝ)*G^(1/128:ℝ) := by
    have hh := mul_le_mul hV hV hV0 (Real.rpow_nonneg hG0.le (1/128:ℝ))
    simpa only [pow_two] using hh
  have hfirst : V^2*G^(-(1/8:ℝ)) ≤ G^(-(7/128:ℝ)) := by
    calc
      _ ≤ (G^(1/128:ℝ)*G^(1/128:ℝ))*G^(-(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hG0.le _)
      _ = G^(-(14/128:ℝ)) := by rw [← Real.rpow_add hG0,← Real.rpow_add hG0]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
  have hsecond : V*G^(-(1/16:ℝ)) ≤ G^(-(7/128:ℝ)) := by
    calc
      _ ≤ G^(1/128:ℝ)*G^(-(1/16:ℝ)) :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  refine ⟨hexp,habsorb,?_⟩
  calc
    _ = 27648*(V^2*G^(-(1/8:ℝ)))+(2+F)*(V*G^(-(1/16:ℝ))) := by ring
    _ ≤ 27648*G^(-(7/128:ℝ))+(2+F)*G^(-(7/128:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = (27650+F)*G^(-(7/128:ℝ)) := by ring
    _ ≤ G^(3/128:ℝ)*G^(-(7/128:ℝ)) :=
      mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hG0.le _)
    _ = _ := by rw [← Real.rpow_add hG0]; norm_num

/-- The source values `p=sqrt L`, `epsilon=G^(-1/8)` and
`theta=G^(-1/16)` meet the complete dominant-comparison budget. -/
theorem eventually_source_prediction_parameters (C F : ℝ) (_hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let G := SourceParameters.step L
      let ε := G^(-(1/8:ℝ))
      let θ := G^(-(1/16:ℝ))
      Real.exp (24*p*ε*(2*K)) ≤ 2 ∧
      2*24*p*ε*(2*K) ≤ θ ∧
      (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+F*G^(-(1/16:ℝ))*p*K ≤
        G^(-(1/32:ℝ)) := by
  have hsub := eventually_source_subpower_amplitude (C+1/2) (1/128) (by norm_num)
  have hsmall := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/128)).comp
    source_step_tendsto_atTop).eventually_ge_atTop 96
  have hcost := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/128)).comp
    source_step_tendsto_atTop).eventually_ge_atTop (27650+F)
  filter_upwards [hsub,hsmall,hcost,eventually_ge_atTop (1:ℝ)] with L hsub hsmall hcost hL
  intro D N hD hN hlogN
  dsimp only
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let K := L^C*(1+N^phaseMu D (Real.sqrt L))
  let V := Real.sqrt L*K
  have hV0 : 0 ≤ V := by dsimp [V,K]; positivity
  have hV : V ≤ SourceParameters.step L^(1/128:ℝ) := by
    calc
      _ = L^(C+1/2)*(1+N^phaseMu D (Real.sqrt L)) := by
        dsimp [V,K]
        rw [Real.rpow_add hL0,← Real.sqrt_eq_rpow]
        ring
      _ ≤ _ := hsub D N hD hN hlogN
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  obtain ⟨hexp,habsorb,hbudget⟩ := prediction_budget_of_subpower hG hV0 hV hF hsmall hcost
  refine ⟨?_,?_,?_⟩
  · convert hexp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp [V,K]
    ring
  · convert habsorb using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [V,K]
    ring
  · convert hbudget using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [V,K]
    ring

/-- The balanced branch fits inside the same error budget as the
dominant branch, so the final marked-cell exponent is common to both. -/
theorem balanced_prediction_cost_le_dominant {p K ε θ : ℝ}
    (hp : 1 ≤ p) (hK : 1 ≤ K) (hε : 0 ≤ ε) :
    6*p*ε*K+2*θ*(p*K) ≤
      12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)) := by
  have hx : 1 ≤ p*K := one_le_mul_of_one_le_of_one_le hp hK
  have hbase : 6*(p*K) ≤ 27648*(p*K)^2 := by nlinarith
  calc
    _ = 6*(p*K)*ε+θ*(p*(2*K)) := by ring
    _ ≤ 27648*(p*K)^2*ε+θ*(p*(2*K)) :=
      add_le_add (mul_le_mul_of_nonneg_right hbase hε) le_rfl
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBalancedGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual marked-cell factor in the balanced branch, combining
source amplitude comparison with the proved near-uniform graph averaging. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_balanced_grid_prediction :
    ∃ Cav L0 : ℝ, 1 ≤ Cav ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
      (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (D p K C ε θ freqBound u : ℝ),
      1 ≤ D → 4 ≤ p → 0 ≤ K → 0 ≤ C → 0 ≤ ε → 0 ≤ θ → θ ≤ 1 →
      0 ≤ freqBound → 1/2 ≤ u → n^(phaseMu D p) ≤ K → C*n^(phaseMu D p) ≤ K →
      (∀ i, ‖A i‖ ≤ C*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ)
      (A' : ℝ → ι → EuclideanSpace ℂ κ) (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^(phaseMu D p)) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (((6*p*ε*K+2*θ*(p*K))+
            (4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
              p*freqBound*K*(grid.width/(grid.branching:ℝ)^level)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_supported_grid_prediction
  refine ⟨Cav,L0,hCav,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG c m n hc hn hm htotal frequency A lam
    i₀ D p K C ε θ freqBound u hD hp hK hC hε hθ0 hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hsep hcard hfreqBound n' c' A' lam' hn' hc' hscaled hnum
  let X := fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)
  have hcoeff : (∑ i : RemainderIndex i₀,
      ‖predictionCoefficients (fun i => c i/n) X lam D p i‖) ≤ K*u :=
    source_snapshot_graph_coefficient_sum hn hε hC hK hsize
      (fun i : RemainderIndex i₀ => c i) (fun i => hc i) (fun i => A i) (fun i => lam i)
      (fun i => hA i) (fun i => hlam i) hoff
  have hcard' (S : Finset ι) (hs : ∀ i ∈ S, X i ≠ 0 ∨ i = i₀)
      (hind : (S:Set ι).Pairwise (fun i j => ¬G i j)) : (S.card:ℝ) ≤ D := by
    apply hcard S _ hind
    intro i hi
    rcases hs i hi with hx | he
    · exact Or.inl (fun hz => hx (by simp only [X,hz,smul_zero]))
    · exact Or.inr he
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hG c m hc hm
    frequency (fun i => c i/n) X lam i₀ D p K u freqBound θ hD hp hsep hcard'
    (fun i => (div_pos (hc i) hn).le) htotal hlamGraph hK (by linarith) hfreq hcoeff
    hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  intro b hb
  have hcompare := source_balanced_values_blend hn (hn' b hb) c (c' b) hc (hc' b hb)
    (by linarith : 1 ≤ p) hε hK hpower hu htotal frequency b A (A' b) lam (lam' b)
    hlam (hscaled b hb) (hnum b hb) hC hsize hA hθ0 hθ1
  rw [source_snapshot_graph_identity] at hcompare
  calc
    _ ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        ((1-θ)*graphPredictionValue frequency (fun i => c i/n) X lam D p b+θ) := hcompare
    _ ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        (Real.exp ((4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
          p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ b) :=
      mul_le_mul_of_nonneg_left (hpoint b hb) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGridParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source prediction scale gives one uniform marked-cell error in
both branches. The only mesh hypothesis is the explicit carrier oscillation
bound on a cell; the averaging measure and its remainder are already proved. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem source_grid_cost_le {p K θ Cav F freq mesh A R : ℝ}
    (hp : 0 ≤ p) (hK : 0 ≤ K) (hmesh : freq*mesh ≤ F*θ)
    (hbudget : A+(4*Cav+F)*θ*p*K ≤ R) :
    A+(4*Cav*θ*p*K+p*freq*K*mesh) ≤ R := by
  have hm := mul_le_mul_of_nonneg_left hmesh (mul_nonneg hp hK)
  calc
    _ = A+4*Cav*θ*p*K+(p*K)*(freq*mesh) := by ring
    _ ≤ A+4*Cav*θ*p*K+(p*K)*(F*θ) := add_le_add le_rfl hm
    _ = A+(4*Cav+F)*θ*p*K := by ring
    _ ≤ R := hbudget

/-- The balanced source factor has a normalized, measurable cell-constant
majorant with pointwise error `G^(-1/32) * u` at the actual parameters. -/
theorem eventually_source_balanced_grid_parameters (C F : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let Gstep := SourceParameters.step L
      let ε := Gstep^(-(1/8:ℝ))
      let θ := Gstep^(-(1/16:ℝ))
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
        (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
        (∑ i, c i/n) ≤ 1 →
      ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
        (i₀ : ι) (Aconst freqBound u : ℝ),
        0 ≤ Aconst → 0 ≤ freqBound → 1/2 ≤ u →
        n^(phaseMu D p) ≤ K → Aconst*n^(phaseMu D p) ≤ K →
        (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
        (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
        (∑ i : RemainderIndex i₀, c i/n) ≤ u →
        (∀ i j, i ≠ j → ¬G i j → ∀ k,
          1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
        (∀ S : Finset ι,
          (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
          (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
        (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
        freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
      ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ)
        (A' : ℝ → ι → EuclideanSpace ℂ κ) (lam' : ℝ → ι → ℂ),
        (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
        (∀ b ∈ grid.root, ∀ i,
          ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
            diagonalModulation (frequency i)
              (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
            ε*(c i/n)^(1/p)*(c i)^(phaseMu D p)) →
        (∀ b ∈ grid.root, ∀ i,
          ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
            ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
            ε*K*(c i/n)) →
        ∃ Γ : ℝ → ℝ, Measurable Γ ∧
          Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
          (∀ b, 0 ≤ Γ b) ∧
          (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
          (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
          ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
            Real.exp ((Gstep^(-(1/32:ℝ)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_balanced_grid_prediction
  have hparams := eventually_source_prediction_parameters C (4*Cav+F) hC (by linarith)
  filter_upwards [hparams,eventually_ge_atTop L0,eventually_ge_atTop (16:ℝ)]
    with L hparams hL hL16
  intro D N hD hN hlog
  dsimp only
  let p := Real.sqrt L
  let K := L^C*(1+N^phaseMu D p)
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let θ := SourceParameters.step L^(-(1/16:ℝ))
  have hp : 4 ≤ p := by
    dsimp [p]
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL16
  have hK : 1 ≤ K := by
    have hpow : 1 ≤ L^C := Real.one_le_rpow (by linarith) hC
    have hmass : 0 ≤ N^phaseMu D p := Real.rpow_nonneg hN.le _
    exact one_le_mul_of_one_le_of_one_le hpow (by linarith)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hε : 0 ≤ ε := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ : 0 ≤ θ := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ1 : θ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hbudget := (hparams D N hD hN hlog).2.2
  change (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
    (4*Cav+F)*θ*p*K ≤ SourceParameters.step L^(-(1/32:ℝ)) at hbudget
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff
    hsep hcard hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hsym
    c m n hc hn hm htotal frequency A lam i₀ D p K Aconst ε θ freqBound u
    hD hp (by linarith) hAconst hε hθ hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hsep hcard hfreqBound n' c' A' lam' hn' hc' hscaled hnum
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hcost := source_grid_cost_le (show 0 ≤ p by linarith) (show 0 ≤ K by linarith)
    hmesh ((add_le_add
      (balanced_prediction_cost_le_dominant (by linarith : 1 ≤ p) hK hε) le_rfl).trans hbudget)
  intro b hb
  exact (hpoint b hb).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcost (by linarith))) (hpos b))

/-- The unshrunk path vector in the dominant branch has the same final
marked-cell error as the balanced branch. All phase and mass hypotheses
remain the explicit local estimates proved for the original packets. -/
theorem eventually_source_dominant_grid_parameters (C F : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let Gstep := SourceParameters.step L
      let ε := Gstep^(-(1/8:ℝ))
      let θ := Gstep^(-(1/16:ℝ))
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
        (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
        (∑ i, c i/n) ≤ 1 →
      ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
        (i₀ : ι) (Aconst freqBound u q : ℝ),
        0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
        n^(phaseMu D p) ≤ K → Aconst*n^(phaseMu D p) ≤ K →
        (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
        (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
        (∑ i : RemainderIndex i₀, c i/n) ≤ u →
        lam i₀ ≠ 0 → 0 ≤ q → q < 1 → q ≤ ε →
        0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ →
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 →
        1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u →
        (∀ i j, i ≠ j → ¬G i j → ∀ k,
          1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
        (∀ S : Finset ι,
          (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
          (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
        (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
        freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
      ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ)
        (A' : ℝ → ι → EuclideanSpace ℂ κ) (lam' : ℝ → ι → ℂ),
        (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
        (∀ b ∈ grid.root, ∀ i,
          ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
            diagonalModulation (frequency i)
              (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
            ε*(c i/n)^(1/p)*(c i)^(phaseMu D p)) →
        (∀ b ∈ grid.root, ∀ i,
          ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
            ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
            ε*K*(c i/n)) →
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) →
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u) →
        ∃ Γ : ℝ → ℝ, Measurable Γ ∧
          Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
          (∀ b, 0 ≤ Γ b) ∧
          (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
          (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
          ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
            Real.exp ((Gstep^(-(1/32:ℝ)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_dominant_grid_prediction
  have hparams := eventually_source_prediction_parameters C (4*Cav+F) hC (by linarith)
  filter_upwards [hparams,eventually_ge_atTop L0,eventually_ge_atTop (16:ℝ)]
    with L hparams hL hL16
  intro D N hD hN hlog
  dsimp only
  let p := Real.sqrt L
  let K := L^C*(1+N^phaseMu D p)
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let θ := SourceParameters.step L^(-(1/16:ℝ))
  have hp : 4 ≤ p := by
    dsimp [p]
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL16
  have hK : 1 ≤ K := by
    have hpow : 1 ≤ L^C := Real.one_le_rpow (by linarith) hC
    have hmass : 0 ≤ N^phaseMu D p := Real.rpow_nonneg hN.le _
    exact one_le_mul_of_one_le_of_one_le hpow (by linarith)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hε : 0 ≤ ε := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hθ : 0 ≤ θ := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ1 : θ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  obtain ⟨hexp,habsorb,hbudget⟩ := hparams D N hD hN hlog
  change (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
    (4*Cav+F)*θ*p*K ≤ SourceParameters.step L^(-(1/32:ℝ)) at hbudget
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff
    hpath hq0 hq1 hqε hcoeff0 hcoeff1 hdrop hsep hcard hfreqBound hmesh
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hsym
    c m n hc hn hm htotal frequency A lam i₀ D p K Aconst ε θ freqBound u q
    hD hp hK hAconst hε hε1 hθ hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hpath hq0 hq1 hqε hcoeff0 hcoeff1 hdrop hexp habsorb hsep hcard hfreqBound
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hcost := source_grid_cost_le (show 0 ≤ p by linarith) (show 0 ≤ K by linarith)
    hmesh hbudget
  intro b hb
  exact (hpoint b hb).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcost hu)) (hpos b))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceEitherGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The balanced and dominant source constructions give one marked
predictor. Dominant-path hypotheses are only needed when the drop is small. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_grid_parameters_oai (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2*L →
    let p := Real.sqrt L
    let K := L^C*(1+N^phaseMu D p)
    let ε := SourceParameters.step L^(-(1/8:ℝ))
    let θ := SourceParameters.step L^(-(1/16:ℝ))
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) → (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (Aconst freqBound u q : ℝ),
      0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
      n^phaseMu D p ≤ K → Aconst*n^phaseMu D p ≤ K →
      (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
      freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ) (A' : ℝ → ι → EuclideanSpace ℂ κ)
      (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^phaseMu D p) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
        0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ∧
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 ∧
        1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u ∧
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  filter_upwards [eventually_source_balanced_grid_parameters C F hC hF,
    eventually_source_dominant_grid_parameters C F hC hF] with L hbalanced hdominant
  intro D N hD hN hlog
  dsimp only
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff hsep hcard
    hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum hdom
  by_cases hb : 1/2 ≤ u
  · exact hbalanced D N hD hN hlog ι κ grid level hlevel G hsym c m n hc hn hm htotal
      frequency A lam i₀ Aconst freqBound u hAconst hfreq hb hpower hsize hA hlam
      hlamGraph hoff hsep hcard hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum
  · obtain ⟨hpath,hq0,hq1,hqε,hcoef0,hcoef1,hdrop,hphase,hmove⟩ := hdom (lt_of_not_ge hb)
    exact hdominant D N hD hN hlog ι κ grid level hlevel G hsym c m n hc hn hm htotal
      frequency A lam i₀ Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam
      hlamGraph hoff hpath hq0 hq1 hqε hcoef0 hcoef1 hdrop hsep hcard hfreqBound hmesh
      n' c' A' lam' hn' hc' hscaled hnum hphase hmove

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.eventually_source_grid_parameters_oai := @OAI.LipschitzHilbert.eventually_source_grid_parameters_oai
