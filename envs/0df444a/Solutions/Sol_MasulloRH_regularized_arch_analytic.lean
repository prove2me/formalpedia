-- Prove2me | solution 1 for MasulloRH.regularized_arch_analytic
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:01:51.596476+00:00
-- url     : https://prove2.me/submissions/2583563a-247b-4522-b565-9ffa7ee2f604

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Elementary bound `log t · √t/(t²-1) ≤ 4 t^(-5/4)` for `t > 1`. -/
private lemma log_mul_weight_le {t : ℝ} (ht : 1 < t) :
    Real.log t * (Real.sqrt t / (t ^ 2 - 1)) ≤ 4 * t ^ (-5 / 4 : ℝ) := by
  have ht0 : 0 < t := by linarith
  set u : ℝ := t ^ (1 / 4 : ℝ) with hu
  have hu1 : 1 < u := Real.one_lt_rpow ht (by norm_num)
  have htu : t = u ^ 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hsq : Real.sqrt t = u ^ 2 := by
    rw [htu, show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpow : t ^ (-5 / 4 : ℝ) = 1 / u ^ 5 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, one_div, ← Real.rpow_neg ht0.le]
    norm_num
  have hlog : Real.log t = 4 * Real.log u := by
    rw [htu, Real.log_pow]; norm_num
  have hlu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
  rw [hsq, hpow, hlog, htu]
  have hd : 0 < (u ^ 4) ^ 2 - 1 := by nlinarith [one_lt_pow₀ hu1 (n := 8) (by norm_num)]
  have h7 : 1 ≤ u ^ 7 := one_le_pow₀ hu1.le
  rw [mul_one_div, ← mul_div_assoc, div_le_div_iff₀ hd (by positivity)]
  have : Real.log u * u ^ 2 * u ^ 5 ≤ (u - 1) * u ^ 7 := by
    have := mul_le_mul_of_nonneg_right hlu (by positivity : (0:ℝ) ≤ u ^ 7)
    nlinarith
  nlinarith

/-- The integrand of `regularizedArch`. -/
private noncomputable def archF (s : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (1 / 2 - s) - (t : ℂ) ^ (-2 : ℂ)) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)

/-- Its `s`-derivative. -/
private noncomputable def archF' (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (1 / 2 - s) * Complex.log t * (-1) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)

/-- The half-plane `Re s > 1/2`. -/
private def archHalfPlane : Set ℂ := {x : ℂ | (1 / 2 : ℝ) < x.re}

private lemma isOpen_archHalfPlane : IsOpen archHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma convex_archHalfPlane : Convex ℝ archHalfPlane :=
  convex_halfSpace_re_gt _

private lemma archF_hasDerivAt (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => archF s t) (archF' x t) x := by
  have h1 : HasDerivAt (fun s : ℂ => 1 / 2 - s) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 / 2 : ℂ)
  have h2 := h1.const_cpow (c := (t : ℂ)) (Or.inl (by exact_mod_cast ht.ne'))
  have h3 := (h2.sub_const ((t : ℂ) ^ (-2 : ℂ))).mul_const
    ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)
  simpa [archF, archF'] using h3

private lemma norm_archF'_le {x : ℂ} (hx : x ∈ archHalfPlane) {t : ℝ} (ht : 1 < t) :
    ‖archF' x t‖ ≤ 4 * t ^ (-5 / 4 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hw : 0 ≤ Real.sqrt t / (t ^ 2 - 1) := by
    apply div_nonneg (Real.sqrt_nonneg _); nlinarith
  have hlog : Complex.log (t : ℂ) = (Real.log t : ℂ) := (Complex.ofReal_log ht0.le).symm
  simp only [archF', norm_mul, norm_neg, norm_one, mul_one, hlog,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg ht.le), abs_of_nonneg hw]
  have hre : (1 / 2 - x).re ≤ 0 := by
    simp only [archHalfPlane, mem_ofPred_eq] at hx
    simp; linarith
  have hp : t ^ (1 / 2 - x).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le hre
  have := log_mul_weight_le ht
  have h0 : 0 ≤ Real.log t * (Real.sqrt t / (t ^ 2 - 1)) :=
    mul_nonneg (Real.log_nonneg ht.le) hw
  calc t ^ (1 / 2 - x).re * Real.log t * (Real.sqrt t / (t ^ 2 - 1))
      = t ^ (1 / 2 - x).re * (Real.log t * (Real.sqrt t / (t ^ 2 - 1))) := by ring
    _ ≤ 1 * (Real.log t * (Real.sqrt t / (t ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_right hp h0
    _ ≤ 4 * t ^ (-5 / 4 : ℝ) := by linarith

private lemma archF_five_halves (t : ℝ) : archF (5 / 2) t = 0 := by
  simp only [archF]
  norm_num

/-- Pointwise domination of the integrand on the half-plane. -/
private lemma norm_archF_le {x : ℂ} (hx : x ∈ archHalfPlane) {t : ℝ} (ht : 1 < t) :
    ‖archF x t‖ ≤ 4 * t ^ (-5 / 4 : ℝ) * ‖x - 5 / 2‖ := by
  have h52 : (5 / 2 : ℂ) ∈ archHalfPlane := by
    simp only [archHalfPlane, mem_ofPred_eq]; norm_num
  have := convex_archHalfPlane.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => archF s t) (f' := fun s => archF' s t)
    (fun y _ => (archF_hasDerivAt y (by linarith)).hasDerivWithinAt)
    (fun y hy => norm_archF'_le hy ht) h52 hx
  simpa [archF_five_halves] using this

private lemma integrableOn_bound :
    IntegrableOn (fun t : ℝ => 4 * t ^ (-5 / 4 : ℝ)) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 4

private lemma archF_measurable (x : ℂ) : Measurable (archF x) := by
  unfold archF; fun_prop

private lemma archF'_measurable (x : ℂ) : Measurable (archF' x) := by
  unfold archF'; fun_prop

/-- The integrand is integrable on `(1, ∞)` for `Re s > 1/2`. -/
private lemma archF_integrableOn {x : ℂ} (hx : x ∈ archHalfPlane) :
    IntegrableOn (archF x) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_bound.mul_const ‖x - 5 / 2‖)
    (archF_measurable x).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => norm_archF_le hx ht)

private lemma regularizedArch_hasDerivAt {x : ℂ} (hx : x ∈ archHalfPlane) :
    HasDerivAt MasulloRH.regularizedArch (∫ t in Ioi (1 : ℝ), archF' x t) x := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := archF) (F' := archF') (x₀ := x) (bound := fun t : ℝ => 4 * t ^ (-5 / 4 : ℝ))
    (isOpen_archHalfPlane.mem_nhds hx)
    (Eventually.of_forall fun y => (archF_measurable y).aestronglyMeasurable)
    (archF_integrableOn hx) (archF'_measurable x).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht y hy => norm_archF'_le hy ht))
    integrableOn_bound
    ((ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun t ht y _ => archF_hasDerivAt y (lt_trans one_pos ht)))
  exact this.2

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ MasulloRH.regularizedArch s :=
  (DifferentiableOn.analyticOnNhd
    (fun _ hx => (regularizedArch_hasDerivAt hx).differentiableAt.differentiableWithinAt)
    isOpen_archHalfPlane) s hs
