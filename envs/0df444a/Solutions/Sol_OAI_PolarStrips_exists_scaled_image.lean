-- Prove2me | solution 1 for OAI.PolarStrips.exists_scaled_image
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:13.881072+00:00
-- url     : https://prove2.me/submissions/a47c71de-971b-4c97-b59e-10cf7079a987

import Mathlib
import Definitions.Def_OAIQWSP000

section
-- module Solutions.OAIQW_SymmetricPolar.PotentialForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u27 u28 u29

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped Topology ContDiff

variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.ComplexPotential.oneTensorGroup
attribute [local instance] OAI.ComplexPotential.oneTensorSpace
attribute [local instance] OAI.ComplexPotential.twoTensorGroup
attribute [local instance] OAI.ComplexPotential.twoTensorSpace
theorem dc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : dc J φ x = dc J ψ x := by
  rw [dc, dc, h.fderiv_eq]

theorem ddc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : ddc J φ x = ddc J ψ x := by
  have he : dc J φ =ᶠ[𝓝 x] dc J ψ := h.eventuallyEq_nhds.mono (fun y hy => dc_congr J hy)
  simpa only [ddc, exteriorD] using congrArg alt he.fderiv_eq

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.RegularizedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36 u37

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace ComplexPotential

open TensorCalculus SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u36} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance maxOneGroup_r4569f5_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance maxOneSpace_r4569f5_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance maxTwoGroup_r4569f5_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance maxTwoSpace_r4569f5_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
theorem IsPSHAt.congr {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (he : ψ =ᶠ[𝓝 x] φ) : IsPSHAt J ψ x := by
  refine ⟨hφ.1.congr_of_eventuallyEq he, fun a => ?_⟩
  rw [ddc_congr J he]
  exact hφ.2 a

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology

open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
noncomputable section

theorem hasDerivAt_term (n : ℕ) (w : ℂ) : HasDerivAt (term n) (termDeriv n w) w := by
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  convert (((hasDerivAt_id w).pow (2*n+1)).const_mul ((-1 : ℂ)^n)).div_const
    ((2*(n : ℂ)+1)^2) using 1 <;> try rfl
  simp only [termDeriv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [hn]
  rfl

theorem norm_termDeriv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ r) (n : ℕ) : ‖termDeriv n w‖ ≤ r^n := by
  have hn : (1 : ℝ) ≤ 2 * n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc
    ‖termDeriv n w‖ = ‖w‖^(2*n) / (2*n+1) := by
      simp only [termDeriv, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 1
      norm_cast
    _ ≤ r^(2*n) := (div_le_self (pow_nonneg (norm_nonneg _) _) hn).trans
      (pow_le_pow_left₀ (norm_nonneg _) hw _)
    _ ≤ r^n := pow_le_pow_of_le_one hr hr1 (by omega)

theorem hasDerivAt_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, termDeriv n w) w := by
  obtain ⟨r, hwr, hr1⟩ := exists_between hw
  have hr : 0 < r := (norm_nonneg w).trans_lt hwr
  have hh := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_of_lt_one hr.le hr1) Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ => hasDerivAt_term n z)
    (fun n z hz => norm_termDeriv_le hr.le hr1.le ((by simpa [Metric.mem_ball] using hz : ‖z‖ < r).le) n)
    (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using hr)
    (show Summable (fun n => term n (0 : ℂ)) by simp)
    (show w ∈ Metric.ball 0 r by simpa using hwr)
  exact hh.const_mul _

theorem analyticOnNhd_F : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (hasDerivAt_F (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    w * deriv F w = (8 / (Real.pi^2) : ℝ) * Complex.arctan w := by
  rw [(hasDerivAt_F hw).deriv, mul_left_comm, ← tsum_mul_left]
  congr 1
  have he : (fun n : ℕ => w * termDeriv n w) =
      (fun n : ℕ => (-1)^n * w^(2*n+1) / (2*n+1)) := by
    funext n
    dsimp [termDeriv]
    rw [pow_succ]
    ring
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using (Complex.hasSum_arctan hw).tsum_eq

theorem norm_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖term n w‖ ≤ 1 / ((n : ℝ)+1)^2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  calc
    ‖term n w‖ = ‖w‖^(2*n+1) / (2*(n : ℝ)+1)^2 := by
      simp only [term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 2
      norm_cast
    _ ≤ 1 / (2*(n : ℝ)+1)^2 := div_le_div_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) hw) (sq_nonneg _)
    _ ≤ 1 / ((n : ℝ)+1)^2 := one_div_le_one_div_of_le (sq_pos_of_pos hn)
      (pow_le_pow_left₀ hn.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) 2)

theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))

theorem continuousOn_F_closedBall : ContinuousOn F (Metric.closedBall 0 1) := by
  apply ContinuousOn.const_mul _ _
  apply continuousOn_tsum (fun n => (by unfold term; fun_prop : Continuous (term n)).continuousOn)
    summable_bound
  intro n w hw
  exact norm_term_le (by simpa using hw) n

theorem cayley_re (w : ℂ) : (cayley w).re = (1 - ‖w‖^2) / normSq (1-w*I) := by
  rw [cayley, div_re, Complex.sq_norm]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add, normSq_apply]
  ring

theorem cayley_im (w : ℂ) : (cayley w).im = 2*w.re / normSq (1-w*I) := by
  rw [cayley, div_im]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add]
  ring

theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : 1-w*I ≠ 0 := by
    intro h
    have he := congr_arg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, norm_I, mul_one] at he
    linarith
  rw [cayley_re]
  exact div_pos (by nlinarith [norm_nonneg w]) (normSq_pos.mpr hn)

theorem arctan_re_eq {w : ℂ} (hw : ‖w‖ < 1) :
    (Complex.arctan w).re = (1/2 : ℝ) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayley_re_pos hw)))
  have ht := Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg, cayley_re, cayley_im] at ht
  have hn : normSq (1-w*I) ≠ 0 := by
    apply ne_of_gt
    have h := cayley_re_pos hw
    rw [cayley_re] at h
    exact (div_pos_iff.mp h).resolve_right (by rintro ⟨_, hneg⟩; exact (normSq_nonneg _).not_gt hneg) |>.2
  have he : (2*w.re/normSq (1-w*I)) / ((1-‖w‖^2)/normSq (1-w*I)) =
      2*w.re/(1-‖w‖^2) := by field_simp
  rw [he] at ht
  rw [Complex.arctan, mul_re]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, log_im]
  change 0 - (-1/2) * (cayley w).arg = _
  rw [← ht]
  ring

theorem re_mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    (w * deriv F w).re = (4 / Real.pi^2) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  rw [mul_deriv_F hw, re_ofReal_mul, arctan_re_eq hw]
  ring

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem norm_one_add_mul_I_sq (w : ℂ) : ‖1+w*I‖^2 = 1-2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, add_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, add_im, one_im, mul_im, zero_add, add_zero]
  ring

theorem norm_one_sub_mul_I_sq (w : ℂ) : ‖1-w*I‖^2 = 1+2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, sub_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, sub_im, one_im, mul_im, add_zero]
  ring

theorem one_add_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1+w*I ≠ 0 := by
  intro h
  have he : w*I = -1 := eq_neg_of_add_eq_zero_right h
  have hh := congr_arg norm he
  simp only [norm_mul, norm_I, mul_one, norm_neg, norm_one] at hh
  linarith

theorem one_sub_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1-w*I ≠ 0 := by
  have h := one_add_mul_I_ne_zero (w := -w) (by simpa using hw)
  simpa only [neg_mul, sub_eq_add_neg] using h

theorem arctan_im_eq (w : ℂ) :
    (Complex.arctan w).im = -(1/2 : ℝ) * Real.log (‖1+w*I‖/‖1-w*I‖) := by
  rw [Complex.arctan, mul_im]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, zero_add, log_re, norm_div]
  ring

theorem arctan_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hi : 0 < w.im) :
    0 < (Complex.arctan w).im := by
  have ha : 0 < ‖1+w*I‖ := norm_pos_iff.mpr (one_add_mul_I_ne_zero hw)
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1+w*I‖ < ‖1-w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_neg (div_pos ha hb) ((div_lt_one hb).mpr hab)
  linarith

theorem arctan_im_neg {w : ℂ} (hw : ‖w‖ < 1) (hi : w.im < 0) :
    (Complex.arctan w).im < 0 := by
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1-w*I‖ < ‖1+w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_pos ((one_lt_div hb).mpr hab)
  linarith

theorem arctan_im_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).im * w.im := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos (arctan_im_neg hw hi).le hi.le
  · simp [hi]
  · exact (mul_pos (arctan_im_pos hw hi) hi).le

theorem arctan_re_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).re * w.re := by
  rw [arctan_re_eq hw]
  have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rcases lt_trichotomy w.re 0 with hi | hi | hi
  · have hr : Real.arctan (2*w.re/(1-‖w‖^2)) < 0 :=
      Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hn)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hi.le
  · simp [hi]
  · have hr : 0 < Real.arctan (2*w.re/(1-‖w‖^2)) :=
      Real.arctan_pos.mpr (div_pos (by linarith) hn)
    positivity

theorem arctan_div_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (Complex.arctan w / w).re := by
  rw [div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hr := arctan_re_mul_nonneg hw
  have hi := arctan_im_mul_nonneg hw
  by_cases hre : w.re = 0
  · have him : w.im ≠ 0 := by
      intro h; apply hw0; exact Complex.ext (by simpa using hre) (by simpa using h)
    rcases lt_or_gt_of_ne him with him | him
    · have := mul_pos_of_neg_of_neg (arctan_im_neg hw him) him
      linarith
    · have := mul_pos (arctan_im_pos hw him) him
      linarith
  · have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have hp : 0 < (Complex.arctan w).re * w.re := by
      rw [arctan_re_eq hw]
      rcases lt_or_gt_of_ne hre with hre | hre
      · have h := Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos
          (by linarith : 2*w.re < 0) hn)
        exact mul_pos_of_neg_of_neg (by linarith) hre
      · have h := Real.arctan_pos.mpr (div_pos (by linarith : 0 < 2*w.re) hn)
        positivity
    linarith

@[simp] theorem deriv_F_zero : deriv F 0 = (8 / Real.pi^2 : ℝ) := by
  rw [(hasDerivAt_F (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
  have he : (∑' n : ℕ, termDeriv n 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp [termDeriv]
    · intro n hn
      have h : 2*n ≠ 0 := by omega
      simp [termDeriv, h]
  rw [he, mul_one]

theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  by_cases hw0 : w = 0
  · rw [hw0, deriv_F_zero, ofReal_re]
    positivity
  · have he : deriv F w = (8 / Real.pi^2 : ℝ) * (Complex.arctan w / w) := by
      apply (mul_left_cancel₀ hw0)
      rw [mul_deriv_F hw]
      field_simp
    rw [he, re_ofReal_mul]
    exact mul_pos (by positivity) (arctan_div_re_pos hw hw0)

theorem F_injOn : InjOn F (Metric.ball 0 1) := by
  intro x hx y hy hxy
  by_contra hn
  have hd : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖x+(t : ℂ)*(y-x)‖ < 1 := by
    intro t ht
    have hh := (convex_ball (0 : ℂ) 1).add_smul_sub_mem hx hy ht
    simpa only [Metric.mem_ball, dist_zero_right, Complex.real_smul] using hh
  let H : ℝ → ℝ := fun t => (F (x+(t : ℂ)*(y-x))/(y-x)).re
  have hh : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt H (deriv F (x+(t : ℂ)*(y-x))).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hc := ((hasDerivAt_id (t : ℂ)).mul_const (y-x)).const_add x
    have hm := (hf.comp (t : ℂ) hc).div_const (y-x)
    have he : deriv F (x+(t : ℂ)*(y-x)) * (1*(y-x)) / (y-x) =
        deriv F (x+(t : ℂ)*(y-x)) := by field_simp
    rw [he] at hm
    exact hm.real_of_complex
  have hmono : StrictMonoOn H (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  simp only [H, ofReal_zero, zero_mul, add_zero, ofReal_one, one_mul, add_sub_cancel] at hlt
  rw [hxy] at hlt
  exact lt_irrefl _ hlt

theorem re_F_imaginary (t : ℝ) : (F ((t : ℂ)*I)).re = 0 := by
  have h : (starRingEnd ℂ) ((t : ℂ)*I) = -((t : ℂ)*I) := by simp
  have he := F_conj ((t : ℂ)*I)
  rw [h, F_neg] at he
  have hre := congr_arg Complex.re he
  simp only [neg_re, conj_re] at hre
  linarith

theorem re_F_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < (F w).re := by
  let H : ℝ → ℝ := fun t => (F ((t : ℂ)+(w.im : ℂ)*I)).re
  have hseg : ∀ t ∈ Icc 0 w.re, ‖(t : ℂ)+(w.im : ℂ)*I‖ < 1 := by
    intro t ht
    have he : ‖(t : ℂ)+(w.im : ℂ)*I‖^2 = t^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hh : ‖w‖^2 = w.re^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hn : ‖w‖^2 < 1 := by nlinarith [norm_nonneg w]
    nlinarith [norm_nonneg ((t : ℂ)+(w.im : ℂ)*I), ht.1, ht.2]
  have hh : ∀ t ∈ Icc 0 w.re, HasDerivAt H (deriv F ((t : ℂ)+(w.im : ℂ)*I)).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hm := hf.comp (t : ℂ) ((hasDerivAt_id _).add_const ((w.im : ℂ)*I))
    convert hm.real_of_complex using 1 <;> first | rfl | simp
  have hmono : StrictMonoOn H (Icc 0 w.re) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 w.re)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have he : (w.re : ℂ)+(w.im : ℂ)*I = w := by simp
  simpa only [H, ofReal_zero, zero_add, re_F_imaginary, he] using hlt

theorem re_F_neg {w : ℂ} (hw : ‖w‖ < 1) (hr : w.re < 0) : (F w).re < 0 := by
  have h := re_F_pos (w := -w) (by simpa using hw) (by simpa using neg_pos.mpr hr)
  simpa only [F_neg, neg_re, neg_pos] using h

theorem re_F_eq_zero {w : ℂ} (hr : w.re = 0) : (F w).re = 0 := by
  have he : w = (w.im : ℂ)*I := by apply Complex.ext <;> simp [hr]
  rw [he, re_F_imaginary]

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem g_F {w : ℂ} (hw : ‖w‖ < 1) : g (F w) = w :=
  F_injOn.leftInvOn_invFunOn (by simpa using hw)

theorem F_g {z : ℂ} (hz : z ∈ D) : F (g z) = z :=
  Function.invFunOn_eq hz

theorem norm_g_lt {z : ℂ} (hz : z ∈ D) : ‖g z‖ < 1 := by
  have h := Function.invFunOn_mem hz
  simpa [g] using h

theorem zero_mem_D : (0 : ℂ) ∈ D := ⟨0, by simp, F_zero⟩

@[simp] theorem g_zero : g 0 = 0 := by
  simpa using g_F (by simp : ‖(0 : ℂ)‖ < 1)

theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  intro h
  have hh := deriv_F_re_pos hw
  rw [h, zero_re] at hh
  exact lt_irrefl _ hh

theorem analyticOnNhd_g : AnalyticOnNhd ℂ g D := by
  rintro z ⟨w, hw, rfl⟩
  have hw' : ‖w‖ < 1 := by simpa using hw
  apply (analyticAt_comp_iff_of_deriv_ne_zero (analyticOnNhd_F w hw)
    (deriv_F_ne_zero hw')).mp
  apply analyticAt_id.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
  exact (g_F (by simpa using hv)).symm

theorem isOpen_D : IsOpen D := by
  rcases analyticOnNhd_F.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with h | h
  · obtain ⟨c, hc⟩ := h
    have hz : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
    have hh : (1/2 : ℂ) ∈ Metric.ball 0 1 := by norm_num [Metric.mem_ball, norm_div]
    have he := F_injOn hz hh ((hc 0 hz).trans (hc _ hh).symm)
    norm_num at he
  · exact h _ Subset.rfl Metric.isOpen_ball

theorem isBounded_D : Bornology.IsBounded D := by
  apply ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn continuousOn_F_closedBall).isBounded.subset
  exact image_mono Metric.ball_subset_closedBall

theorem continuousOn_g : ContinuousOn g D := analyticOnNhd_g.continuousOn

theorem deriv_g_F {w : ℂ} (hw : ‖w‖ < 1) : deriv g (F w) = (deriv F w)⁻¹ := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hg := (analyticOnNhd_g _ hFw).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_F hw).differentiableAt.hasDerivAt
  have hc := hg.comp w hf
  have he : g ∘ F =ᶠ[𝓝 w] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hw : w ∈ Metric.ball 0 1)] with z hz
    exact g_F (by simpa using hz)
  have hid := hc.congr_of_eventuallyEq he.symm
  have hm : deriv g (F w) * deriv F w = 1 := hid.unique (hasDerivAt_id w)
  apply mul_right_cancel₀ (deriv_F_ne_zero hw)
  rw [hm, inv_mul_cancel₀ (deriv_F_ne_zero hw)]

theorem re_g_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) : 0 < (g z).re := by
  by_contra h
  rcases (le_of_not_gt h).eq_or_lt with he | he
  · have hh := re_F_eq_zero he
    rw [F_g hz] at hh
    linarith
  · have hh := re_F_neg (norm_g_lt hz) he
    rw [F_g hz] at hh
    linarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem summable_odd_sq : Summable (fun n : ℕ => 1/(2*(n : ℝ)+1)^2) := by
  have h := hasSum_zeta_two.summable.comp_injective (i := fun n : ℕ => 2*n+1)
    (by intro n m h; dsimp at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

theorem tsum_odd_sq : (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) = Real.pi^2/8 := by
  have he : HasSum (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) (Real.pi^2/24) := by
    have hh : HasSum (fun n : ℕ => (1/4 : ℝ) * (1/(n : ℝ)^2))
        ((1/4 : ℝ)*(Real.pi^2/6)) := hasSum_zeta_two.mul_left _
    have eqf : (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) =
        (fun n : ℕ => (1/4 : ℝ)*(1/(n : ℝ)^2)) := by
      funext n
      push_cast
      simp only [mul_pow, div_mul_eq_div_div]
      norm_num
      ring
    rw [eqf, show Real.pi^2/24 = (1/4 : ℝ)*(Real.pi^2/6) by ring]
    exact hh
  have ho : HasSum (fun n : ℕ => 1/((2*n+1 : ℕ) : ℝ)^2)
      (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_odd_sq.hasSum
  have h := (HasSum.even_add_odd (f := fun n : ℕ => 1/(n : ℝ)^2) he ho).unique hasSum_zeta_two
  linarith

@[simp] theorem F_I : F (I : ℂ) = (I : ℂ) := by
  have he : (fun n : ℕ => term n I) = (fun n : ℕ => (I : ℂ) * ((1/(2*(n : ℝ)+1)^2 : ℝ) : ℂ)) := by
    funext n
    have hp : (-1 : ℂ)^n * (I : ℂ)^(2*n+1) = (I : ℂ) := by
      rw [pow_succ, pow_mul, I_sq]
      have h1 : (-1 : ℂ)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
      linear_combination I * h1
    simp only [term, hp, ofReal_div, ofReal_one, ofReal_pow, ofReal_add, ofReal_mul,
      ofReal_ofNat, ofReal_natCast]
    ring
  rw [F, he, tsum_mul_left, ← Complex.ofReal_tsum, tsum_odd_sq]
  push_cast
  field_simp [Real.pi_ne_zero]

@[simp] theorem T_one : T 1 = 1 := by simp [T]

theorem continuousOn_T : ContinuousOn T (Icc (-1) 1) := by
  have hh : ContinuousOn (fun r : ℝ => F ((r : ℂ)*I)) (Icc (-1) 1) := by
    apply continuousOn_F_closedBall.comp (by fun_prop)
    intro r hr
    simpa [Metric.mem_closedBall, norm_mul, norm_real, Real.norm_eq_abs, abs_le] using hr
  exact Complex.continuous_im.comp_continuousOn hh

theorem hasDerivAt_T {r : ℝ} (hr : |r| < 1) :
    HasDerivAt T (deriv F ((r : ℂ)*I)).re r := by
  have hf := (hasDerivAt_F (w := (r : ℂ)*I) (by simpa [norm_mul] using hr)).differentiableAt.hasDerivAt
  have hc := hf.comp (r : ℂ) ((hasDerivAt_id _).mul_const I)
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hc.comp_ofReal
  convert hm using 1 <;> first | rfl | simp

theorem strictMonoOn_T : StrictMonoOn T (Icc (-1) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) continuousOn_T
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact (hasDerivAt_T h).hasDerivWithinAt
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact deriv_F_re_pos (by simpa [norm_mul] using h)

theorem T_lt_one {r : ℝ} (hr : -1 ≤ r) (hr1 : r < 1) : T r < 1 := by
  have h := strictMonoOn_T ⟨hr, hr1.le⟩ (by norm_num : (1 : ℝ) ∈ Icc (-1) 1) hr1
  simpa using h

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem A_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < A w := by
  rw [A, re_mul_deriv_F hw]
  apply mul_pos (by positivity)
  apply Real.arctan_pos.mpr
  apply div_pos (by linarith)
  nlinarith [norm_nonneg w]

theorem hasDerivAt_horizontal_g {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => g ((h : ℂ)+(t : ℂ)*I))
      (deriv g ((v : ℂ)+(t : ℂ)*I)) v := by
  have hg := (analyticOnNhd_g _ hz).differentiableAt.hasDerivAt
  have hc := hg.comp (v : ℂ) ((hasDerivAt_id _).add_const ((t : ℂ)*I))
  convert hc.comp_ofReal using 1 <;> first | rfl | simp only [mul_one]

theorem horizontal_normSq_deriv {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2)
      (2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2) v := by
  have hh := (hasDerivAt_horizontal_g hz).norm_sq
  have he : deriv g ((v : ℂ)+(t : ℂ)*I) = (deriv F (g ((v : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [he] at hh
  convert hh using 1
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  simp only [A, Complex.sq_norm, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im, RCLike.re_to_complex]
  ring

theorem horizontal_normSq_deriv_pos {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 < v) :
    0 < 2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2 := by
  apply div_pos
  · exact mul_pos (by norm_num) (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hv)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz)))

theorem horizontal_segment_mem {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (_hv : 0 ≤ v) {h : ℝ} (hh : h ∈ Icc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  let R := ‖g ((v : ℂ)+(t : ℂ)*I)‖
  have hR : R < 1 := norm_g_lt hz
  let C := F '' Metric.closedBall (0 : ℂ) R
  have hCD : C ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    simpa using hw'.trans_lt hR
  have hCc : IsCompact C := by
    apply (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    exact continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hR.le)
  have hCm {a : ℝ} : (a : ℂ)+(t : ℂ)*I ∈ C ↔
      (a : ℂ)+(t : ℂ)*I ∈ D ∧ ‖g ((a : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hw' : ‖w‖ ≤ R := by simpa using hw
      refine ⟨hCD ⟨w, hw, he⟩, ?_⟩
      rw [← he, g_F (hw'.trans_lt hR)]
      exact hw'
    · rintro ⟨ha, hr⟩
      exact ⟨g _, by simpa using hr, F_g ha⟩
  let S := Icc h v ∩ (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) ⁻¹' C
  have hSc : IsCompact S := isCompact_Icc.inter_right (hCc.isClosed.preimage (by fun_prop))
  have hvS : v ∈ S := ⟨⟨hh.2, le_rfl⟩, hCm.mpr ⟨hz, le_rfl⟩⟩
  obtain ⟨a, ha, hmin⟩ := hSc.exists_isMinOn ⟨v, hvS⟩ (continuous_id.continuousOn)
  have haD := (hCm.mp ha.2).1
  have haR := (hCm.mp ha.2).2
  have hha : h ≤ a := ha.1.1
  by_cases he : a = h
  · simpa only [he] using haD
  have hha' : h < a := lt_of_le_of_ne hha (Ne.symm he)
  have ha0 : 0 < a := hh.1.trans_lt hha'
  have hopen : IsOpen ((fun b : ℝ => (b : ℂ)+(t : ℂ)*I) ⁻¹' D) :=
    isOpen_D.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a haD
  let d := min (a-h) ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdh : d < a-h := by dsimp [d]; linarith [min_le_left (a-h) ε]
  have hdε : d < ε := by dsimp [d]; linarith [min_le_right (a-h) ε]
  let b := a-d
  have hhb : h < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hseg : ∀ x ∈ Icc b a, (x : ℂ)+(t : ℂ)*I ∈ D := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x-a ≤ 0)]
    have hxb : a-d ≤ x := hx.1
    linarith
  have hmono : StrictMonoOn (fun x : ℝ => ‖g ((x : ℂ)+(t : ℂ)*I)‖^2) (Icc b a) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc b a)
      (fun x hx => (horizontal_normSq_deriv (hseg x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (horizontal_normSq_deriv (hseg x (interior_subset hx))).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply horizontal_normSq_deriv_pos (hseg x hx')
    linarith [hx'.1, hh.1]
  have hnorm : ‖g ((b : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    have hm := hmono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba
    have hR0 : 0 ≤ R := norm_nonneg _
    nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I))]
  have hbS : b ∈ S := ⟨⟨hhb.le, hba.le.trans ha.1.2⟩,
    hCm.mpr ⟨hseg b ⟨le_rfl, hba.le⟩, hnorm⟩⟩
  have ham : a ≤ b := hmin hbS
  exact False.elim (not_le_of_gt hba ham)

theorem neg_conj_mem_D {z : ℂ} (hz : z ∈ D) : -(starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨-(starRingEnd ℂ) w, by simpa using hw, ?_⟩
  simp

theorem g_neg_conj {z : ℂ} (hz : z ∈ D) : g (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (g z) := by
  apply F_injOn (by simpa using norm_g_lt (neg_conj_mem_D hz))
    (by simpa using norm_g_lt hz)
  rw [F_g (neg_conj_mem_D hz)]
  simp [F_g hz]

theorem horizontal_segment_mem_signed {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    {h : ℝ} (hh : h ∈ uIcc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  rcases le_total 0 v with hv | hv
  · rw [uIcc_of_le hv] at hh
    exact horizontal_segment_mem hz hv hh
  · rw [uIcc_of_ge hv] at hh
    have he (a : ℝ) : -((starRingEnd ℂ) ((a : ℂ)+(t : ℂ)*I)) = ((-a : ℝ) : ℂ)+(t : ℂ)*I := by
      apply Complex.ext <;> simp
    have hz' := neg_conj_mem_D hz
    rw [he] at hz'
    have hh' : -h ∈ Icc 0 (-v) := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hhD := horizontal_segment_mem hz' (by linarith) hh'
    have hneg := neg_conj_mem_D hhD
    simpa only [he, neg_neg] using hneg

theorem axis_mem_D {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : (t : ℂ)*I ∈ D := by
  simpa using horizontal_segment_mem_signed hz (left_mem_uIcc (a := 0) (b := v))

theorem g_axis_re_zero {t : ℝ} (ht : (t : ℂ)*I ∈ D) : (g ((t : ℂ)*I)).re = 0 := by
  have he : -(starRingEnd ℂ) ((t : ℂ)*I) = (t : ℂ)*I := by simp
  have hh := g_neg_conj ht
  rw [he] at hh
  have hr := congr_arg Complex.re hh
  simp only [neg_re, conj_re] at hr
  linarith

theorem axis_image {t : ℝ} (ht : (t : ℂ)*I ∈ D) :
    ∃ r ∈ Ioo (-1 : ℝ) 1, g ((t : ℂ)*I) = (r : ℂ)*I ∧ T r = t := by
  let r := (g ((t : ℂ)*I)).im
  have he : g ((t : ℂ)*I) = (r : ℂ)*I := by
    apply Complex.ext <;> simp [r, g_axis_re_zero ht]
  have hr : |r| < 1 := by
    have hh := norm_g_lt ht
    rw [he] at hh
    simpa [norm_mul] using hh
  refine ⟨r, abs_lt.mp hr, he, ?_⟩
  have hh := congr_arg Complex.im (F_g ht)
  rw [he] at hh
  simpa [T] using hh

theorem im_mem_Ioo {z : ℂ} (hz : z ∈ D) : z.im ∈ Ioo (-1 : ℝ) 1 := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  obtain ⟨r, hr, _, ht⟩ := axis_image (axis_mem_D hz')
  rw [← ht]
  refine ⟨?_, T_lt_one hr.1.le hr.2⟩
  have h := strictMonoOn_T (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1) ⟨hr.1.le, hr.2.le⟩ hr.1
  simpa using h

theorem horizontal_radius_strictMono {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖) (Icc 0 v) := by
  have hm : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2) (Icc 0 v) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 v)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv hh)).continuousAt.continuousWithinAt)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv (interior_subset hh))).hasDerivWithinAt)
    intro h hh
    apply horizontal_normSq_deriv_pos (horizontal_segment_mem hz hv (interior_subset hh))
    have hh' : h ∈ Ioo 0 v := by simpa only [interior_Icc] using hh
    exact hh'.1
  intro a ha b hb hab
  have hh := hm ha hb hab
  nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I)), norm_nonneg (g ((b : ℂ)+(t : ℂ)*I))]

theorem T_norm_g_axis {t : ℝ} (ht : (t : ℂ)*I ∈ D) : T ‖g ((t : ℂ)*I)‖ = |t| := by
  obtain ⟨r, hr, he, hT⟩ := axis_image ht
  rw [he]
  simp only [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
  rcases le_total 0 r with hr0 | hr0
  · rw [abs_of_nonneg hr0, ← hT, abs_of_nonneg]
    have h := strictMonoOn_T.monotoneOn (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
      ⟨hr.1.le, hr.2.le⟩ hr0
    simpa using h
  · rw [abs_of_nonpos hr0, T_neg, ← hT, abs_of_nonpos]
    have h := strictMonoOn_T.monotoneOn ⟨hr.1.le, hr.2.le⟩
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) hr0
    simpa using h

theorem vertical_gap_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) :
    0 < T ‖g z‖ - |z.im| := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  have hnorm := horizontal_radius_strictMono hz' hr.le
    (left_mem_Icc.mpr hr.le) (right_mem_Icc.mpr hr.le) hr
  simp only [ofReal_zero, zero_add, re_add_im] at hnorm
  rw [← T_norm_g_axis (axis_mem_D hz')]
  have hh := strictMonoOn_T
    ⟨by linarith [norm_nonneg (g ((z.im : ℂ)*I))], (norm_g_lt (axis_mem_D hz')).le⟩
    ⟨by linarith [norm_nonneg (g z)], (norm_g_lt hz).le⟩ hnorm
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex MeasureTheory intervalIntegral
open scoped Topology ContDiff
noncomputable section

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (hc.intervalIntegrable 0 x)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun t _ => by
      apply (div_le_one (by positivity : 0 < 1+t^2)).mpr
      nlinarith [sq_nonneg t])
  simpa [integral_one_div_one_add_sq] using hi

theorem half_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x/2 ≤ Real.arctan x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (intervalIntegrable_const (c := (1/2 : ℝ)))
    (hc.intervalIntegrable 0 x) (fun t ht => by
      apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
      have h0 := ht.1
      have h1 := ht.2.trans hx1
      nlinarith)
  simpa [integral_one_div_one_add_sq, div_eq_mul_inv] using hi

theorem reciprocal_arctan {x : ℝ} (hx : 0 < x) :
    1 / Real.arctan x ≤ 2 / Real.pi + 2/x := by
  have ha : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  rcases le_total x 1 with hx1 | hx1
  · have hh := half_le_arctan hx.le hx1
    have hdiv : 1 / Real.arctan x ≤ 2/x := by
      apply (div_le_div_iff₀ ha hx).mpr
      linarith
    apply hdiv.trans
    have hp : 0 < 2 / Real.pi := by positivity
    linarith
  · have hh : Real.pi / 2 - Real.arctan x ≤ 1/x := by
      rw [← Real.arctan_inv_of_pos hx]
      simpa only [one_div] using arctan_le_self (inv_nonneg.mpr hx.le)
    have hA : Real.pi / 4 ≤ Real.arctan x := by
      simpa using Real.arctan_strictMono.monotone hx1
    have hπA : 1 ≤ Real.pi * Real.arctan x := by
      have hp := Real.pi_gt_three
      nlinarith [mul_le_mul_of_nonneg_left hA Real.pi_pos.le]
    have hfirst : (Real.pi/2-Real.arctan x) / Real.arctan x ≤ (1/x)/Real.arctan x :=
      div_le_div_of_nonneg_right hh ha.le
    have hsecond : (2/Real.pi)*((1/x)/Real.arctan x) ≤ 2/x := by
      apply (le_div_iff₀ hx).mpr
      have he : (2/Real.pi)*((1/x)/Real.arctan x)*x = 2/(Real.pi*Real.arctan x) := by
        field_simp
      rw [he]
      apply (div_le_iff₀ (mul_pos Real.pi_pos ha)).mpr
      linarith
    have hthird := mul_le_mul_of_nonneg_left hfirst
      (by positivity : 0 ≤ 2/Real.pi)
    have he : (2/Real.pi)*((Real.pi/2-Real.arctan x)/Real.arctan x) =
        1/Real.arctan x - 2/Real.pi := by field_simp
    rw [he] at hthird
    linarith

theorem norm_circleTop (r s : ℝ) : ‖circleTop r s‖ = |r| := by
  have hh : ‖circleTop r s‖^2 = r^2 := by
    rw [Complex.sq_norm, normSq_apply, circleTop_re, circleTop_im]
    nlinarith [Real.sin_sq_add_cos_sq s]
  nlinarith [sq_abs r, norm_nonneg (circleTop r s), abs_nonneg r]

theorem continuous_circleTop (r : ℝ) : Continuous (circleTop r) := by
  unfold circleTop; fun_prop

theorem hasDerivAt_F_im_circleTop {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    HasDerivAt (fun s => (F (circleTop r s)).im) (-A (circleTop r s)) s := by
  have hnorm : ‖(r : ℂ)*(Complex.sin s+Complex.cos s*I)‖ < 1 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    change ‖circleTop r s‖ < 1
    rw [norm_circleTop]
    exact hr
  have hd := ((Complex.hasDerivAt_sin (s : ℂ)).add
    ((Complex.hasDerivAt_cos (s : ℂ)).mul_const I)).const_mul (r : ℂ)
  have hf := (hasDerivAt_F hnorm).differentiableAt.hasDerivAt
  have hh := hf.comp (s : ℂ) hd
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hh.comp_ofReal
  convert hm using 1 <;> try rfl
  · funext x
    simp only [circleTop, ofReal_sin, ofReal_cos, Function.comp_apply, Pi.add_apply,
      Complex.imCLM_apply]
  · simp only [Complex.imCLM_apply, A, circleTop, ← ofReal_sin, ← ofReal_cos,
      mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, add_zero, zero_add, zero_sub, neg_re, neg_im]
    ring

theorem continuous_A_circleTop {r : ℝ} (hr : |r| < 1) :
    Continuous (fun s => A (circleTop r s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hs : circleTop r s ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, norm_circleTop] using hr
  exact Complex.continuous_re.continuousAt.comp
    (((continuous_circleTop r).continuousAt).mul
      (((analyticOnNhd_F _ hs).deriv.continuousAt).comp (continuous_circleTop r).continuousAt))

theorem gap_integral {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    T r - (F (circleTop r s)).im = ∫ x in 0..s, A (circleTop r x) := by
  have hh := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F_im_circleTop hr x)
    ((continuous_A_circleTop hr).neg.intervalIntegrable 0 s)
  rw [intervalIntegral.integral_neg, circleTop_zero] at hh
  change -(∫ x in 0..s, A (circleTop r x)) = (F (circleTop r s)).im - T r at hh
  linarith

theorem A_circleTop_le {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    A (circleTop r s) ≤ (8*r/(Real.pi^2*(1-r^2)))*s := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  have hnorm : ‖circleTop r s‖ < 1 := by simpa only [norm_circleTop] using hrabs
  rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc ⟨hs, by linarith [Real.pi_pos]⟩
  have hx : 0 ≤ 2*(r*Real.sin s)/(1-r^2) := by positivity
  calc
    _ ≤ (4/Real.pi^2) * (2*(r*Real.sin s)/(1-r^2)) := by
      exact mul_le_mul_of_nonneg_left (arctan_le_self hx) (by positivity)
    _ ≤ (4/Real.pi^2) * (2*(r*s)/(1-r^2)) := by
      gcongr
      exact Real.sin_le hs
    _ = _ := by field_simp; ring

theorem gap_le_square {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    T r - (F (circleTop r s)).im ≤ s^2/(1-r) := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  rw [gap_integral hrabs]
  have hh := integral_mono_on (μ := volume) hs ((continuous_A_circleTop hrabs).intervalIntegrable 0 s)
    ((show Continuous (fun x : ℝ => (8*r/(Real.pi^2*(1-r^2)))*x) from by fun_prop).intervalIntegrable 0 s)
    (fun x hx => A_circleTop_le hr hr1 hx.1 (hx.2.trans hs1))
  have he : (∫ x in 0..s, (8*r/(Real.pi^2*(1-r^2)))*x) =
      (4*r/(Real.pi^2*(1-r^2)))*s^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [he] at hh
  apply hh.trans
  have hd : 0 < 1-r^2 := by nlinarith
  have h1 : 0 < 1-r := by linarith
  have hco : 4*r/(Real.pi^2*(1-r^2)) ≤ 1/(1-r) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos Real.pi_pos) hd) h1).mpr
    have hp := Real.pi_gt_three
    have heq : 1-r^2 = (1-r)*(1+r) := by ring
    rw [heq]
    have haux : 4*r ≤ Real.pi^2*(1+r) := by
      have hp4 : 0 ≤ Real.pi^2-4 := by nlinarith
      nlinarith [mul_nonneg hp4 hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr haux) h1.le]
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using mul_le_mul_of_nonneg_right hco (sq_nonneg s)

theorem reciprocal_A_circleTop {r s : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s ≤ Real.pi/2) :
    1 / A (circleTop r s) ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs (by linarith [Real.pi_pos])
  have hnorm : ‖circleTop r s‖ < 1 := by simpa [norm_circleTop, abs_of_pos hr0] using hr1
  let X := 2*(r*Real.sin s)/(1-r^2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < Real.arctan X := Real.arctan_pos.mpr hX
  have he : 1 / A (circleTop r s) = (Real.pi^2/4) * (1/Real.arctan X) := by
    rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
    dsimp [X]
    field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (reciprocal_arctan hX)
    (by positivity : 0 ≤ Real.pi^2/4)
  apply hh.trans
  have hratio : (1+r)/r ≤ 4 := by
    apply (div_le_iff₀ hr0).mpr
    linarith
  have hsinbound : (1-r)/Real.sin s ≤ (Real.pi/2)*((1-r)/s) := by
    apply (div_le_iff₀ hsin).mpr
    have hx := Real.mul_le_sin hs.le hs1
    have hy : s ≤ (Real.pi/2)*Real.sin s := by
      have hp := mul_le_mul_of_nonneg_left hx (Real.pi_pos.le)
      field_simp at hp
      linarith
    have hz := mul_le_mul_of_nonneg_left hy (show 0 ≤ (1-r)/s by positivity)
    have heq : (1-r)/s*s = 1-r := by field_simp
    rw [heq] at hz
    nlinarith
  calc
    _ = Real.pi/2 + (Real.pi^2/4)*((1+r)/r)*((1-r)/Real.sin s) := by
      dsimp [X]
      field_simp
      ring
    _ ≤ Real.pi/2 + Real.pi^2*((1-r)/Real.sin s) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hratio (show 0 ≤ Real.pi^2/4 by positivity)]
    _ ≤ Real.pi/2 + Real.pi^2*((Real.pi/2)*((1-r)/s)) := by gcongr
    _ ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
      have hp : 0 ≤ Real.pi^3*(1-r)/s := by positivity
      have heq : Real.pi^2*((Real.pi/2)*((1-r)/s)) =
          (Real.pi^3*(1-r)/s)/2 := by ring
      rw [heq]
      linarith

theorem circleTop_arg {w : ℂ} (hr : 0 < w.re) (hi : 0 ≤ w.im) :
    ∃ s ∈ Ioc (0 : ℝ) (Real.pi/2), circleTop ‖w‖ s = w := by
  let s := Real.pi/2-w.arg
  have ha0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hi
  have ha1 : w.arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  refine ⟨s, ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩, ?_⟩
  apply Complex.ext
  · rw [circleTop_re]
    dsimp [s]
    rw [Real.sin_pi_div_two_sub, Complex.norm_mul_cos_arg]
  · rw [circleTop_im]
    dsimp [s]
    rw [Real.cos_pi_div_two_sub, Complex.norm_mul_sin_arg]

lemma div_le_sqrt_of_gap {d δ s : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hs : 0 < s)
    (hg : δ ≤ s^2/d) : d/s ≤ Real.sqrt (d/δ) := by
  have hg' : δ*d ≤ s^2 := (le_div_iff₀ hd).mp hg
  have he : (d/s)^2 ≤ d/δ := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg' hd.le]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr he

theorem reciprocal_A_slice {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re)
    (hradius : 1/2 ≤ ‖w‖) :
    1 / A w ≤ Real.pi/2 + Real.pi^3 *
      Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|)) := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hdelta : 0 < T ‖w‖ - |(F w).im| := by
    have hh := vertical_gap_pos hFw (re_F_pos hw hr)
    simpa only [g_F hw] using hh
  have upper (z : ℂ) (hz : ‖z‖ < 1) (hzr : 0 < z.re) (hzi : 0 ≤ z.im)
      (hzlow : 1/2 ≤ ‖z‖) (hgap : 0 < T ‖z‖ - |(F z).im|) :
      1 / A z ≤ Real.pi/2 + Real.pi^3 *
        Real.sqrt ((1-‖z‖)/(T ‖z‖ - |(F z).im|)) := by
    obtain ⟨s, hs, he⟩ := circleTop_arg hzr hzi
    have hh := reciprocal_A_circleTop hzlow hz hs.1 hs.2
    rw [he] at hh
    apply hh.trans
    have hgs := gap_le_square (norm_nonneg z) hz hs.1.le hs.2
    rw [he] at hgs
    have hg : T ‖z‖ - |(F z).im| ≤ s^2/(1-‖z‖) := by
      linarith [le_abs_self (F z).im]
    have hb := div_le_sqrt_of_gap (sub_pos.mpr hz) hgap hs.1 hg
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi^3 by positivity)
    have heq : Real.pi^3*((1-‖z‖)/s) = Real.pi^3*(1-‖z‖)/s := by ring
    rw [heq] at hm
    linarith
  rcases le_total 0 w.im with hi | hi
  · exact upper w hw hr hi hradius hdelta
  · have hn : ‖(starRingEnd ℂ) w‖ = ‖w‖ := by simp
    have ha : A ((starRingEnd ℂ) w) = A w := by
      rw [A, re_mul_deriv_F (by simpa using hw), A, re_mul_deriv_F hw]
      simp
    have hh := upper ((starRingEnd ℂ) w) (by simpa using hw) (by simpa using hr)
      (by simpa using neg_nonneg.mpr hi) (by simpa using hradius) (by simpa using hdelta)
    simpa [ha] using hh

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem deriv_T_eq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    deriv T r = (8 / Real.pi^2) * (Real.artanh r / r) := by
  have habs : |r| < 1 := by simpa only [abs_of_pos hr] using hr1
  rw [(hasDerivAt_T habs).deriv]
  have hh := congr_arg Complex.im (mul_deriv_F (w := (r : ℂ)*I) (by simpa [norm_mul] using habs))
  have hc : cayley ((r : ℂ)*I) = (((1-r)/(1+r) : ℝ) : ℂ) := by
    unfold cayley
    push_cast
    rw [mul_assoc, I_mul_I]
    ring
  have hai : (Complex.arctan ((r : ℂ)*I)).im = Real.artanh r := by
    rw [Complex.arctan]
    change ((-I/2) * Complex.log (cayley ((r : ℂ)*I))).im = _
    rw [hc, mul_im]
    have hp : 0 < (1-r)/(1+r) := by positivity
    have hre : (-I/2 : ℂ).re = 0 := by norm_num [div_re]
    have him : (-I/2 : ℂ).im = -1/2 := by norm_num [div_im]
    rw [hre, him, zero_mul, zero_add]
    rw [Complex.log_re, norm_real, Real.norm_eq_abs, abs_of_pos hp,
      Real.artanh_eq_half_log ⟨by linarith, hr1.le⟩]
    have hlog : Real.log ((1-r)/(1+r)) = -Real.log ((1+r)/(1-r)) := by
      rw [show (1-r)/(1+r) = ((1+r)/(1-r))⁻¹ by rw [inv_div], Real.log_inv]
    rw [hlog]
    norm_num
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    zero_mul, zero_sub, add_zero, neg_zero, zero_add] at hh
  rw [hai] at hh
  rw [mul_comm] at hh
  have hh := (eq_div_iff hr.ne').mpr hh
  calc
    _ = ((8 / Real.pi^2) * Real.artanh r)/r := hh
    _ = _ := by ring

theorem deriv_T_lower {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr : r < 1) :
    (8/Real.pi^2) * Real.artanh a ≤ deriv T r := by
  have hr0 : 0 < r := ha.trans_le har
  rw [deriv_T_eq hr0 hr]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Real.artanh_le_artanh (by linarith) hr har).trans
  exact le_div_self (Real.artanh_nonneg hr0.le) hr0 hr.le

theorem T_tail_gap {a r s : ℝ} (ha : 0 < a) (har : a ≤ r) (hrs : r ≤ s)
    (hs : s < 1) :
    (8/Real.pi^2)*Real.artanh a * (s-r) ≤ T s-T r := by
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc r s)
    (continuousOn_T.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2.trans hs.le⟩))
    (by intro x hx
        have hxabs : |x| < 1 := by
          simp only [interior_Icc, mem_Ioo] at hx
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        exact (hasDerivAt_T hxabs).differentiableAt.differentiableWithinAt)
    (by intro x hx
        simp only [interior_Icc, mem_Ioo] at hx
        exact deriv_T_lower ha (har.trans hx.1.le) (hx.2.trans hs))
    r ⟨le_rfl, hrs⟩ s ⟨hrs, le_rfl⟩ hrs

theorem exists_tail_cutoff (M : ℝ) : ∃ a ∈ Ioo (1/2 : ℝ) 1,
    M < (8/Real.pi^2)*Real.artanh a := by
  let y := max (Real.artanh (1/2)) ((Real.pi^2/8)*M) + 1
  let a := Real.tanh y
  have ha : a ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  have hy : Real.artanh a = y := Real.artanh_tanh y
  have hhalf : (1/2 : ℝ) < a := by
    apply (Real.artanh_lt_artanh_iff (by norm_num) ha).mp
    rw [hy]
    dsimp [y]
    have := le_max_left (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  refine ⟨a, ⟨hhalf, ha.2⟩, ?_⟩
  rw [hy]
  have hyy : (Real.pi^2/8)*M < y := by
    dsimp [y]
    have := le_max_right (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  have hm := mul_lt_mul_of_pos_left hyy (by positivity : 0 < 8/Real.pi^2)
  have he : (8/Real.pi^2)*((Real.pi^2/8)*M) = M := by field_simp
  rwa [he] at hm

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HorizontalIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u52 u53 u54

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem density_nonneg (k : ℕ) (z : ℂ) : 0 ≤ density k z := by
  unfold density; positivity

theorem contDiffOn_density (k : ℕ) : ContDiffOn ℝ ∞ (density k) D := by
  have hg : ContDiffOn ℝ ∞ g D := (analyticOnNhd_g.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have hd : ContDiffOn ℝ ∞ (deriv g) D :=
    (analyticOnNhd_g.deriv.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have he : density k = fun z => (‖g z‖^2)^(k-1) * ‖deriv g z‖^2 := by
    funext z
    simp only [density, ← pow_mul]
    congr 2
    omega
  rw [he]
  exact ((hg.norm_sq ℂ).pow (k-1)).mul (hd.norm_sq ℂ)

theorem continuousOn_density (k : ℕ) : ContinuousOn (density k) D :=
  (contDiffOn_density k).continuousOn

theorem integrable_density {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume 0 v := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_density k).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem_signed hz hh

theorem J_nonneg {v t : ℝ} (hv : 0 ≤ v) (k : ℕ) : 0 ≤ J k v t := by
  apply mul_nonneg (sq_nonneg _)
  exact intervalIntegral.integral_nonneg hv (fun _ _ => density_nonneg _ _)

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem rho_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rho t h := by
  apply norm_pos_iff.mpr
  intro he
  have hre := re_g_pos hz (by simpa using hh)
  rw [he] at hre
  simp at hre

theorem hasDerivAt_rho {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    HasDerivAt (rho t) (rhoD t h) h := by
  have hn := rho_pos hz hh
  have hd := (horizontal_normSq_deriv hz).sqrt (ne_of_gt (sq_pos_of_pos hn))
  have he : (fun x : ℝ => Real.sqrt (‖g ((x : ℂ)+(t : ℂ)*I)‖^2)) = rho t := by
    funext x; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hd
  convert hd using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  dsimp [rhoD, rho]
  ring

theorem rhoD_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rhoD t h := by
  apply div_pos (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  exact mul_pos (rho_pos hz hh) (sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))))

theorem continuousOn_rho {t v : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hv : 0 ≤ v) :
    ContinuousOn (rho t) (Icc 0 v) := by
  apply (continuousOn_g.norm).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem hz hv hh

theorem density_radial {k : ℕ} (hk : 1 ≤ k) {t h : ℝ}
    (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    density k ((h : ℂ)+(t : ℂ)*I) =
      (rho t h)^(2*k-1) * (1/A (g ((h : ℂ)+(t : ℂ)*I))) * rhoD t h := by
  have hA := ne_of_gt (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  have hr := ne_of_gt (rho_pos hz hh)
  have hF := norm_ne_zero_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))
  have he : deriv g ((h : ℂ)+(t : ℂ)*I) = (deriv F (g ((h : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [density, he, norm_inv]
  rw [show 2*k-1 = (2*k-2)+1 by omega, pow_succ]
  dsimp [rhoD, rho] at *
  field_simp
  rw [pow_succ]

theorem deriv_F_neg {w : ℂ} (hw : ‖w‖ < 1) : deriv F (-w) = deriv F w := by
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  congr 1
  apply tsum_congr
  intro n
  simp only [termDeriv]
  rw [(show Even (2*n) from ⟨n, by omega⟩).neg_pow]

theorem deriv_F_conj {w : ℂ} (hw : ‖w‖ < 1) :
    deriv F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv F w) := by
  have he : (fun n : ℕ => termDeriv n ((starRingEnd ℂ) w)) =
      fun n : ℕ => conjCLE (termDeriv n w) := by
    funext n
    simp [termDeriv, map_ofNat]
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  simp only [he, ← conjCLE.map_tsum]
  simp [map_ofNat]

theorem density_neg_conj {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    density k (-(starRingEnd ℂ) z) = density k z := by
  have hd (w : ℂ) (hw : w ∈ D) : deriv g w = (deriv F (g w))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hw), F_g hw]
  rw [density, density, hd _ (neg_conj_mem_D hz), hd _ hz, g_neg_conj hz,
    deriv_F_neg (by simpa using norm_g_lt hz), deriv_F_conj (norm_g_lt hz)]
  simp

theorem J_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    J k (-v) t = -J k v t := by
  have he (h : ℝ) : -(starRingEnd ℂ) ((h : ℂ)+(t : ℂ)*I) = ((-h : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  have hsub := intervalIntegral.integral_comp_neg
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (a := 0) (b := v)
  simp only [neg_zero] at hsub
  have hi : (∫ h in (0 : ℝ)..v, density k (((-h : ℝ) : ℂ)+(t : ℂ)*I)) =
      ∫ h in (0 : ℝ)..v, density k ((h : ℂ)+(t : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro h hh
    dsimp only
    rw [← he, density_neg_conj (horizontal_segment_mem_signed hz hh)]
  rw [hi, intervalIntegral.integral_symm (a := 0) (b := -v)] at hsub
  rw [J, J, ← mul_neg]
  congr 1
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.TipEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

open MeasureTheory intervalIntegral Set
open scoped Real

namespace SymmetricPolar
noncomputable section

lemma endpointKernel_eq_rpow {H y : ℝ} (hy : 0 ≤ y) (hyH : y ≤ H) :
    endpointKernel H y = y ^ (1 / 2 : ℝ) * (H - y) ^ (-(1 / 2 : ℝ)) := by
  rw [endpointKernel, Real.sqrt_div hy, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_neg (sub_nonneg.mpr hyH), div_eq_mul_inv]

lemma intervalIntegrable_endpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (endpointKernel H) volume 0 H := by
  have hi : IntervalIntegrable (fun y : ℝ => (H - y) ^ (-(1 / 2 : ℝ))) volume 0 H := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := H)
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left H).symm
  have hm := hi.continuousOn_mul Real.continuous_sqrt.continuousOn
  apply IntervalIntegrable.congr (f := fun y => Real.sqrt y * (H - y) ^ (-(1 / 2 : ℝ))) _ hm
  intro y hy
  rw [uIoc_of_le hH] at hy
  dsimp only
  rw [endpointKernel_eq_rpow hy.1.le hy.2, Real.sqrt_eq_rpow]

private lemma beta_three_halves_one_half :
    Complex.betaIntegral (3 / 2) (1 / 2) = (Real.pi : ℂ) / 2 := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
  have hG : Complex.Gamma (2 : ℂ) = 1 := by
    norm_num [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one]
  have hreflect := Complex.Gamma_mul_Gamma_one_sub (1 / 2)
  norm_num at hreflect
  rw [show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring,
    Complex.sin_pi_div_two, div_one] at hreflect
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, hG, div_one,
    show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
    Complex.Gamma_add_one _ (by norm_num)]
  rw [mul_assoc, hreflect]
  ring

lemma integral_endpointKernel {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, endpointKernel H y) = Real.pi * H / 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_scaled (3 / 2) (1 / 2) hH
  norm_num only at h
  rw [beta_three_halves_one_half] at h
  have hc : (∫ y in 0..H, (endpointKernel H y : ℂ)) =
      ∫ y in 0..H, (y : ℂ) ^ ((3 / 2 : ℂ) - 1) *
        ((H : ℂ) - y) ^ ((1 / 2 : ℂ) - 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hH.le] at hy
    dsimp only
    rw [endpointKernel_eq_rpow hy.1 hy.2, Complex.ofReal_mul,
      Complex.ofReal_cpow hy.1, Complex.ofReal_cpow (sub_nonneg.mpr hy.2),
      Complex.ofReal_sub]
    norm_num
  rw [hc]
  norm_num only
  rw [h]
  norm_num
  ring

lemma endpointKernel_le_one {H y : ℝ} (hH : 0 < H) (_hy : 0 ≤ y)
    (hyH : y ≤ H / 2) : endpointKernel H y ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact (div_le_one (by linarith : 0 < H - y)).mpr (by linarith)

lemma intervalIntegrable_dampedEndpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (fun y => Real.exp (-y) * endpointKernel H y) volume 0 H :=
  (intervalIntegrable_endpointKernel hH).continuousOn_mul (by fun_prop)

lemma integral_dampedEndpointKernel_le {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, Real.exp (-y) * endpointKernel H y) ≤
      1 + Real.pi / Real.exp 1 := by
  have hhalf : 0 ≤ H / 2 := by positivity
  have hhalfH : H / 2 ≤ H := by linarith
  have hsfirst : uIcc 0 (H / 2) ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalf, uIcc_of_le hH.le] using
      Icc_subset_Icc le_rfl hhalfH
  have hslast : uIcc (H / 2) H ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalfH, uIcc_of_le hH.le] using
      Icc_subset_Icc hhalf le_rfl
  have hk := intervalIntegrable_endpointKernel hH.le
  have hf := intervalIntegrable_dampedEndpointKernel hH.le
  have hfirst : (∫ y in 0..H / 2, Real.exp (-y) * endpointKernel H y) ≤ 1 := by
    calc
      _ ≤ ∫ y in 0..H / 2, Real.exp (-y) := by
        apply intervalIntegral.integral_mono_on hhalf (hf.mono_set hsfirst)
          ((by fun_prop : Continuous (fun y : ℝ => Real.exp (-y))).intervalIntegrable _ _)
        intro y hy
        exact mul_le_of_le_one_right (Real.exp_pos _).le
          (endpointKernel_le_one hH hy.1 hy.2)
      _ ≤ 1 := by
        rw [intervalIntegral.integral_comp_neg, integral_exp]
        simp only [neg_zero, Real.exp_zero]
        linarith [Real.exp_pos (-(H / 2))]
  have hlast : (∫ y in H / 2..H, Real.exp (-y) * endpointKernel H y) ≤
      Real.exp (-(H / 2)) * (Real.pi * H / 2) := by
    calc
      _ ≤ ∫ y in H / 2..H, Real.exp (-(H / 2)) * endpointKernel H y := by
        apply intervalIntegral.integral_mono_on hhalfH (hf.mono_set hslast)
          ((hk.mono_set hslast).const_mul _)
        intro y hy
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hy.1))
          (Real.sqrt_nonneg _)
      _ = Real.exp (-(H / 2)) * ∫ y in H / 2..H, endpointKernel H y :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp (-(H / 2)) * ∫ y in 0..H, endpointKernel H y := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply intervalIntegral.integral_mono_interval hhalf hhalfH le_rfl _ hk
        exact Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _)
      _ = _ := by rw [integral_endpointKernel hH]
  have hexp : (H / 2) * Real.exp (-(H / 2)) ≤ 1 / Real.exp 1 := by
    calc
      _ ≤ Real.exp (H / 2 - 1) * Real.exp (-(H / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (H / 2 - 1)]
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
      _ = _ := by rw [Real.exp_neg, one_div]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set hsfirst) (hf.mono_set hslast)]
  have hp := mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
  have hp' : Real.exp (-(H / 2)) * (Real.pi * H / 2) ≤ Real.pi / Real.exp 1 := by
    calc
      _ = Real.pi * (H / 2 * Real.exp (-(H / 2))) := by ring
      _ ≤ Real.pi * (1 / Real.exp 1) := hp
      _ = _ := by ring
  exact add_le_add hfirst (hlast.trans hp')

lemma movingEndpointIntegral_eq {k : ℕ} (hk : 0 < k) (a : ℝ) :
    movingEndpointIntegral k a = ∫ y in 0..(k : ℝ) * (1 - a),
      (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  let f : ℝ → ℝ := fun y =>
    (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y
  have hsub (r : ℝ) : f ((k : ℝ) - k * r) =
      r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a)) := by
    dsimp [f, endpointKernel]
    have hbase : 1 - ((k : ℝ) - k * r) / k = r := by field_simp; ring
    rw [hbase]
    congr 2
    rw [show (k : ℝ) - k * r = k * (1 - r) by ring,
      show (k : ℝ) * (1 - a) - k * (1 - r) = k * (r - a) by ring,
      mul_div_mul_left _ _ hk0]
  calc
    _ = (k : ℝ) • ∫ r in a..1, f ((k : ℝ) - k * r) := by
      simp only [movingEndpointIntegral, smul_eq_mul, hsub]
    _ = ∫ y in (k : ℝ) - k * 1..(k : ℝ) - k * a, f y :=
      intervalIntegral.smul_integral_comp_sub_mul f _ _
    _ = _ := by
      rw [show (k : ℝ) - k * 1 = 0 by ring,
        show (k : ℝ) - k * a = k * (1 - a) by ring]

lemma movingEndpointIntegral_le {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    movingEndpointIntegral k a ≤ 1 + Real.pi / Real.exp 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hH : 0 < (k : ℝ) * (1 - a) := mul_pos hkR (sub_pos.mpr ha1)
  rw [movingEndpointIntegral_eq (by omega : 0 < k) a]
  apply le_trans _ (integral_dampedEndpointKernel_le hH)
  apply intervalIntegral.integral_mono_on hH.le
    ((intervalIntegrable_endpointKernel hH.le).continuousOn_mul (by fun_prop))
    (intervalIntegrable_dampedEndpointKernel hH.le)
  intro y hy
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hyk : y ≤ (k : ℝ) := by nlinarith [mul_nonneg hkR.le ha, hy.2]
  have hb0 : 0 ≤ 1 - y / (k : ℝ) := sub_nonneg.mpr ((div_le_one hkR).mpr hyk)
  have hb1 : 1 - y / (k : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hy.1 hkR.le)
  exact (pow_le_pow_of_le_one hb0 hb1 (by omega : k ≤ 2 * k - 1)).trans
    (Real.one_sub_div_pow_le_exp_neg hyk)

end
end SymmetricPolar

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem tailSlope_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < tailSlope a := by
  apply mul_pos (by positivity)
  exact Real.artanh_pos ⟨ha, ha1⟩

theorem T_rho_ge_abs {t v u : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) (hu : u ∈ Icc 0 v) : |t| ≤ T (rho t u) := by
  have hmono := (horizontal_radius_strictMono hz hv).monotoneOn
  have h0 := horizontal_segment_mem hz hv (left_mem_Icc.mpr hv)
  have hU := horizontal_segment_mem hz hv hu
  have hle := hmono (left_mem_Icc.mpr hv) hu hu.1
  have hT := strictMonoOn_T.monotoneOn
    (show rho t 0 ∈ Icc (-1) 1 from ⟨(le_trans (by norm_num) (norm_nonneg _)), (norm_g_lt h0).le⟩)
    (show rho t u ∈ Icc (-1) 1 from ⟨le_trans (by norm_num) (norm_nonneg _), (norm_g_lt hU).le⟩) hle
  have he : T (rho t 0) = |t| := by simpa [rho] using T_norm_g_axis (axis_mem_D hz)
  rwa [he] at hT

theorem reciprocal_A_tail {w : ℂ} (hw : ‖w‖ < 1) (hwr : 0 < w.re)
    {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hbw : b < ‖w‖)
    (ht : |(F w).im| ≤ T b) :
    1/A w ≤ Real.pi/2 + Real.pi^3 / Real.sqrt (tailSlope a) *
      Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := hab.trans_lt (hbw.trans hw)
  have hL := tailSlope_pos ha0 ha1
  have hgap := T_tail_gap ha0 hab hbw.le hw
  have hnum : 0 ≤ 1-‖w‖ := by linarith
  have hden : 0 < tailSlope a * (‖w‖-b) := mul_pos hL (sub_pos.mpr hbw)
  have hgap' : tailSlope a * (‖w‖-b) ≤ T ‖w‖ - |(F w).im| := by
    dsimp [tailSlope] at *
    linarith
  apply (reciprocal_A_slice hw hwr (ha.trans (hab.trans hbw.le))).trans
  apply add_le_add_right
  calc
    Real.pi^3 * Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|))
        ≤ Real.pi^3 * Real.sqrt ((1-‖w‖)/(tailSlope a*(‖w‖-b))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hnum hden hgap'
    _ = Real.pi^3 / Real.sqrt (tailSlope a) * Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
      rw [show (1-‖w‖)/(tailSlope a*(‖w‖-b)) = ((1-‖w‖)/(‖w‖-b))/(tailSlope a) by rw [div_div, mul_comm (‖w‖-b)],
        Real.sqrt_div (div_nonneg hnum (sub_nonneg.mpr hbw.le))]
      ring

theorem integrable_radialError {b : ℝ} (hb : b ≤ 1) (k : ℕ) :
    IntervalIntegrable (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-b))) volume b 1 := by
  have h := (SymmetricPolar.intervalIntegrable_endpointKernel (sub_nonneg.mpr hb)).comp_sub_left 1
  have he : (fun r : ℝ => SymmetricPolar.endpointKernel (1-b) (1-r)) =
      fun r : ℝ => Real.sqrt ((1-r)/(r-b)) := by
    funext r
    dsimp [SymmetricPolar.endpointKernel]
    congr 2
    ring
  rw [he] at h
  have hh : IntervalIntegrable (fun r : ℝ => Real.sqrt ((1-r)/(r-b))) volume b 1 := by
    convert h.symm using 1 <;> ring
  exact hh.continuousOn_mul (by fun_prop)

theorem integral_radialLeading {k : ℕ} (hk : 1 ≤ k) (b R : ℝ) :
    (k : ℝ) * ∫ r in b..R, r^(2*k-1)*(Real.pi/2) =
      Real.pi/4 * (R^(2*k)-b^(2*k)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => r^(2*k)/(2*k)) (r^(2*k-1)) r := by
    convert ((hasDerivAt_id r).pow (2*k)).div_const ((2:ℝ)*k) using 1 <;>
      first | rfl | (simp only [Nat.cast_mul, Nat.cast_ofNat, id_eq, mul_one]; field_simp [hk0])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r ∈ uIcc b R) => hd r)
    (show IntervalIntegrable (fun r : ℝ => r^(2*k-1)) volume b R from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, hi]
  field_simp
  ring

theorem outer_integral_bound {k : ℕ} (hk : 1 ≤ k) {t v u a : ℝ}
    (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 1/2 ≤ a) (hau : a ≤ rho t u) :
    (k : ℝ)*∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*((rho t v)^(2*k)-(rho t u)^(2*k)) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have hv : 0 ≤ v := hu.trans huv
  have huI : u ∈ Icc 0 v := ⟨hu, huv⟩
  have huD := horizontal_segment_mem hz hv huI
  have hb0 : 0 ≤ rho t u := norm_nonneg _
  have hb1 : rho t u < 1 := norm_g_lt huD
  have hR1 : rho t v < 1 := norm_g_lt hz
  have hrho := horizontal_radius_strictMono hz hv
  have hbR : rho t u ≤ rho t v := hrho.monotoneOn huI (right_mem_Icc.mpr hv) huv
  have ha1 : a < 1 := hau.trans_lt hb1
  have hL : 0 < tailSlope a := tailSlope_pos (by linarith) ha1
  have hc : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a) := by positivity
  let P : ℝ → ℝ := fun r => r^(2*k-1)*(Real.pi/2) +
    (Real.pi^3/Real.sqrt (tailSlope a))*(r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)))
  have hradE := integrable_radialError hb1.le k
  have hradE' : IntervalIntegrable
      (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) volume (rho t u) (rho t v) :=
    hradE.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by
      rw [uIcc_of_le hb1.le]; exact ⟨hbR, hR1.le⟩))
  have hP : IntervalIntegrable P volume (rho t u) (rho t v) :=
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _).add
      (hradE'.const_mul _)
  have hcont : ContinuousOn (rho t) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact (continuousOn_rho hz hv).mono (fun _ hx => ⟨hu.trans hx.1, hx.2⟩)
  have hder : ∀ h ∈ Ioo (min u v) (max u v), HasDerivAt (rho t) (rhoD t h) h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact hasDerivAt_rho (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)
  have hpos : ∀ h ∈ Ioo (min u v) (max u v), 0 ≤ rhoD t h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact (rhoD_pos (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)).le
  have hPc : IntervalIntegrable (fun h => P (rho t h)*rhoD t h) volume u v :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hcont hder hpos).mpr hP
  have hdens : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_density k).comp (by fun_prop)
    intro h hh
    rw [uIcc_of_le huv] at hh
    exact horizontal_segment_mem hz hv ⟨hu.trans hh.1, hh.2⟩
  have hcmp : ∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ ∫ r in rho t u..rho t v, P r := by
    rw [← intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hcont hder hpos (g := P)]
    apply intervalIntegral.integral_mono_ae_restrict huv hdens hPc
    change ∀ᵐ (h : ℝ) ∂volume.restrict (Icc u v), density k ((h : ℂ)+(t : ℂ)*I) ≤ P (rho t h)*rhoD t h
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [volume.ae_ne u] with h hne hh
    have hhu : u < h := lt_of_le_of_ne hh.1 (Ne.symm hne)
    have hh0 : 0 < h := hu.trans_lt hhu
    have hhz := horizontal_segment_mem hz hv ⟨hh0.le, hh.2⟩
    have hbr : rho t u < rho t h := hrho huI ⟨hh0.le, hh.2⟩ hhu
    have hA := reciprocal_A_tail (norm_g_lt hhz) (re_g_pos hhz (by simpa using hh0))
      ha hau hbr (by simpa only [F_g hhz, add_im, ofReal_im, mul_im, ofReal_re, I_im,
        I_re, mul_one, mul_zero, add_zero, zero_add] using T_rho_ge_abs hz hv huI)
    rw [density_radial hk hhz hh0]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (norm_nonneg (g ((h : ℂ)+(t : ℂ)*I))) (2*k-1))) (rhoD_pos hhz hh0).le
    convert hmul using 1 <;>
      first | rfl | (dsimp only [P, rho]; ring)
  have hlead := integral_radialLeading hk (rho t u) (rho t v)
  have herr : (k : ℝ)*∫ r in rho t u..rho t v,
      r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)) ≤ 1+Real.pi/Real.exp 1 := by
    apply le_trans _ (SymmetricPolar.movingEndpointIntegral_le hk hb0 hb1)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    apply intervalIntegral.integral_mono_interval le_rfl hbR hR1.le _ hradE
    change ∀ᵐ (r : ℝ) ∂volume.restrict (Ioc (rho t u) 1), 0 ≤ r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun r hr => mul_nonneg
      (pow_nonneg (hb0.trans hr.1.le) _) (Real.sqrt_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
  dsimp [P] at hh
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _)
    (hradE'.const_mul _), intervalIntegral.integral_const_mul, mul_add, hlead] at hh
  apply hh.trans
  apply add_le_add_right
  calc
    _ = (Real.pi^3/Real.sqrt (tailSlope a))*((k : ℝ)*∫ r in rho t u..rho t v,
        r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left herr hc

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem exists_inner_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v → rho t v ≤ a →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        C*(k : ℝ)*a^(2*k-2) := by
  let Cset := F '' Metric.closedBall (0 : ℂ) a
  have hCD : Cset ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ a := by simpa using hw
    simpa using hw'.trans_lt ha1
  have hCc : IsCompact Cset := (isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
    (continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall ha1.le))
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (analyticOnNhd_g.deriv.continuousOn.mono hCD)
  obtain ⟨B, hB0, hB⟩ := isBounded_D.exists_pos_norm_le
  let M := max N 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨B*M^2, mul_nonneg hB0.le (sq_nonneg _), ?_⟩
  intro k t v hz hv hra
  have hvB : v ≤ B := by
    have hh := (abs_re_le_norm ((v : ℂ)+(t : ℂ)*I)).trans (hB _ hz)
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self, add_zero, abs_of_nonneg hv] using hh
  have hpi : IntervalIntegrable (fun h : ℝ => a^(2*k-2)*M^2) volume 0 v := intervalIntegrable_const
  have hii := integrable_density hz k
  have hcmp : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ v*(a^(2*k-2)*M^2) := by
    have hh : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        ∫ h in 0..v, a^(2*k-2)*M^2 := by
      apply intervalIntegral.integral_mono_on hv hii hpi
      intro h hh
      have hhz := horizontal_segment_mem hz hv hh
      have hr : rho t h ≤ a := ((horizontal_radius_strictMono hz hv).monotoneOn hh
        (right_mem_Icc.mpr hv) hh.2).trans hra
      have hc : (h : ℂ)+(t : ℂ)*I ∈ Cset :=
        ⟨g _, by simpa [rho] using hr, F_g hhz⟩
      have hn : ‖deriv g ((h : ℂ)+(t : ℂ)*I)‖ ≤ M := (hN _ hc).trans (le_max_left _ _)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hr _) (pow_le_pow_left₀ (norm_nonneg _) hn _)
        (sq_nonneg _) (pow_nonneg ha0 _)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  calc
    _ ≤ (k : ℝ)*(v*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
    _ ≤ (k : ℝ)*(B*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hvB (mul_nonneg (pow_nonneg ha0 _) (sq_nonneg _))) (Nat.cast_nonneg k)
    _ = _ := by ring

theorem exists_uniform_error_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*(rho t v)^(2*k) + C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨C, hC, hinner⟩ := exists_inner_bound ha0 ha1
  refine ⟨C, hC, ?_⟩
  intro k hk t v hz hv
  have hE : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by positivity
  have hCterm : 0 ≤ C*(k : ℝ)*a^(2*k-2) := by positivity
  have hR : 0 ≤ Real.pi/4*(rho t v)^(2*k) := by
    exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  by_cases hr : rho t v ≤ a
  · exact (hinner k t v hz hv hr).trans (by linarith)
  by_cases hl : a ≤ rho t 0
  · have hh := outer_integral_bound hk hz (le_refl 0) hv ha hl
    have hn : 0 ≤ Real.pi/4*(rho t 0)^(2*k) :=
      mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
    nlinarith
  have haI : a ∈ Icc (rho t 0) (rho t v) := ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc hv (continuousOn_rho hz hv) haI
  have huD := horizontal_segment_mem hz hv hu
  have hleft := hinner k t u huD hu.1 heu.le
  have hright := outer_integral_bound hk hz hu.1 hu.2 ha heu.ge
  have hIuv : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    exact (integrable_density hz k).mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hv]) right_mem_uIcc)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (integrable_density huD k) hIuv
  have hn : 0 ≤ Real.pi/4*(rho t u)^(2*k) :=
    mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  rw [← hadd]
  nlinarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem J_div_order {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hv : 0 ≤ v) :
    |J k v t|/(k : ℝ) = (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [abs_of_nonneg (J_nonneg hv k), J]
  field_simp

theorem rho_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : rho t (-v) = rho t v := by
  have he : -(starRingEnd ℂ) ((v : ℂ)+(t : ℂ)*I) = ((-v : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  rw [rho, rho, ← he, g_neg_conj hz]
  simp

theorem epsilon_nonneg (k : ℕ) : 0 ≤ epsilon k := le_max_left _ _

theorem exists_excess_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ D,
      excess k z ≤ C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_error_bound ha ha1
  refine ⟨C, hC, ?_⟩
  intro k hk z hz
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa only [re_add_im] using hz
  have hpos (v t : ℝ) (hv : 0 ≤ v) (hh : (v : ℂ)+(t : ℂ)*I ∈ D) :
      |J k v t|/(k : ℝ) - Real.pi/4*(rho t v)^(2*k) ≤
        C*(k : ℝ)*a^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
    rw [J_div_order hk hv]
    linarith [hb k hk t v hh hv]
  by_cases hv : 0 ≤ z.re
  · simpa only [excess, rho, re_add_im] using hpos z.re z.im hv hz'
  · have hnz : ((-z.re : ℝ) : ℂ)+(z.im : ℂ)*I ∈ D := by
      convert neg_conj_mem_D hz using 1
      apply Complex.ext <;> simp
    have hh := hpos (-z.re) z.im (by linarith) hnz
    rw [J_neg hz', abs_neg, rho_neg hz'] at hh
    simpa only [excess, rho, re_add_im] using hh

theorem bddAbove_excess {k : ℕ} (hk : 1 ≤ k) : BddAbove (excess k '' D) := by
  obtain ⟨C, _, hC⟩ := exists_excess_bound (a := 3/4) (by norm_num) (by norm_num)
  refine ⟨C*(k : ℝ)*(3/4)^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope (3/4))*(1+Real.pi/Real.exp 1), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC k hk z hz

theorem excess_le_epsilon {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ D) : excess k z ≤ epsilon k :=
  (le_csSup (bddAbove_excess hk) (mem_image_of_mem _ hz)).trans (le_max_right _ _)

theorem epsilon_le_of_excess_le {k : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ z ∈ D, excess k z ≤ B) :
    epsilon k ≤ B := by
  apply max_le hB
  apply csSup_le ⟨excess k 0, mem_image_of_mem _ zero_mem_D⟩
  rintro _ ⟨z, hz, rfl⟩
  exact h z hz

theorem tendsto_inner_error {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (C : ℝ) :
    Tendsto (fun k : ℕ => C*(k : ℝ)*a^(2*k-2)) atTop (𝓝 0) := by
  have hq : |a^2| < 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq).const_mul (C/a^2)
  simp only [pow_one, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hp : a^(2*k-2)*a^2 = (a^2)^k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ 2*k), pow_mul]
  have ha2 : a^2 ≠ 0 := pow_ne_zero _ ha.ne'
  apply mul_right_cancel₀ ha2
  calc
    ((C/a^2)*((k : ℝ)*(a^2)^k))*a^2 = C*(k : ℝ)*(a^2)^k := by field_simp
    _ = C*(k : ℝ)*(a^(2*k-2)*a^2) := by rw [hp]
    _ = C*(k : ℝ)*a^(2*k-2)*a^2 := by ring

theorem exists_small_tail (e : ℝ) (he : 0 < e) :
    ∃ a ∈ Ioo (1/2 : ℝ) 1,
      Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) < e := by
  let H := Real.pi^3*(1+Real.pi/Real.exp 1)
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨a, ha, hL⟩ := exists_tail_cutoff ((H/e)^2)
  have ha0 : 0 < a := by linarith [ha.1]
  have hs : 0 < Real.sqrt (tailSlope a) := Real.sqrt_pos.2 (tailSlope_pos ha0 ha.2)
  have hq : H/e < Real.sqrt (tailSlope a) := by
    rw [← Real.sqrt_sq (div_nonneg hH.le he.le)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hL
  refine ⟨a, ha, ?_⟩
  have hh : H < e * Real.sqrt (tailSlope a) := by
    have := (div_lt_iff₀ he).mp hq
    nlinarith
  have hh' := (div_lt_iff₀ hs).mpr hh
  have hEq : Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) = H/Real.sqrt (tailSlope a) := by
    show _ = Real.pi^3*(1+Real.pi/Real.exp 1)/Real.sqrt (tailSlope a)
    ring
  rw [hEq]
  exact hh'

theorem tendsto_epsilon : Tendsto epsilon atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun k => hc.trans_le (epsilon_nonneg k))
  · intro e he
    obtain ⟨a, ha, htail⟩ := exists_small_tail (e/2) (by linarith)
    obtain ⟨C, hC, hbound⟩ := exists_excess_bound ha.1.le ha.2
    have ha0 : 0 < a := by linarith [ha.1]
    have ht := (tendsto_inner_error ha0 ha.2 C).eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < e/2))
    filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with k hinner hk
    have hE := epsilon_le_of_excess_le (k := k)
      (B := C*(k : ℝ)*a^(2*k-2)+Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1))
      (by positivity) (hbound k hk)
    linarith

theorem uniform_slice {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    |J k v t|/(k : ℝ) ≤ Real.pi/4*‖g ((v : ℂ)+(t : ℂ)*I)‖^(2*k)+epsilon k := by
  have hh := excess_le_epsilon hk hz
  have hre : ((v : ℂ)+(t : ℂ)*I).re = v := by simp
  have him : ((v : ℂ)+(t : ℂ)*I).im = t := by simp
  simp only [excess, hre, him] at hh
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u55 u56 u57 u58 u59 u60

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u55} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type u56} [Fintype ι]

theorem norm_tuple_sq (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) :
    ‖tuple ℓ k z‖^2 = ∑ j, ‖PlanarLens.g (ℓ j z)‖^(2*k) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change ‖PlanarLens.g (ℓ j z)^k‖^2 = _
  rw [norm_pow, ← pow_mul, Nat.mul_comm k 2]

omit [Fintype ι] in
theorem zero_mem_domain (ℓ : ι → E →L[ℂ] ℂ) : (0 : E) ∈ domain ℓ := by
  intro j
  simpa using PlanarLens.zero_mem_D

variable [FiniteDimensional ℂ E]

omit [Fintype ι] in

theorem isBounded_domain (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) : Bornology.IsBounded (domain ℓ) := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  let C := PlanarLens.F '' Metric.closedBall (0 : ℂ) 1
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
    PlanarLens.continuousOn_F_closedBall
  have hc : IsCompact (L ⁻¹' {f : ι → ℂ | ∀ j, f j ∈ C}) :=
    hL.isCompact_preimage (isCompact_pi_infinite (fun _ => hC))
  apply hc.isBounded.subset
  intro z hz j
  exact image_mono Metric.ball_subset_closedBall (hz j)

end
end PolarStrips

namespace ComplexCoordinates
open scoped ComplexConjugate ContDiff
noncomputable section
variable {ι : Type u57} [Fintype ι]

theorem re_functional (b : R ι) (z : C ι) :
    (functional b z).re = inner (𝕜 := ℝ) b (re z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem im_functional (b : R ι) (z : C ι) :
    (functional b z).im = inner (𝕜 := ℝ) b (im z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_sq_parts (z : C ι) : ‖z‖^2 = ‖re z‖^2+‖im z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, re_apply, im_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]

theorem functional_injective {κ : Type u60} (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    Function.Injective (fun z : C ι => fun j => functional (b j) z) := by
  intro z w h
  apply parts.injective
  apply Prod.ext
  · apply hb
    funext j
    have hh := congrArg Complex.re (congrFun h j)
    simpa only [re_functional, parts_apply] using hh
  · apply hb
    funext j
    have hh := congrArg Complex.im (congrFun h j)
    simpa only [im_functional, parts_apply] using hh

end
end ComplexCoordinates

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u61 u62 u63 u64 u65 u66 u67 u68 u69

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u68} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_interior_polar_of_bound {K : Set E} {p : E} {B r : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ q ∈ K, ‖q‖ ≤ B) (hr : r < 1)
    (hp : ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ r) : p ∈ interior (polar K) := by
  let δ := (1-r)/(B+1)
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Metric.ball_mem_nhds p hδ)
  intro w hw q hq
  have hw' : ‖w-p‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hinner := real_inner_le_norm q (w-p)
  have hbq := hbound q hq
  have hmul : ‖q‖*‖w-p‖ ≤ (B+1)*δ := by
    calc
      ‖q‖*‖w-p‖ ≤ B*δ := mul_le_mul hbq hw'.le (norm_nonneg _) hB
      _ ≤ (B+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hδeq : (B+1)*δ = 1-r := by dsimp [δ]; field_simp
  rw [inner_sub_right] at hinner
  linarith [hp q hq]

variable {κ : Type u69}

variable [Fintype κ]

theorem mem_interior_stripBody (b : κ → E) {x : E}
    (hx : ∀ j, |inner (𝕜 := ℝ) (b j) x| < 1) : x ∈ interior (stripBody b) := by
  let U : Set E := {y | ∀ j, |inner (𝕜 := ℝ) (b j) y| < 1}
  have hopen : IsOpen U := by
    have he : U = ⋂ j, {y | |inner (𝕜 := ℝ) (b j) y| < 1} := by ext y; simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (by fun_prop) continuous_const
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hopen.mem_nhds hx) (fun y hy j => (hy j).le))

theorem zero_mem_interior_stripBody (b : κ → E) : (0 : E) ∈ interior (stripBody b) :=
  mem_interior_stripBody b (by intro j; simp)

variable [FiniteDimensional ℝ E]

omit [Fintype κ] in
theorem isCompact_stripBody (b : κ → E)
    (hb : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x)) :
    IsCompact (stripBody b) := by
  let L : E →L[ℝ] (κ → ℝ) := ContinuousLinearMap.pi (fun j => innerSL ℝ (b j))
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hb)
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : κ => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
  convert hc using 1
  ext x
  simp only [stripBody, mem_ofPred_eq, mem_preimage, ContinuousLinearMap.pi_apply, innerSL_apply_apply,
    mem_Icc, ← abs_le, L]

end
end ConvexPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MomentumBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u70 u71 u72 u73

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter ComplexCoordinates
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u70} {κ : Type u71} [Fintype ι] [Fintype κ]

theorem position_mem_interior (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) :
    (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) := by
  apply ConvexPolar.mem_interior_stripBody
  intro j
  change |inner (𝕜 := ℝ) (b j) (im z)| < 1
  rw [← im_functional]
  exact abs_lt.mpr (PlanarLens.im_mem_Ioo (hz j))

theorem norm_re_le (z : C ι) : ‖re z‖ ≤ ‖z‖ := by
  have hh := norm_sq_parts z
  nlinarith [sq_nonneg ‖im z‖, norm_nonneg (re z), norm_nonneg z]

theorem momentum_bound (b : κ → R ι) {k : ℕ} (hk : 1 ≤ k) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) {y : R ι}
    (hy : y ∈ ConvexPolar.stripBody b) {A B : ℝ}
    (hzA : ‖z‖ ≤ A) (hyB : ‖y‖ ≤ B) :
    inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
      A*B/(k : ℝ) + Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
        (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hu : inner (𝕜 := ℝ) y (-re z) ≤ A*B := by
    have hh := real_inner_le_norm y (-re z)
    rw [norm_neg] at hh
    have hm := mul_le_mul hyB ((norm_re_le z).trans hzA) (norm_nonneg _) (le_trans (norm_nonneg _) hyB)
    nlinarith
  have hj (j : κ) : -(PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)) ≤
      |PlanarLens.primitive k (functional (b j) z)| := by
    have hh : |inner (𝕜 := ℝ) y (b j)| ≤ 1 := by rw [real_inner_comm]; exact hy j
    calc
      _ ≤ |PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)| := neg_le_abs _
      _ = |PlanarLens.primitive k (functional (b j) z)| * |inner (𝕜 := ℝ) y (b j)| := abs_mul _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hh (abs_nonneg (PlanarLens.primitive k (functional (b j) z)))
  have hsum : inner (𝕜 := ℝ) y (phase b k z).2 ≤ A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)| := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [phase, inner_sub_right, inner_sum, real_inner_smul_right, Finset.sum_neg_distrib] at ⊢ hh
    linarith
  have hslice (j : κ) : |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) ≤
      Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k := by
    simpa only [PlanarLens.primitive, Complex.re_add_im] using
      PlanarLens.uniform_slice hk (v := (functional (b j) z).re) (t := (functional (b j) z).im)
        (by simpa only [Complex.re_add_im] using hz j)
  calc
    _ ≤ (A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)|)/(k : ℝ) :=
      div_le_div_of_nonneg_right hsum hkpos.le
    _ = A*B/(k : ℝ) + ∑ j, |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) := by
      rw [add_div, Finset.sum_div]
    _ ≤ A*B/(k : ℝ) + ∑ j, (Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hslice j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← norm_tuple_sq]; simp [add_assoc]

theorem exists_uniform_momentum_bound (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ ConvexPolar.stripBody b, ‖y‖ ≤ B) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ z ∈ domain (fun j => functional (b j)),
        ∀ y ∈ ConvexPolar.stripBody b,
          inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
            C/(k : ℝ)+Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
              (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  obtain ⟨A, hA⟩ := (isBounded_domain _ (functional_injective b hb)).exists_norm_le
  obtain ⟨B, hB⟩ := (ConvexPolar.isCompact_stripBody b hb).isBounded.exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg (0 : C ι)).trans (hA 0 (zero_mem_domain _))
  have hB0 : 0 ≤ B := (norm_nonneg (0 : R ι)).trans (hB 0 (interior_subset (ConvexPolar.zero_mem_interior_stripBody b)))
  refine ⟨A*B, B, mul_nonneg hA0 hB0, hB0, hB, ?_⟩
  intro k hk z hz y hy
  exact momentum_bound b hk hz hy (hA z hz) (hB y hy)

theorem exists_scaled_image_oai (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x))
    {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z : C ι,
      z ∈ domain (fun j => functional (b j)) → ‖tuple (fun j => functional (b j)) k z‖^2 < 1 →
      (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) ∧
        (((1+η)*Real.pi*(k : ℝ)/4)⁻¹ • (phase b k z).2) ∈ interior (ConvexPolar.polar (ConvexPolar.stripBody b)) := by
  obtain ⟨C, B, _hC, hB, hbound, hmoment⟩ := exists_uniform_momentum_bound b hb
  have ht : Tendsto (fun k : ℕ => C/(k : ℝ)+(Fintype.card κ : ℝ)*PlanarLens.epsilon k) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (PlanarLens.tendsto_epsilon.const_mul (Fintype.card κ : ℝ))
  have hsmall := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < η*Real.pi/4 by positivity))
  obtain ⟨k, hk, hksmall⟩ := (eventually_ge_atTop (1 : ℕ)).and hsmall |>.exists
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let T := (1+η)*Real.pi/4
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsmall : C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k < T := by dsimp [T]; nlinarith
  refine ⟨k, hk, fun z hz hτ => ⟨position_mem_interior b k hz, ?_⟩⟩
  apply ConvexPolar.mem_interior_polar_of_bound hB hbound
    (r := (C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k)/T)
  · exact (div_lt_one hT).mpr hTsmall
  · intro y hy
    have hh := hmoment k hk z hz y hy
    have hp : inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ) ≤
        C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
      have hm := mul_le_mul_of_nonneg_left hτ.le (by positivity : (0 : ℝ) ≤ Real.pi/4)
      linarith
    have hd := div_le_div_of_nonneg_right hp hT.le
    calc
      _ = inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ)/T := by
        rw [real_inner_smul_right]
        dsimp only [T]
        field_simp
      _ ≤ _ := hd

end
end PolarStrips

open Set
open scoped ContDiff ENNReal

end LowerBoundInline

end OAI
end

theorem solution.{u70, u71} : type_of% @OAI.PolarStrips.exists_scaled_image_oai.{u70, u71} := @OAI.PolarStrips.exists_scaled_image_oai.{u70, u71}
