-- Prove2me | solution 1 for OAI.SharpLiebThirring.sharp_lieb_thirring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T14:05:08.125578+00:00
-- url     : https://prove2.me/submissions/bbaa40a5-6f48-4431-8efb-92c862d7c48b

import Mathlib
import Definitions.Def_LiebThirring
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_ActionProof_regularized_action_upper_test
import Theorems.Thm_OAI_SharpLiebThirring_SobolevProof_weak_derivative_representation

section
-- module Solutions.OAIQW_LiebThirring.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/


open Matrix Unitary

open MeasureTheory Set Filter
open scoped Topology
namespace ScalarProof

lemma normalization_integral_pos {σ : ℝ} (hσ : σ < 1) :
    0 < ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  apply integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (normalization_integrable hσ) |>.2
  have hs : Function.support (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp


/-- A global comparison with the Japanese-bracket integrable majorant, including
negative shifts. It supplies all scalar dominated-convergence bounds. -/
lemma shifted_base_lower {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    (δ / (δ + |z| + 1)) * (1 + s ^ 2) ≤ max (s ^ 2 + z) 0 + δ := by
  have hd : 0 < δ + |z| + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  have hm : 0 ≤ max (s ^ 2 + z) 0 := le_max_right _ _
  have hh : s ^ 2 ≤ max (s ^ 2 + z) 0 + |z| := by
    have := le_max_left (s ^ 2 + z) 0
    have := neg_le_abs z
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh hδ.le,
    mul_nonneg (abs_nonneg z) hm, mul_nonneg (abs_nonneg z) hδ.le]

lemma shifted_derivative_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) := by
  have ha : 0 < δ / (δ + |z| + 1) := by positivity
  refine ((normalization_integrable hσ).const_mul
    ((δ / (δ + |z| + 1)) ^ (σ - 3 / 2))).mono' ?_ ?_
  · exact ((derivative_continuous σ hδ).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.mul_rpow ha.le (by positivity : 0 ≤ 1 + s ^ 2)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (shifted_base_lower hδ z s) (by linarith)

lemma primitive_difference_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z s : ℝ) :
    ‖regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)‖ ≤
      (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) * |z| := by
  have hd : ∀ y ∈ Ici (s ^ 2 - |z|),
      ‖(max y 0 + δ) ^ (σ - 3 / 2)‖ ≤
        (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max hy le_rfl) le_rfl) (by linarith)
  have hs : s ^ 2 ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := abs_nonneg z
    linarith
  have hsz : s ^ 2 + z ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := neg_le_abs z
    linarith
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (convex_Ici (s ^ 2 - |z|)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (primitive_hasDerivAt σ hδ y).hasDerivWithinAt) hd hs hsz

lemma mu_integrand_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) := by
  have hi := (shifted_derivative_integrable hσ hδ (-|z|)).mul_const |z|
  refine hi.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (((primitive_differentiable σ hδ).continuous.comp (by fun_prop)).sub
      ((primitive_differentiable σ hδ).continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro s
    simpa only [sub_eq_add_neg] using primitive_difference_bound hσ hδ z s

lemma mu_hasDerivAt_integral {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    HasDerivAt (scalarMu σ δ)
      (fieldNormalization σ * ∫ s : ℝ, (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) z := by
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioi (z - 1)) (x₀ := z)
    (F := fun y s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + y) -
      regularizedPrimitive σ δ (s ^ 2))
    (F' := fun y s : ℝ ↦ (max (s ^ 2 + y) 0 + δ) ^ (σ - 3 / 2))
    (bound := fun s : ℝ ↦ (max (s ^ 2 + (z - 1)) 0 + δ) ^ (σ - 3 / 2))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall (fun y ↦ (mu_integrand_integrable hσ hδ y).aestronglyMeasurable))
    (mu_integrand_integrable hσ hδ z)
    (shifted_derivative_integrable hσ hδ z).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s y hy ↦ ?_))
    (shifted_derivative_integrable hσ hδ (z - 1))
    (Filter.Eventually.of_forall (fun s y _ ↦ ?_))
  · exact hh.2.const_mul (fieldNormalization σ)
  · change z - 1 < y at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max (by linarith) le_rfl) le_rfl) (by linarith)
  · simpa using ((primitive_hasDerivAt σ hδ (s ^ 2 + y)).comp y
      ((hasDerivAt_id y).const_add (s ^ 2))).sub_const (regularizedPrimitive σ δ (s ^ 2))

/-- The scaling integral used in the evaluation of the scalar field. -/
lemma quadratic_integral_scale (t : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ s : ℝ, (s ^ 2 + a) ^ t) =
      a ^ (t + 1 / 2) * ∫ s : ℝ, (1 + s ^ 2) ^ t := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have he (s : ℝ) : (s ^ 2 + a) ^ t =
      a ^ t * (1 + (s / Real.sqrt a) ^ 2) ^ t := by
    rw [← Real.mul_rpow ha.le (by positivity)]
    congr 1
    rw [div_pow, Real.sq_sqrt ha.le]
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_div (fun s : ℝ ↦ (1 + s ^ 2) ^ t),
    abs_of_pos hs, smul_eq_mul, ← mul_assoc, Real.sqrt_eq_rpow,
    ← Real.rpow_add ha]

lemma mu_hasDerivAt_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    HasDerivAt (scalarMu σ δ) (σ * (z + δ) ^ (σ - 1)) z := by
  have hh := mu_hasDerivAt_integral hσ hδ z
  have he (s : ℝ) : (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2) =
      (s ^ 2 + (z + δ)) ^ (σ - 3 / 2) := by
    rw [max_eq_left (by positivity)]
    congr 1
    ring
  simp_rw [he] at hh
  rw [quadratic_integral_scale _ (by positivity : 0 < z + δ)] at hh
  have hp := (normalization_integral_pos hσ).ne'
  convert hh using 1
  unfold fieldNormalization
  rw [show σ - 3 / 2 + 1 / 2 = σ - 1 by ring]
  rw [mul_comm ((z + δ) ^ (σ - 1)), ← mul_assoc, div_mul_cancel₀ _ hp]

lemma mu_eq_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    scalarMu σ δ z = (z + δ) ^ σ - δ ^ σ := by
  have hd (y : ℝ) (hy : 0 ≤ y) :
      HasDerivAt (fun x : ℝ ↦ (x + δ) ^ σ - δ ^ σ)
        (σ * (y + δ) ^ (σ - 1)) y := by
    convert! (((hasDerivAt_id y).add_const δ).rpow_const (p := σ)
      (Or.inl (by positivity : y + δ ≠ 0))).sub_const (δ ^ σ) using 1
    simp
  exact eq_of_has_deriv_right_eq
    (fun y hy ↦ (mu_hasDerivAt_nonneg hσ hδ hy.1).hasDerivWithinAt)
    (fun y hy ↦ (hd y hy.1).hasDerivWithinAt)
    (continuous_iff_continuousAt.mpr (fun y ↦
      (mu_hasDerivAt_integral hσ hδ y).continuousAt)).continuousOn
    (fun y hy ↦ (hd y hy.1).continuousAt.continuousWithinAt)
    (by simp) z ⟨hz, le_rfl⟩


end ScalarProof

open scoped MatrixOrder ComplexOrder


end SharpLiebThirring

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ResolventCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u6 u7 u8 u9 u10 u11

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix


open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
namespace SharpLiebThirring.MatrixProof
variable {n : Type u10} [Fintype n] [DecidableEq n]

lemma cfc_diagonal_real (f : ℝ → ℝ) (x : n → ℝ) (hf : Continuous f) :
    cfc f (diagonal (fun i ↦ (x i : ℂ))) = diagonal (fun i ↦ (f (x i) : ℂ)) := by
  have : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := n → ℂ)).toContinuousFunctionalCalculus
  have hself : IsSelfAdjoint (fun i ↦ (x i : ℂ)) := by ext i; simp
  change cfc f (diagonalStarAlgHom (fun i ↦ (x i : ℂ))) = _
  erw [← (diagonalStarAlgHom (n := n)).map_cfc f (fun i ↦ (x i : ℂ)) hf.continuousOn
    (by change Continuous (diagonal : (n → ℂ) → Matrix n n ℂ); fun_prop) hself
    (isHermitian_diagonal_iff.2 fun i ↦ by simp [IsSelfAdjoint])]
  rw [cfc_map_pi (S := ℝ) f _ hf.continuousOn hself (fun i ↦ by simp [IsSelfAdjoint])]
  change diagonal (fun i ↦ cfc f (x i : ℂ)) = diagonal (fun i ↦ (f (x i) : ℂ))
  apply congrArg diagonal
  funext i
  exact cfc_algebraMap (R := ℝ) (A := ℂ) (x i) f

end SharpLiebThirring.MatrixProof


end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u16 u17 u18

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpLiebThirring.ScalarProof

lemma symmetric_shift_boundary {g : ℝ → ℝ} (hg : Continuous g) (he : Function.Even g)
    (R b : ℝ) :
    (∫ s in -R..R, g (s - b) - g s) =
      ∫ t in 0..b, g (R + t) - g (R - b + t) := by
  have hc1 : Continuous (fun s : ℝ ↦ g (s - b)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ ↦ g (R + t)) := by fun_prop
  have hc3 : Continuous (fun t : ℝ ↦ g (R - b + t)) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_comp_sub_right]
  rw [intervalIntegral.integral_interval_sub_interval_comm
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hn : (∫ s in -R - b..-R, g s) = ∫ t in R..R + b, g t := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := R) (b := R + b)
    calc
      _ = ∫ x in R..R + b, g (-x) := by
        simpa only [show -(R + b) = -R - b by ring] using h.symm
      _ = _ := intervalIntegral.integral_congr (fun x _ ↦ he x)
  rw [hn, intervalIntegral.integral_sub (hc2.intervalIntegrable _ _)
    (hc3.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_comp_add_left, add_zero, sub_add_cancel]

lemma symmetric_shift_norm_le {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (R b C T : ℝ) (hR : T + 2 * |b| ≤ R)
    (hbound : ∀ x, T ≤ x → ‖g' x‖ ≤ C) :
    ‖∫ s in -R..R, g (s - b) - g s‖ ≤ C * |b| ^ 2 := by
  rw [symmetric_shift_boundary (continuous_iff_continuousAt.2 (fun x ↦ (hg x).continuousAt)) he]
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * |b|) (fun t ht ↦ ?_)) (by simp [pow_two, mul_assoc])
  have ht' : -|b| ≤ t := by
    have := ht.1
    have hmin : -|b| ≤ min 0 b := le_min (by linarith [abs_nonneg b]) (neg_abs_le b)
    linarith
  have hx : R - b + t ∈ Ici T := by
    have := le_abs_self b
    change T ≤ _
    linarith
  have hy : R + t ∈ Ici T := by change T ≤ _; linarith [abs_nonneg b]
  have hm := (convex_Ici T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hg x).hasDerivWithinAt) (fun x hx ↦ hbound x hx) hx hy
  simpa only [show R + t - (R - b + t) = b by ring, Real.norm_eq_abs] using hm

lemma symmetric_shift_tendsto_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (hlim : Tendsto g' atTop (𝓝 0)) (b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R, g (s - b) - g s) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hc : 0 < ε / (|b| ^ 2 + 1) := div_pos hε (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) _ hc
  refine ⟨T + 2 * |b|, fun R hR ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt (symmetric_shift_norm_le hg he R b (ε / (|b| ^ 2 + 1)) T hR (fun x hx ↦ ?_)) ?_
  · simpa only [dist_zero_right] using (hT x hx).le
  · have hden : 0 < |b| ^ 2 + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_quadratic_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t ^ 2 + z))
      (2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) s := by
  convert! (primitive_hasDerivAt σ hδ (s ^ 2 + z)).comp s
    (((hasDerivAt_id s).pow 2).add_const z) using 1
  simp only [id_eq, Nat.cast_ofNat, mul_one]
  ring

lemma primitive_quadratic_deriv_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Tendsto (fun s : ℝ ↦ 2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) atTop (𝓝 0) := by
  let a := δ / (δ + |z| + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : Tendsto (fun s : ℝ ↦ (2 * a ^ (σ - 3 / 2)) * s ^ (2 * σ - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 - 2 * σ by linarith)).const_mul
      (2 * a ^ (σ - 3 / 2))
    simpa only [show -(2 - 2 * σ) = 2 * σ - 2 by ring, mul_zero] using h
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ : 0 < s := by linarith
    have hb := Real.rpow_le_rpow_of_nonpos (show 0 < a * (1 + s ^ 2) by positivity)
      (shifted_base_lower hδ z s) (show σ - 3 / 2 ≤ 0 by linarith)
    have hsq := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hs₀)
      (show s ^ 2 ≤ 1 + s ^ 2 by linarith) (show σ - 3 / 2 ≤ 0 by linarith)
    rw [Real.mul_rpow ha.le (by positivity)] at hb
    calc
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (s ^ 2) ^ (σ - 3 / 2)) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs₀.le]
        norm_num only [Nat.cast_ofNat]
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one s]
        rw [show 2 * s ^ (1 : ℝ) * (a ^ (σ - 3 / 2) * s ^ ((2 : ℝ) * (σ - 3 / 2))) =
          (2 * a ^ (σ - 3 / 2)) * (s ^ (1 : ℝ) * s ^ (2 * (σ - 3 / 2))) by ring,
          ← Real.rpow_add hs₀]
        congr 2
        ring

lemma primitive_symmetric_shift_zero {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2 + z))
      atTop (𝓝 0) :=
  symmetric_shift_tendsto_zero (primitive_quadratic_hasDerivAt σ hδ z)
    (fun s ↦ by simp) (primitive_quadratic_deriv_tendsto hσ hδ z) b

/-- The symmetric shift identity, with exactly the cutoff used in the field. -/
lemma primitive_shift_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2))
      atTop (𝓝 (scalarMu σ δ z)) := by
  have hc := (primitive_differentiable σ hδ).continuous
  have h₁ := primitive_symmetric_shift_zero hσ hδ z b
  have h₂ := intervalIntegral_tendsto_integral (mu_integrand_integrable hσ hδ z)
    tendsto_neg_atTop_atBot tendsto_id
  have hh := (h₁.add h₂).const_mul (fieldNormalization σ)
  simp only [zero_add] at hh
  apply hh.congr
  intro R
  congr 1
  simp only [id_eq]
  rw [← intervalIntegral.integral_add
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - b) ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2 + z)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

end SharpLiebThirring.ScalarProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u19 u20 u21 u22 u23 u24

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u24} [Fintype n] [DecidableEq n]

lemma complexify_diagonal (x : n → ℝ) :
    complexify (diagonal x) = diagonal (fun i ↦ (x i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u32 u33 u34

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma matrixField_eq_realPart {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    matrixField σ δ k B = realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := by
  rw [← complexify_matrixField hσ hδ k hB, realPartCLM_complexify]

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u36} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma quadraticMatrix_diagonal (c b : n → ℝ) (s : ℝ) :
    quadraticMatrix (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ (((s - b i) ^ 2 + (c i - b i ^ 2) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [quadraticMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [quadraticMatrix, hij]

lemma fieldIntegrand_diagonal {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) (c b : n → ℝ) (s : ℝ) :
    fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ ((regularizedPrimitive σ δ ((s - b i) ^ 2 + (c i - b i ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2) : ℝ) : ℂ)) := by
  rw [fieldIntegrand, quadraticMatrix_diagonal,
    cfc_diagonal_real _ _ (primitive_differentiable σ hδ).continuous]
  ext i j
  by_cases hij : i = j <;> simp [hij, Complex.real_smul]

lemma hermitianField_diagonal {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (c b : n → ℝ) :
    hermitianField σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) =
      diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ)) := by
  have hC : (diagonal (fun i ↦ (c i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have hB : (diagonal (fun i ↦ (b i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  apply tendsto_nhds_unique (hermitianField_cutoff_limit hσ hδ hC hB)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have he (R : ℝ) := (entryCLM i j).intervalIntegral_comp_comm (μ := volume)
    (hc.intervalIntegrable (-R) R)
  simp only [entryCLM_apply] at he
  have he' (R : ℝ) :
      (fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s) i j =
      fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s i j := by
    simp only [Matrix.smul_apply]
    rw [← he R]
  suffices ht : Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R,
      fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ)))
        (diagonal (fun i ↦ (b i : ℂ))) s i j) atTop
      (𝓝 ((diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ))) i j)) by
    apply ht.congr
    intro R
    exact (he' R).symm
  simp only [fieldIntegrand_diagonal hδ]
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (primitive_shift_limit hσ hδ (c i - b i ^ 2) (b i))
    convert! hs using 1
    funext R
    rw [intervalIntegral.integral_ofReal]
    simp [Complex.real_smul]
  · simp only [diagonal_apply_ne _ hij, intervalIntegral.integral_zero, smul_zero]
    exact tendsto_const_nhds

lemma matrixField_diagonal {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k b : Fin N → ℝ) :
    matrixField σ δ k (diagonal b) = diagonal (fun i ↦ scalarMu σ δ (k i ^ 2 - b i ^ 2)) := by
  rw [matrixField_eq_realPart hσ hδ k (isHermitian_diagonal b),
    complexify_diagonal, complexify_diagonal, hermitianField_diagonal hσ hδ]
  ext i j
  by_cases hij : i = j <;> simp [realPartCLM, hij]

lemma continuous_scalarMu {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    Continuous (scalarMu σ δ) :=
  continuous_iff_continuousAt.mpr (fun _ ↦ (mu_hasDerivAt_integral hσ hδ _).continuousAt)

lemma fieldPrimitive_diagonal {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k b : Fin N → ℝ) :
    fieldPrimitive σ δ k (diagonal b) =
      -(∑ i, ∫ s in (0 : ℝ)..b i, scalarMu σ δ (k i ^ 2 - s ^ 2)) := by
  have hc := continuous_scalarMu hσ hδ
  have he (t : ℝ) : trace (diagonal b * matrixField σ δ k (t • diagonal b)) =
      ∑ i, b i * scalarMu σ δ (k i ^ 2 - (t * b i) ^ 2) := by
    rw [← diagonal_smul, matrixField_diagonal hσ hδ]
    simp [trace, diag]
  unfold fieldPrimitive
  simp_rw [he]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    exact_mod_cast (by simpa using (intervalIntegral.smul_integral_comp_mul_right
      (fun s : ℝ ↦ scalarMu σ δ (k i ^ 2 - s ^ 2)) (a := 0) (b := 1) (b i)))
  · intro i _
    exact (by fun_prop : Continuous (fun t : ℝ ↦ b i * scalarMu σ δ (k i ^ 2 - (t * b i) ^ 2))).intervalIntegrable _ _

lemma fieldPrimitive_endpoint_jump {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) =
      ∑ i, ∫ s in -(k i)..k i, scalarMu σ δ (k i ^ 2 - s ^ 2) := by
  rw [diagonal_neg, fieldPrimitive_diagonal hσ hδ, fieldPrimitive_diagonal hσ hδ]
  rw [neg_sub_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Continuous (fun s : ℝ ↦ scalarMu σ δ (k i ^ 2 - s ^ 2)) := by
    have := continuous_scalarMu hσ hδ
    fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator Topology

lemma scalar_boundary_regularized {σ δ k : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hk : 0 ≤ k) :
    (∫ s in -k..k, scalarMu σ δ (k ^ 2 - s ^ 2)) =
      ∫ s in -k..k, (k ^ 2 - s ^ 2 + δ) ^ σ - δ ^ σ := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by linarith : -k ≤ k)] at hs
  exact mu_eq_nonneg hσ hδ (by nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (show 0 ≤ k + s by linarith [hs.1])])

lemma scalar_boundary_limit {σ k : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hk : 0 ≤ k) :
    Tendsto (fun δ : ℝ ↦ ∫ s in -k..k, scalarMu σ δ (k ^ 2 - s ^ 2))
      (𝓝[>] 0) (𝓝 (∫ s in -k..k, (k ^ 2 - s ^ 2) ^ σ)) := by
  have hc : Continuous (fun δ : ℝ ↦ ∫ s in -k..k, (k ^ 2 - s ^ 2 + δ) ^ σ - δ ^ σ) := by
    simp_rw [intervalIntegral.integral_of_le (by linarith : -k ≤ k), ← integral_Icc_eq_integral_Ioc]
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((Real.continuous_rpow_const hσ₀.le).comp (by fun_prop)).sub
      ((Real.continuous_rpow_const hσ₀.le).comp (by fun_prop))
  have ht := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero, Real.zero_rpow hσ₀.ne', sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (scalar_boundary_regularized hσ₁ hδ hk).symm

lemma fieldPrimitive_endpoint_limit {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (k : Fin N → ℝ) (hk : ∀ i, 0 ≤ k i) :
    Tendsto (fun δ : ℝ ↦ fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k))
      (𝓝[>] 0) (𝓝 (∑ i, ∫ s in -(k i)..k i, (k i ^ 2 - s ^ 2) ^ σ)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ scalar_boundary_limit hσ₀ hσ₁ (hk i))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (fieldPrimitive_endpoint_jump hσ₁ hδ k).symm

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.SpectralProof
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

lemma sigma_holderConjugate {σ : ℝ} (hσ : 0 < σ) :
    (1 + σ).HolderConjugate (1 + 1 / σ) := by
  rw [Real.holderConjugate_iff]
  constructor
  · linarith
  · have h1 : 1 + σ ≠ 0 := by positivity
    have h2 : 1 + 1 / σ ≠ 0 := by positivity
    field_simp
    ring

lemma young_action_bound {σ W m : ℝ} (hσ : 0 < σ) (hW : 0 ≤ W) (hm : 0 ≤ m) :
    W * m - m ^ (1 + 1 / σ) ≤ actionYoungConstant σ * W ^ (1 + σ) := by
  let q := 1 + 1 / σ
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : 0 < 1 + σ := by positivity
  have hy := Real.young_inequality_of_nonneg (div_nonneg hW hq.le) hm (sigma_holderConjugate hσ)
  change W / q * m ≤ (W / q) ^ (1 + σ) / (1 + σ) + m ^ q / q at hy
  have hc : q * ((W / q) ^ (1 + σ) / (1 + σ)) = actionYoungConstant σ * W ^ (1 + σ) := by
    rw [Real.div_rpow hW hq.le]
    have hqe : q = (1 + σ) / σ := by dsimp [q]; field_simp; ring
    have hpow : q ^ (1 + σ) = q * ((1 + σ) ^ σ / σ ^ σ) := by
      rw [Real.rpow_add hq, Real.rpow_one, hqe, Real.div_rpow hp.le hσ.le]
    rw [hpow]
    unfold actionYoungConstant
    rw [Real.rpow_add hp, Real.rpow_one]
    have hsp := Real.rpow_pos_of_pos hσ σ
    have hpp := Real.rpow_pos_of_pos hp σ
    field_simp
  have hy' := mul_le_mul_of_nonneg_left hy hq.le
  have hm' : q * (m ^ q / q) = m ^ q := by field_simp
  have hw' : q * (W / q * m) = W * m := by field_simp
  rw [mul_add, hc, hm', hw'] at hy'
  linarith

end SharpLiebThirring.SpectralProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma tanh_sq_add_sech_sq (x : ℝ) :
    Real.tanh x ^ 2 + (Real.cosh x)⁻¹ ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hx := Real.cosh_sq_sub_sinh_sq x
  have hn : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith

lemma profileDerivative_hasDerivAt {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (profileDerivative r) ((1 - potential r x) * profile r x) x := by
  have ht := (tanh_hasDerivAt (r*x)).comp x ((hasDerivAt_id x).const_mul r)
  have hh := ht.neg.mul (profile_hasDerivAt hr x)
  convert! hh using 1
  unfold profileDerivative potential
  simp only [Function.comp_apply, Pi.neg_apply, mul_one]
  have he := congrArg (fun y : ℝ ↦ y * profile r x) (tanh_sq_add_sech_sq (r*x))
  nlinarith

lemma potential_continuous (r : ℝ) : Continuous (potential r) := by
  unfold potential
  exact continuous_const.mul (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
    (fun _ ↦ ne_of_gt (Real.cosh_pos _))).pow 2)

lemma potential_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 ≤ potential r x := by
  unfold potential
  positivity

end SharpLiebThirring.ExtremizerProof

namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma cutoff_bound (n : ℕ) (x : ℝ) : |cutoff n x| ≤ 1 := by
  unfold cutoff
  rw [abs_of_nonneg (baseCutoff.nonneg)]
  exact baseCutoff.le_one

lemma scale_tendsto : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma cutoff_tendsto (x : ℝ) : Tendsto (fun n : ℕ ↦ cutoff n x) atTop (𝓝 1) := by
  have hh := baseCutoff_smooth.continuous.continuousAt.tendsto.comp
    (scale_tendsto.mul_const x)
  have hb : (baseCutoff : ℝ → ℝ) 0 = 1 := by
    apply baseCutoff.one_of_mem_closedBall
    simp [baseCutoff, Metric.mem_closedBall]
  change Tendsto (fun n : ℕ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * x)) atTop (𝓝 1)
  convert! hh using 1; simp only [zero_mul, hb]

lemma cutoffDerivative_uniform_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ n x, |cutoffDerivative n x| ≤ D := by
  obtain ⟨D, hD⟩ := baseCutoff.hasCompactSupport.deriv.exists_bound_of_continuous
    (baseCutoff_smooth.continuous_deriv (by norm_num))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨D, hD0, fun n x ↦ ?_⟩
  unfold cutoffDerivative
  rw [abs_mul, abs_of_pos (inv_pos.mpr (scale_pos n))]
  have hi : (n + 1 : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_num
  exact (mul_le_mul_of_nonneg_right (hD _) (inv_pos.mpr (scale_pos n)).le).trans
    (mul_le_of_le_one_right hD0 hi)

lemma cutoffDerivative_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ ↦ cutoffDerivative n x) atTop (𝓝 0) := by
  have hh := (baseCutoff_smooth.continuous_deriv (by norm_num)).continuousAt.tendsto.comp
    (scale_tendsto.mul_const x)
  simpa [cutoffDerivative] using hh.mul scale_tendsto

/-- Dominated convergence for a uniformly bounded multiplier of an L¹ function. -/
lemma integral_multiplier_tendsto {a : ℕ → ℝ → ℂ} {l : ℂ} {g : ℝ → ℂ}
    (hg : Integrable g) (ha : ∀ n, AEStronglyMeasurable (a n) volume)
    {D : ℝ} (_hD : 0 ≤ D) (hb : ∀ n x, ‖a n x‖ ≤ D)
    (hl : ∀ x, Tendsto (fun n ↦ a n x) atTop (𝓝 l)) :
    Tendsto (fun n ↦ ∫ x : ℝ, a n x * g x) atTop (𝓝 (∫ x : ℝ, l * g x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ D * ‖g x‖)
  · exact fun n ↦ (ha n).mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul D
  · intro n
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _))
  · exact Filter.Eventually.of_forall (fun x ↦ (hl x).mul_const (g x))

end SharpLiebThirring.SobolevProof

namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

/-- Extend the distributional H¹ identity from compactly supported tests to
smooth L² tests with L² classical derivative. No pointwise representative of
an arbitrary H¹ element is assumed. -/
lemma weak_derivative_smooth_L2 (v : H1) {f f' : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf2 : MemLp f 2 volume) (hf'2 : MemLp f' 2 volume) :
    (∫ x : ℝ, v.val x * f' x) = -(∫ x : ℝ, v.grad x * f x) := by
  have hg0 : Integrable (fun x ↦ v.val x * f x) := v.val_memLp.integrable_mul hf2
  have hg1 : Integrable (fun x ↦ v.val x * f' x) := v.val_memLp.integrable_mul hf'2
  have hg2 : Integrable (fun x ↦ v.grad x * f x) := v.grad_memLp.integrable_mul hf2
  obtain ⟨D, hD, hDb⟩ := cutoffDerivative_uniform_bound
  have hc (n : ℕ) : ContDiff ℝ ∞ (fun x ↦ (cutoff n x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (cutoff_contDiff n)
  have hcm (n : ℕ) : AEStronglyMeasurable (fun x ↦ (cutoff n x : ℂ)) volume :=
    (hc n).continuous.aestronglyMeasurable
  have hdm (n : ℕ) : AEStronglyMeasurable (fun x ↦ (cutoffDerivative n x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (cutoffDerivative_continuous n)).aestronglyMeasurable
  have hcb (n : ℕ) (x : ℝ) : ‖(cutoff n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using cutoff_bound n x
  have hdb (n : ℕ) (x : ℝ) : ‖(cutoffDerivative n x : ℂ)‖ ≤ D := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hDb n x
  have hcl (x : ℝ) : Tendsto (fun n ↦ (cutoff n x : ℂ)) atTop (𝓝 1) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoff_tendsto x)
  have hdl (x : ℝ) : Tendsto (fun n ↦ (cutoffDerivative n x : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoffDerivative_tendsto x)
  have h0 := integral_multiplier_tendsto hg0 hdm hD hdb hdl
  have h1 := integral_multiplier_tendsto hg1 hcm (by norm_num : (0 : ℝ) ≤ 1) hcb hcl
  have h2 := integral_multiplier_tendsto hg2 hcm (by norm_num : (0 : ℝ) ≤ 1) hcb hcl
  simp only [zero_mul, one_mul, integral_zero] at h0 h1 h2
  have heq (n : ℕ) :
      (∫ x : ℝ, (cutoffDerivative n x : ℂ) * (v.val x * f x)) +
      (∫ x : ℝ, (cutoff n x : ℂ) * (v.val x * f' x)) =
      -(∫ x : ℝ, (cutoff n x : ℂ) * (v.grad x * f x)) := by
    let φ : ℝ → ℂ := fun x ↦ (cutoff n x : ℂ) * f x
    have hφ : ContDiff ℝ ∞ φ := (hc n).mul hf
    have hcc : HasCompactSupport (fun x ↦ (cutoff n x : ℂ)) :=
      (cutoff_compact n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hφc : HasCompactSupport φ := hcc.mul_right
    have hφd (x : ℝ) : deriv φ x =
        (cutoffDerivative n x : ℂ) * f x + (cutoff n x : ℂ) * f' x := by
      exact (((cutoff_hasDerivAt n x).ofReal_comp).mul (hd x)).deriv
    have hh := v.weak_derivative φ hφ hφc
    have hi0 := hg0.bdd_mul (hdm n) (Filter.Eventually.of_forall (hdb n))
    have hi1 := hg1.bdd_mul (hcm n) (Filter.Eventually.of_forall (hcb n))
    rw [← integral_add hi0 hi1]
    calc
      _ = ∫ x : ℝ, v.val x * deriv φ x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp only; rw [hφd]; ring)
      _ = -(∫ x : ℝ, v.grad x * φ x) := hh
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp [φ]; ring)
  have he : Tendsto (fun n ↦ -(∫ x : ℝ, (cutoff n x : ℂ) * (v.grad x * f x)))
      atTop (𝓝 (∫ x : ℝ, v.val x * f' x)) := by
    simpa only [zero_add] using (h0.add h1).congr (fun n ↦ heq n)
  exact tendsto_nhds_unique he h2.neg

end SharpLiebThirring.SobolevProof

namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma potential_le {r : ℝ} (hr : 0 < r) (x : ℝ) : potential r x ≤ r + 1 := by
  have hi : (Real.cosh (r*x))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh _)
  have hi0 : 0 ≤ (Real.cosh (r*x))⁻¹ := inv_nonneg.mpr (Real.cosh_pos _).le
  have hs : (Real.cosh (r*x))⁻¹ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_right (by linarith) hs

lemma profileDerivative_contDiff (r : ℝ) : ContDiff ℝ ∞ (profileDerivative r) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    convert! (Real.contDiff_sinh.div Real.contDiff_cosh
      (fun _ ↦ ne_of_gt (Real.cosh_pos _))) using 1
    funext t
    exact Real.tanh_eq_sinh_div_cosh t
  exact ((ht.comp (contDiff_const.mul contDiff_id)).neg).mul
    ((profile_contDiff r).of_le le_top)

lemma profileSecond_continuous (r : ℝ) : Continuous (profileSecond r) :=
  (continuous_const.sub (potential_continuous r)).mul (profile_continuous r)

lemma profileSecond_memLp (r : ℝ) (hr : 0 < r) : MemLp (profileSecond r) 2 volume := by
  apply ((profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).const_mul (r + 2)).mono'
    (profileSecond_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [profileSecond, Real.norm_eq_abs, abs_mul, abs_of_pos (profile_pos r x)]
    apply mul_le_mul_of_nonneg_right _ (profile_pos r x).le
    have hW := potential_nonneg hr x
    have hW' := potential_le hr x
    apply abs_le.mpr
    constructor <;> linarith)

lemma boundState_weak_ode {r : ℝ} (hr : 0 < r) (v : H1) :
    (∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) =
    -(∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) := by
  have hh := SobolevProof.weak_derivative_smooth_L2 v
    (f := fun x ↦ (profileDerivative r x : ℂ))
    (f' := fun x ↦ (profileSecond r x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (profileDerivative_contDiff r))
    (fun x ↦ (profileDerivative_hasDerivAt hr x).ofReal_comp)
    (profileDerivative_memLp r hr (by norm_num) (by norm_num)).ofReal
    (profileSecond_memLp r hr).ofReal
  have hc := congrArg (starRingEnd ℂ) hh
  simp only [map_neg, ← integral_conj, map_mul, Complex.conj_ofReal] at hc
  change (∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) =
    -(∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) at hc
  exact (neg_eq_iff_eq_neg.mpr hc).symm

lemma boundState_negativeEigenfunction {r : ℝ} (hr : 0 < r) :
    IsNegativeEigenfunction (potential r) 1 (boundState r hr) := by
  refine ⟨by norm_num, fun v ↦ ?_⟩
  have hψ := (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).ofReal (K := ℂ)
  have hi : Integrable (fun x ↦ star (v.val x) * (profile r x : ℂ)) :=
    v.val_memLp.star.integrable_mul hψ
  have hWm : AEStronglyMeasurable (fun x ↦ (potential r x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (potential_continuous r)).aestronglyMeasurable
  have hWb : ∀ᵐ x : ℝ, ‖(potential r x : ℂ)‖ ≤ r + 1 := by
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hr x)]
      exact potential_le hr x)
  have hiW := hi.bdd_mul hWm hWb
  change (∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) -
    (∫ x : ℝ, (potential r x : ℂ) * star (v.val x) * (profile r x : ℂ)) =
    -(1 ^ 2 : ℝ) * (∫ x : ℝ, star (v.val x) * (profile r x : ℂ))
  rw [boundState_weak_ode hr]
  have hs : (∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) =
      (∫ x : ℝ, star (v.val x) * (profile r x : ℂ)) -
      (∫ x : ℝ, (potential r x : ℂ) * (star (v.val x) * (profile r x : ℂ))) := by
    rw [← integral_sub hi hiW]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      simp only [profileSecond, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
      ring)
  rw [hs]
  simp only [mul_assoc, one_pow, Complex.ofReal_one, neg_mul, one_mul]
  ring

end SharpLiebThirring.ExtremizerProof

namespace SharpLiebThirring
open MeasureTheory

lemma l2Pairing_scale_both (c : ℂ) (u : H1) :
    l2Pairing (scaleH1 c u) (scaleH1 c u) = star c * c * l2Pairing u u := by
  change (∫ x : ℝ, star (c * u.val x) * (c * u.val x)) = _
  simp only [star_mul]
  have he (x : ℝ) : star (u.val x) * star c * (c * u.val x) =
      (star c * c) * (star (u.val x) * u.val x) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

lemma l2Pairing_scale_right (c : ℂ) (v u : H1) :
    l2Pairing v (scaleH1 c u) = c * l2Pairing v u := by
  change (∫ x : ℝ, star (v.val x) * (c * u.val x)) = _
  simp_rw [show ∀ a b : ℂ, a * (c * b) = c * (a*b) by intros; ring]
  exact integral_const_mul _ _

lemma schrodingerForm_scale_right (W : ℝ → ℝ) (c : ℂ) (v u : H1) :
    schrodingerForm W v (scaleH1 c u) = c * schrodingerForm W v u := by
  change (∫ x : ℝ, star (v.grad x) * (c * u.grad x)) -
    (∫ x : ℝ, (W x : ℂ) * star (v.val x) * (c * u.val x)) = _
  simp_rw [show ∀ a b : ℂ, a * (c * b) = c * (a*b) by intros; ring]
  rw [integral_const_mul, integral_const_mul]
  exact (mul_sub _ _ _).symm

lemma IsNegativeEigenfunction.scale {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hu : IsNegativeEigenfunction W k u) (c : ℂ) :
    IsNegativeEigenfunction W k (scaleH1 c u) := by
  refine ⟨hu.1, fun v ↦ ?_⟩
  rw [schrodingerForm_scale_right, l2Pairing_scale_right, hu.2 v]
  ring

lemma oneStateMoment_le_negativeMoment (γ : ℝ) (W : ℝ → ℝ) :
    oneStateMoment γ W ≤ negativeMoment γ W := by
  unfold oneStateMoment
  refine iSup_le (fun u ↦ iSup_le (fun k ↦ iSup_le (fun hnorm ↦ iSup_le (fun hneg ↦ ?_))))
  have hu : IsOrthonormalFamily (fun _ : Fin 1 ↦ u) := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, hnorm]
  unfold negativeMoment
  apply le_iSup_of_le 1
  apply le_iSup_of_le (fun _ : Fin 1 ↦ u)
  apply le_iSup_of_le (fun _ : Fin 1 ↦ k)
  apply le_iSup_of_le hu
  apply le_iSup_of_le (fun _ : Fin 1 ↦ hneg)
  simp

lemma oneStateConstant_le_optimalConstant (γ : ℝ) :
    oneStateConstant γ ≤ optimalConstant γ := by
  unfold oneStateConstant
  refine iSup_le (fun W ↦ iSup_le (fun hW ↦ iSup_le (fun hpos ↦ ?_)))
  unfold optimalConstant
  apply le_iSup_of_le W
  apply le_iSup_of_le hW
  apply le_iSup_of_le hpos
  exact ENNReal.div_le_div_right (oneStateMoment_le_negativeMoment γ W) _

end SharpLiebThirring

namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory

lemma profile_norm_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ profile r x ^ 2) := by
  convert!
    (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).integrable_mul
      (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)) using 1
  funext x
  simp only [pow_two, Pi.mul_apply]

lemma profile_norm_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ x : ℝ, profile r x ^ 2 := by
  apply (integral_pos_iff_support_of_nonneg (fun x ↦ sq_nonneg _) (profile_norm_integrable hr)).mpr
  have hs : Function.support (fun x : ℝ ↦ profile r x ^ 2) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (sq_pos_of_pos (profile_pos r x)).ne'
  rw [hs]
  simp

lemma boundState_l2Pairing {r : ℝ} (hr : 0 < r) :
    l2Pairing (boundState r hr) (boundState r hr) =
      ((∫ x : ℝ, profile r x ^ 2) : ℝ) := by
  change (∫ x : ℝ, star (profile r x : ℂ) * (profile r x : ℂ)) = _
  have ht : (fun x : ℝ ↦ star (profile r x : ℂ) * (profile r x : ℂ)) =
      (fun x : ℝ ↦ ((profile r x ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp only [Complex.star_def, Complex.conj_ofReal, pow_two, Complex.ofReal_mul]
  rw [ht]
  exact integral_ofReal (𝕜 := ℂ)

lemma normalizedBoundState_norm {r : ℝ} (hr : 0 < r) :
    l2Pairing (normalizedBoundState r hr) (normalizedBoundState r hr) = 1 := by
  rw [normalizedBoundState, l2Pairing_scale_both, boundState_l2Pairing hr]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  norm_cast
  have hpos := profile_norm_pos hr
  have hs := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (∫ x : ℝ, profile r x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  nlinarith

lemma normalizedBoundState_eigenfunction {r : ℝ} (hr : 0 < r) :
    IsNegativeEigenfunction (potential r) 1 (normalizedBoundState r hr) :=
  (boundState_negativeEigenfunction hr).scale _

lemma one_le_oneStateMoment {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    1 ≤ oneStateMoment γ (potential r) := by
  unfold oneStateMoment
  apply le_iSup_of_le (normalizedBoundState r hr)
  apply le_iSup_of_le 1
  apply le_iSup_of_le (normalizedBoundState_norm hr)
  apply le_iSup_of_le (normalizedBoundState_eigenfunction hr)
  simp

lemma one_le_negativeMoment {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    1 ≤ negativeMoment γ (potential r) :=
  (one_le_oneStateMoment hr γ).trans (oneStateMoment_le_negativeMoment γ (potential r))

end SharpLiebThirring.ExtremizerProof

namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma memLp_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (fun x : ℝ ↦ Real.exp (-c * |x|)) p volume := by
  have hm : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|)) := by fun_prop
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable hp hp').mp
  have hi := integrable_exp_neg_abs (mul_pos hc (ENNReal.toReal_pos hp hp'))
  convert! hi using 1
  funext x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  ring

lemma cosh_inv_exponential_bound (x : ℝ) :
    (Real.cosh x)⁻¹ ≤ 2 * Real.exp (-|x|) := by
  apply (inv_le_iff_one_le_mul₀ (Real.cosh_pos x)).mpr
  have hh := mul_le_mul_of_nonneg_right (cosh_lower_exponential x) (Real.exp_pos (-|x|)).le
  have he : Real.exp |x| * Real.exp (-|x|) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

lemma potential_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    potential r x ≤ 4 * (r + 1) * Real.exp (-(2*r) * |x|) := by
  have hi0 : 0 ≤ (Real.cosh (r*x))⁻¹ := inv_nonneg.mpr (Real.cosh_pos _).le
  have hh := pow_le_pow_left₀ hi0 (cosh_inv_exponential_bound (r*x)) 2
  have he : (2 * Real.exp (-|r*x|)) ^ 2 = 4 * Real.exp (-(2*r) * |x|) := by
    rw [mul_pow, ← Real.exp_nat_mul, abs_mul, abs_of_pos hr]
    congr 2 <;> ring
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r + 1)).trans_eq (by ring)

lemma potential_memLp {r : ℝ} (hr : 0 < r) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hp' : p ≠ ⊤) : MemLp (potential r) p volume := by
  apply ((memLp_exp_neg_mul_abs (by positivity : 0 < 2*r) hp hp').const_mul
    (4 * (r + 1))).mono' (potential_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hr x)]
    exact potential_exponential_bound hr x)

lemma equalityPotential_admissible {γ : ℝ} (hγ : 1 / 2 < γ) :
    Admissible γ (equalityPotential γ) := by
  have hr : 0 < (γ - 1 / 2)⁻¹ := inv_pos.mpr (by linarith)
  constructor
  · exact Filter.Eventually.of_forall (fun x ↦ potential_nonneg hr x)
  · exact potential_memLp hr (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top

lemma potential_pos {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 < potential r x := by
  unfold potential
  positivity

lemma potential_mass_pos {γ r : ℝ} (hr : 0 < r) :
    0 < potentialMass γ (potential r) := by
  unfold potentialMass
  have hm : Measurable (fun x : ℝ ↦ (ENNReal.ofReal (potential r x)) ^ (γ + 1/2)) :=
    ((potential_continuous r).measurable.ennreal_ofReal).pow_const _
  apply (lintegral_pos_iff_support hm).mpr
  have hs : Function.support (fun x : ℝ ↦ (ENNReal.ofReal (potential r x)) ^ (γ + 1/2)) = Set.univ := by
    apply Function.support_eq_univ
    intro x
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (potential_pos hr x)) ENNReal.ofReal_ne_top).ne'
  rw [hs]
  simp

end SharpLiebThirring.ExtremizerProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.IntervalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set Filter ContinuationGap
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma finite_action_upper_test {σ l r S : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    (hS : ∀ C : LowerSpace N,
      (∫ t in l..r, actionDensity σ k (C.val *ᵥ u t) (C.val *ᵥ v t)) ≤ S) :
    (∑ i, ∫ s in -(k i)..k i, (k i^2-s^2)^σ) ≤ S := by
  apply le_of_tendsto (fieldPrimitive_endpoint_limit hσ₀ hσ₁ k (fun i ↦ (hk i).le))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact regularized_action_upper_test hσ₀ hσ₁ hδ hlr k hk u v hu hv hud hul hur ho hS

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.Gamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.ConstantProof
open MeasureTheory Set Filter
open scoped Topology

lemma real_beta_symmetric {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) =
      Real.Gamma (σ+1)^2 / Real.Gamma (2*(σ+1)) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((σ+1 : ℝ) : ℂ) ((σ+1 : ℝ) : ℂ)
    (by simpa using (show 0 < σ+1 by linarith)) (by simpa using (show 0 < σ+1 by linarith))
  have hi : Complex.betaIntegral ((σ+1 : ℝ) : ℂ) ((σ+1 : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ : ℝ) : ℂ) := by
    rw [Complex.betaIntegral,← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    push_cast
    rw [add_sub_cancel_right,← Complex.ofReal_cpow hx.1,
      show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,← Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  rw [hi,Complex.Gamma_ofReal,← Complex.ofReal_add,
    Complex.Gamma_ofReal] at h
  have hh : (σ+1)+(σ+1) = 2*(σ+1) := by ring
  rw [hh] at h
  have hh' : (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) =
      Real.Gamma (σ+1)*Real.Gamma (σ+1) / Real.Gamma (2*(σ+1)) := by exact_mod_cast h
  simpa only [pow_two] using hh'

lemma betaAction_eq_beta {σ : ℝ} (_hσ : 0 < σ) :
    betaAction σ = 2 * (4 : ℝ)^σ * (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) := by
  have h := intervalIntegral.integral_comp_mul_add
    (fun x : ℝ ↦ (1-x^2)^σ) (a := 0) (b := 1) (c := (2 : ℝ)) (by norm_num) (-1)
  norm_num at h
  have hi : (∫ t in (0 : ℝ)..1, (1-(2*t-1)^2)^σ) =
      (4 : ℝ)^σ * (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    dsimp only
    rw [show 1-(2*x-1)^2 = 4*(x*(1-x)) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
      Real.mul_rpow hx.1 (sub_nonneg.mpr hx.2)]
  rw [show (fun x : ℝ ↦ (1-(2*x+ -1)^2)^σ) = fun x ↦ (1-(2*x-1)^2)^σ by ext; congr 2] at h
  rw [hi] at h
  unfold betaAction
  linarith

lemma betaAction_pos {σ : ℝ} (hσ : 0 < σ) : 0 < betaAction σ := by
  rw [betaAction_eq_beta hσ,real_beta_symmetric hσ]
  have hG := Real.Gamma_pos_of_pos (show 0 < σ+1 by linarith)
  have hG' := Real.Gamma_pos_of_pos (show 0 < 2*(σ+1) by linarith)
  positivity

end SharpLiebThirring.ConstantProof
namespace SharpLiebThirring.ConstantProof
open MeasureTheory Set Filter
open scoped Topology

lemma betaAction_eq_Gamma {σ : ℝ} (hσ : 0 < σ) :
    betaAction σ = Real.sqrt Real.pi * Real.Gamma (σ+1) / Real.Gamma (σ+3/2) := by
  have h := Real.Gamma_mul_Gamma_add_half (σ+1)
  have he : σ+1+1/2 = σ+3/2 := by ring
  rw [he] at h
  have hp : (2 : ℝ)*4^σ*2^(1-2*(σ+1)) = 1 := by
    have hh : (2 : ℝ)*4^σ*2^(1-2*(σ+1)) = 2^(1+2*σ+(1-2*(σ+1))) := by
      rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num),Real.rpow_two]
      norm_num
    rw [hh,show 1+2*σ+(1-2*(σ+1)) = 0 by ring,Real.rpow_zero]
  have hg' : Real.Gamma (σ+3/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < σ+3/2)).ne'
  have hg'' : Real.Gamma (2*(σ+1)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < 2*(σ+1))).ne'
  rw [betaAction_eq_beta hσ,real_beta_symmetric hσ]
  apply (eq_div_iff hg').mpr
  calc
    (2*4^σ*(Real.Gamma (σ+1)^2/Real.Gamma (2*(σ+1))))*Real.Gamma (σ+3/2) =
        (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(2*4^σ*(Real.Gamma (σ+1)*Real.Gamma (σ+3/2))) := by ring
    _ = (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(2*4^σ*(Real.Gamma (2*(σ+1))*2^(1-2*(σ+1))*Real.sqrt Real.pi)) := by rw [h]
    _ = (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(Real.Gamma (2*(σ+1))*Real.sqrt Real.pi) := by
      congr 1
      calc
        _ = Real.Gamma (2*(σ+1))*Real.sqrt Real.pi*(2*4^σ*2^(1-2*(σ+1))) := by ring
        _ = _ := by rw [hp,mul_one]
    _ = _ := by field_simp

lemma boundary_action_scaling {σ k : ℝ} (_hσ : 0 < σ) (hk : 0 < k) :
    (∫ s in -k..k, (k^2-s^2)^σ) = k^(1+2*σ)*betaAction σ := by
  have hi := intervalIntegral.integral_comp_mul_left (fun s : ℝ ↦ (k^2-s^2)^σ)
    (a := -1) (b := 1) (c := k) hk.ne'
  simp only [mul_neg_one,mul_one] at hi
  have hj : (∫ s in (-1 : ℝ)..1, (k^2-(k*s)^2)^σ) = k^(2*σ)*betaAction σ := by
    rw [betaAction,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    dsimp only
    have hs' : 0 ≤ 1-s^2 := by nlinarith [hs.1,hs.2]
    rw [show k^2-(k*s)^2 = k^2*(1-s^2) by ring,Real.mul_rpow (sq_nonneg _) hs',
      ← Real.rpow_two k,← Real.rpow_mul hk.le]
  rw [hj] at hi
  have he : k^(1+2*σ) = k*k^(2*σ) := by rw [Real.rpow_add hk,Real.rpow_one]
  rw [he]
  simp only [smul_eq_mul] at hi
  field_simp [hk.ne'] at hi
  nlinarith [hi]

lemma young_over_beta {σ : ℝ} (hσ : 0 < σ) :
    (σ^σ/(1+σ)^(1+σ))/betaAction σ =
      (σ/(σ+1))^σ*Real.Gamma (σ+3/2)/(Real.sqrt Real.pi*Real.Gamma (σ+2)) := by
  have hg := Real.Gamma_add_one (show σ+1 ≠ 0 by linarith)
  rw [show σ+1+1 = σ+2 by ring] at hg
  rw [betaAction_eq_Gamma hσ,Real.div_rpow hσ.le (by linarith : 0 ≤ σ+1),
    show 1+σ = σ+1 by ring,Real.rpow_add (by linarith : 0 < σ+1),Real.rpow_one,hg]
  field_simp

end SharpLiebThirring.ConstantProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.QuadraticForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u166 u167 u168 u169 u170


noncomputable section
open Filter Set
open scoped Topology
namespace SharpLiebThirring.SpectralProof

lemma quadratic_error_bound {ι : Type u166} [Fintype ι] (M : ι → ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hM : ∀ i j, |M i j| ≤ ε) (c : ι → ℝ) :
    (∑ i, ∑ j, c i*c j*M i j) ≤ ε*(Fintype.card ι)*∑ i, c i^2 := by
  classical
  calc
    _ ≤ ∑ i, ∑ j, ε*(|c i| *|c j|) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      calc
        _ ≤ |c i*c j*M i j| := le_abs_self _
        _ = |c i| *|c j| *|M i j| := by rw [abs_mul,abs_mul]
        _ ≤ |c i| *|c j| *ε := mul_le_mul_of_nonneg_left (hM i j) (by positivity)
        _ = _ := by ring
    _ = ε*(∑ i, |c i|)^2 := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul,pow_two]
    _ ≤ ε*((Fintype.card ι)*∑ i, c i^2) := by
      apply mul_le_mul_of_nonneg_left _ hε
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,sq_abs] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : ℝ)) (fun i ↦ |c i|)
    _ = _ := by ring

/-- A strict negative diagonal is stable under entrywise perturbations. -/
lemma eventually_negative_quadratic {ι : Type u167} [Fintype ι] [DecidableEq ι] (M : ℕ → ι → ι → ℝ)
    (d : ι → ℝ) (hd : ∀ i, d i < 0)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (𝓝 (if i=j then d i else 0))) :
    ∀ᶠ n in atTop, ∀ c : ι → ℝ, (∑ i, ∑ j, c i*c j*M n i j) ≤ 0 := by
  classical
  by_cases hi : IsEmpty ι
  · simp
  let : Nonempty ι := not_isEmpty_iff.mp hi
  obtain ⟨a,ha⟩ := Finite.exists_max d
  let ε := -d a/((Fintype.card ι : ℝ)+1)
  have he : 0 < ε := div_pos (neg_pos.mpr (hd a)) (by positivity)
  have hε : ε*(Fintype.card ι : ℝ) ≤ -d a := by
    have hh : ε*((Fintype.card ι : ℝ)+1) = -d a := by dsimp [ε]; field_simp
    nlinarith
  have hev : ∀ᶠ n in atTop, ∀ i j, |M n i j-(if i=j then d i else 0)| ≤ ε := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    exact ((tendsto_order.1 (((hM i j).sub_const (if i=j then d i else 0)).abs)).2 ε (by simpa using he)).mono
      (fun n hn ↦ le_of_lt (by simpa using hn))
  filter_upwards [hev] with n hn c
  have hb := quadratic_error_bound (fun i j ↦ M n i j-(if i=j then d i else 0)) he.le hn c
  have hid : (∑ i, ∑ j, c i*c j*(if i=j then d i else 0)) = ∑ i, c i^2*d i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite,pow_two]
  have hsplit : (∑ i, ∑ j, c i*c j*M n i j) =
      (∑ i, ∑ j, c i*c j*(M n i j-(if i=j then d i else 0))) + ∑ i, c i^2*d i := by
    rw [← hid,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsplit]
  have hd' : (∑ i, c i^2*d i) ≤ d a*∑ i, c i^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    exact (mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hs : 0 ≤ ∑ i, c i^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hε hs]

end SharpLiebThirring.SpectralProof

end


noncomputable section
open Module
namespace SharpLiebThirring.SpectralProof

variable {E : Type u168} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complex orthonormal vectors give twice as many real orthonormal vectors. -/
lemma doubled_orthonormal {ι : Type u169} [DecidableEq ι] (a b : ι → E)
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0) :
    Orthonormal ℝ (fun z : ι × Bool ↦
      WithLp.toLp 2 (if z.2 then (-b z.1,a z.1) else (a z.1,b z.1))) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,p⟩ ⟨j,q⟩
  cases p <;> cases q <;>
    simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,WithLp.prod_inner_apply,
      inner_neg_left,inner_neg_right,neg_neg,
      Prod.mk.injEq,and_true,and_false,ite_false]
  · exact hr i j
  · linarith [hi i j]
  · linarith [hi j i,real_inner_comm (a j) (b i),real_inner_comm (b j) (a i)]
  · simpa only [add_comm] using hr i j

lemma complex_family_card_le_real_dimension {ι : Type u170} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ E] (a b : ι → E)
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0) :
    Fintype.card ι ≤ finrank ℝ E := by
  have h := (doubled_orthonormal a b hr hi).linearIndependent.fintype_card_le_finrank
  rw [(WithLp.linearEquiv 2 ℝ (E×E)).finrank_eq,finrank_prod] at h
  simp only [Fintype.card_prod,Fintype.card_bool] at h
  omega

end SharpLiebThirring.SpectralProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.CutoffEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set
open scoped Topology

namespace C1L2

lemma inner_eq_integral (u v : C1L2) : inner ℝ u v = ∫ x, u.val x*v.val x := by
  change inner ℝ (toLp u) (toLp v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.val_memLp.coeFn_toLp,v.val_memLp.coeFn_toLp] with x hx hy
  change (toLp v) x*(toLp u) x = u.val x*v.val x
  rw [show (toLp u) x = u.val x from hx,show (toLp v) x = v.val x from hy,mul_comm]

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace C1L2

lemma contDiff (u : C1L2) : ContDiff ℝ 1 u.val := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x ↦ (u.hasDerivAt x).differentiableAt,
    by convert u.grad_continuous using 1; ext x; exact (u.hasDerivAt x).deriv⟩

lemma ac (u : C1L2) (a b : ℝ) : AbsolutelyContinuousOnInterval u.val a b :=
  u.contDiff.contDiffOn.absolutelyContinuousOnInterval

lemma IsEigen.grad_ac {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u.grad a b := by
  have hh : u.grad = fun x ↦ u.grad a+∫ t in a..x, (k^2-W t)*u.val t := by
    funext x; linarith [hu a x]
  rw [hh]
  exact ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ u.grad a)).contDiffOn.absolutelyContinuousOnInterval).add
    ((locallyIntegrable_intervalIntegrable (eigen_integrable hW k u) a b).absolutelyContinuousOnInterval_intervalIntegral (by simp))

lemma IsEigen.grad_deriv {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) :
    ∀ᵐ x, deriv u.grad x = (k^2-W x)*u.val x := by
  have hh : u.grad = fun x ↦ u.grad 0+∫ t in (0 : ℝ)..x, (k^2-W t)*u.val t := by
    funext x; linarith [hu 0 x]
  have hd := LocallyIntegrable.ae_hasDerivAt_integral (eigen_integrable hW k u)
  filter_upwards [hd] with x hx
  rw [hh]
  exact ((hx 0).const_add (u.grad 0)).deriv

lemma IsEigen.weak_interval {W : ℝ → ℝ} {k a b : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2)
    (ha : v.val a = 0) (hb : v.val b = 0) :
    (∫ x in a..b, u.grad x*v.grad x) = -(∫ x in a..b, (k^2-W x)*u.val x*v.val x) := by
  have h := (hu.grad_ac hW a b).integral_mul_deriv_eq_deriv_mul (v.ac a b)
  rw [v.deriv_val,ha,hb,mul_zero,mul_zero,sub_self,zero_sub] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hu.grad_deriv hW] with x hx _
  rw [hx]

lemma IsEigen.weak_compact {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2)
    (hvc : HasCompactSupport v.val) :
    (∫ x, u.grad x*v.grad x) = -(∫ x, (k^2-W x)*u.val x*v.val x) := by
  obtain ⟨R,hR,hzero⟩ := hvc.exists_pos_le_norm
  have hvd : v.grad = deriv v.val := v.deriv_val.symm
  have hi1 : Function.support (fun x ↦ u.grad x*v.grad x) ⊆ Ioc (-(R+1)) (R+1) := by
    intro x hx
    have hxs : x ∈ tsupport v.val :=
      tsupport_deriv_subset (subset_tsupport (deriv v.val) (by
        rw [← hvd]; exact (mul_ne_zero_iff.mp hx).2))
    have hRp : tsupport v.val ⊆ closedBall (0 : ℝ) R := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs]
      exact le_of_lt (lt_of_not_ge (fun h ↦ hx (hzero x h)))
    have hxR := hRp hxs
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_le] at hxR
    constructor <;> linarith [hxR.1,hxR.2]
  have hi2 : Function.support (fun x ↦ (k^2-W x)*u.val x*v.val x) ⊆ Ioc (-(R+1)) (R+1) := by
    intro x hx
    have hxR : |x| < R := lt_of_not_ge (fun hh ↦ (mul_ne_zero_iff.mp hx).2 (hzero x hh))
    rw [abs_lt] at hxR
    constructor <;> linarith [hxR.1,hxR.2]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hi1,
    ← intervalIntegral.integral_eq_integral_of_support_subset hi2]
  exact hu.weak_interval hW v (hzero _ (by rw [Real.norm_eq_abs,abs_neg,abs_of_pos (by linarith)]; linarith))
    (hzero _ (by rw [Real.norm_eq_abs,abs_of_pos (by linarith)]; linarith))

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace C1L2

lemma cut_compact (n : ℕ) (u : C1L2) : HasCompactSupport (u.cut n).val := (cutoff_compact n).mul_right

lemma integrable_val_mul (u v : C1L2) : Integrable (fun x ↦ u.val x*v.val x) :=
  u.val_memLp.integrable_mul v.val_memLp
lemma integrable_grad_mul (u v : C1L2) : Integrable (fun x ↦ u.grad x*v.grad x) :=
  u.grad_memLp.integrable_mul v.grad_memLp

lemma integral_real_multiplier_tendsto {a : ℕ → ℝ → ℝ} {l : ℝ} {g : ℝ → ℝ}
    (hg : Integrable g) (ha : ∀ n, AEStronglyMeasurable (a n))
    {D : ℝ} (hD : ∀ n x, |a n x| ≤ D)
    (hl : ∀ x, Tendsto (fun n ↦ a n x) atTop (𝓝 l)) :
    Tendsto (fun n ↦ ∫ x, a n x*g x) atTop (𝓝 (l*∫ x, g x)) := by
  rw [← integral_const_mul]
  apply tendsto_integral_of_dominated_convergence (fun x ↦ D*|g x|)
  · exact fun n ↦ (ha n).mul hg.aestronglyMeasurable
  · exact hg.abs.const_mul D
  · intro n; exact ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs,abs_mul]; exact mul_le_mul_of_nonneg_right (hD n x) (abs_nonneg _))
  · exact ae_of_all _ (fun x ↦ (hl x).mul_const _)

lemma cutoff_inner_tendsto (u v : C1L2) :
    Tendsto (fun n ↦ inner ℝ (u.cut n) (v.cut n)) atTop (𝓝 (inner ℝ u v)) := by
  simp_rw [inner_eq_integral,cut_val,show ∀ (n : ℕ) (x : ℝ),
    cutoff n x*u.val x*(cutoff n x*v.val x) = cutoff n x^2*(u.val x*v.val x) by intros; ring]
  simpa only [one_mul] using integral_real_multiplier_tendsto (l := 1) (a := fun n x ↦ cutoff n x^2) (u.integrable_val_mul v)
    (fun n ↦ ((cutoff_contDiff n).continuous.pow 2).aestronglyMeasurable)
    (D := 1) (fun n x ↦ by
      rw [abs_pow]; have h := cutoff_bound n x; nlinarith [abs_nonneg (cutoff n x)])
    (fun x ↦ by simpa using (cutoff_tendsto x).pow 2)

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma energy_symm (W : ℝ → ℝ) (u v : C1L2) : energy W u v = energy W v u := by
  unfold energy
  congr 1 <;> apply integral_congr_ae <;> exact ae_of_all _ (fun _ ↦ by ring)

lemma integrable_potential {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (u v : C1L2)
    (hv : HasCompactSupport v.val) : Integrable (fun x ↦ W x*u.val x*v.val x) :=
  (hW.mul_continuous u.continuous).integrable_smul_right_of_hasCompactSupport v.continuous hv

private lemma cut_energy_algebra (c d u v du dv k w : ℝ) :
    (d*u+c*du)*(d*v+c*dv)-w*(c*u)*(c*v) =
      (du*(d*(c*v)+c*(d*v+c*dv))+(k^2-w)*u*(c*(c*v)))+
        -k^2*((c*u)*(c*v))+d^2*(u*v)+(c*d)*(u*dv-du*v) := by ring

lemma cut_error_integrable (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ cutoffDerivative n x^2*(u.val x*v.val x)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffDerivative_uniform_bound
  apply (u.integrable_val_mul v).bdd_mul
    (((cutoffDerivative_continuous n).pow 2).aestronglyMeasurable) (c := D^2)
  exact ae_of_all _ (fun x ↦ by
    rw [Real.norm_eq_abs,Pi.pow_apply,abs_pow]
    nlinarith [hDb n x,abs_nonneg (cutoffDerivative n x)])

lemma cut_cross_integrable (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) :=
  (((cutoff_contDiff n).continuous.mul (cutoffDerivative_continuous n)).mul
    ((u.continuous.mul v.grad_continuous).sub (u.grad_continuous.mul v.continuous))).integrable_of_hasCompactSupport
    (((cutoff_compact n).mul_right).mul_right)

lemma cut_weak_integrable {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ℝ)
    (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ (k^2-W x)*u.val x*((v.cut n).cut n).val x) :=
  ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous u.continuous |>.integrable_smul_right_of_hasCompactSupport
    ((v.cut n).cut n).continuous ((v.cut n).cut_compact n)

lemma cut_weak_zero {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) (n : ℕ) :
    (∫ x, u.grad x*((v.cut n).cut n).grad x+(k^2-W x)*u.val x*((v.cut n).cut n).val x) = 0 := by
  rw [integral_add (u.integrable_grad_mul _) (cut_weak_integrable hW k u v n),
    hu.weak_compact hW _ ((v.cut n).cut_compact n)]
  ring

lemma cut_energy_identity {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) (n : ℕ) :
    energy W (u.cut n) (v.cut n) = -k^2*inner ℝ (u.cut n) (v.cut n)+
      (∫ x, cutoffDerivative n x^2*(u.val x*v.val x))+
      (∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) := by
  let z := (v.cut n).cut n
  have hiw := cut_weak_integrable hW k u v n
  have hig := u.integrable_grad_mul z
  have hiz : Integrable (fun x ↦ u.grad x*z.grad x+(k^2-W x)*u.val x*z.val x) := hig.add hiw
  have hzero := cut_weak_zero hu hW v n
  have hpair := (u.cut n).integrable_val_mul (v.cut n)
  have hi3 := cut_error_integrable u v n
  have hic := cut_cross_integrable u v n
  rw [energy,inner_eq_integral,← integral_const_mul,
    ← integral_sub ((u.cut n).integrable_grad_mul (v.cut n)) (integrable_potential hW _ _ (v.cut_compact n))]
  calc
    _ = (∫ x, u.grad x*z.grad x+(k^2-W x)*u.val x*z.val x) +
      (∫ x, -k^2*((u.cut n).val x*(v.cut n).val x))+
      (∫ x, cutoffDerivative n x^2*(u.val x*v.val x))+
      (∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) := by
      have h1 := integral_add hiz (hpair.const_mul (-k^2))
      have h2 := integral_add (hiz.add (hpair.const_mul (-k^2))) hi3
      have h3 := integral_add ((hiz.add (hpair.const_mul (-k^2))).add hi3) hic
      simp only [Pi.add_apply] at h1 h2 h3
      rw [← h1, ← h2, ← h3]
      apply integral_congr_ae
      exact ae_of_all _ (fun x ↦ by simp only [z,cut_val,cut_grad]; exact cut_energy_algebra _ _ _ _ _ _ _ _)
    _ = _ := by rw [hzero,zero_add]

lemma cut_energy_tendsto {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) :
    Tendsto (fun n ↦ energy W (u.cut n) (v.cut n)) atTop (𝓝 (-k^2*inner ℝ u v)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffDerivative_uniform_bound
  have hd : Tendsto (fun n ↦ ∫ x, cutoffDerivative n x^2*(u.val x*v.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul] using integral_real_multiplier_tendsto (l := 0) (a := fun n x ↦ cutoffDerivative n x^2) (u.integrable_val_mul v)
      (fun n ↦ ((cutoffDerivative_continuous n).pow 2).aestronglyMeasurable)
      (D := D^2) (fun n x ↦ by
        rw [abs_pow]; nlinarith [hDb n x,abs_nonneg (cutoffDerivative n x)])
      (fun x ↦ by simpa using (cutoffDerivative_tendsto x).pow 2)
  have hc : Tendsto (fun n ↦ ∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul,Pi.sub_apply,Pi.mul_apply] using integral_real_multiplier_tendsto (l := 0) (a := fun n x ↦ cutoff n x*cutoffDerivative n x)
      ((u.val_memLp.integrable_mul v.grad_memLp).sub (u.grad_memLp.integrable_mul v.val_memLp))
      (fun n ↦ (((cutoff_contDiff n).continuous).mul (cutoffDerivative_continuous n)).aestronglyMeasurable)
      (D := D) (fun n x ↦ by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (cutoff_bound n x) (abs_nonneg _)).trans (by simpa using hDb n x))
      (fun x ↦ by simpa using (cutoff_tendsto x).mul (cutoffDerivative_tendsto x))
  simp_rw [cut_energy_identity hu hW v]
  simpa only [add_zero] using (((u.cutoff_inner_tendsto v).const_mul (-k^2)).add hd).add hc

lemma eigen_orthogonal {W : ℝ → ℝ} {k l : ℝ} {u v : C1L2}
    (hu : u.IsEigen W k) (hv : v.IsEigen W l) (hW : LocallyIntegrable W volume)
    (hkl : k^2 ≠ l^2) : inner ℝ u v = 0 := by
  have h1 := cut_energy_tendsto hu hW v
  have h2 := cut_energy_tendsto hv hW u
  have h2' : Tendsto (fun n ↦ energy W (u.cut n) (v.cut n)) atTop (𝓝 (-l^2*inner ℝ u v)) := by
    convert h2 using 1
    · ext n; exact energy_symm W _ _
    · rw [real_inner_comm v u]
  have hh := tendsto_nhds_unique h1 h2'
  exact (mul_eq_zero.mp (show (k^2-l^2)*inner ℝ u v = 0 by linarith)).resolve_left (sub_ne_zero.mpr hkl)

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.SobolevProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma h1_project_weak (u : H1) (L : ℂ →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, L (u.val x) * deriv φ x) = -(∫ x, L (u.grad x) * φ x) := by
  have hp : ContDiff ℝ ∞ (fun x ↦ (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hpc : HasCompactSupport (fun x ↦ (φ x : ℂ)) := hφc.comp_left Complex.ofReal_zero
  have hd (x : ℝ) : deriv (fun x ↦ (φ x : ℂ)) x = ((deriv φ x : ℝ) : ℂ) :=
    ((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have hi₁ : Integrable (fun x ↦ u.val x * ((deriv φ x : ℝ) : ℂ)) :=
    (u.val_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp)))
      (hφc.deriv.comp_left Complex.ofReal_zero)
  have hi₂ : Integrable (fun x ↦ u.grad x * (φ x : ℂ)) :=
    (u.grad_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hp.continuous hpc
  have he := congrArg L (u.weak_derivative _ hp hpc)
  simp only [hd,map_neg,← L.integral_comp_comm hi₁,← L.integral_comp_comm hi₂] at he
  have hm (z : ℂ) (a : ℝ) : L (z*(a : ℂ)) = L z*a := by
    rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  simpa only [hm] using he

lemma h1_continuous_representative (u : H1) :
    ∃ f : ℝ → ℂ, Continuous f ∧ u.val =ᵐ[volume] f := by
  have hr := weak_derivative_representation
    ((Complex.reCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (h1_project_weak u Complex.reCLM)
  have hi := weak_derivative_representation
    ((Complex.imCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (h1_project_weak u Complex.imCLM)
  obtain ⟨cr,hr⟩ := hr
  obtain ⟨ci,hi⟩ := hi
  let fr := fun x ↦ cr + ∫ t in (0 : ℝ)..x, (u.grad t).re
  let fi := fun x ↦ ci + ∫ t in (0 : ℝ)..x, (u.grad t).im
  have hfr : Continuous fr := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  have hfi : Continuous fi := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  refine ⟨fun x ↦ (fr x : ℂ)+(fi x : ℂ)*Complex.I,
    (Complex.continuous_ofReal.comp hfr).add ((Complex.continuous_ofReal.comp hfi).mul continuous_const),?_⟩
  filter_upwards [hr,hi] with x hx hy
  apply Complex.ext
  · simpa [fr,fi] using (show (u.val x).re = fr x from hx)
  · simpa [fr,fi] using (show (u.val x).im = fi x from hy)

lemma real_eigen_of_weak {W f g : ℝ → ℝ} {k : ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hW : LocallyIntegrable W volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x*deriv φ x) = -(∫ x, g x*φ x))
    (hwe : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, g x*deriv φ x) = -(∫ x, (k^2-W x)*f x*φ x)) :
    ∃ u : RealEigenfunction W k, f =ᵐ[volume] u.val ∧ g =ᵐ[volume] u.grad := by
  obtain ⟨c,hc⟩ := weak_derivative_representation (hf.locallyIntegrable (by norm_num))
    (hg.locallyIntegrable (by norm_num)) hw
  let F := fun x ↦ c+∫ t in (0 : ℝ)..x, g t
  have hFc : Continuous F := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable (hg.locallyIntegrable (by norm_num))) 0)
  let J := fun x ↦ (k^2-W x)*F x
  have hJ : LocallyIntegrable J volume := ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous hFc
  obtain ⟨d,hd⟩ := weak_derivative_representation (hg.locallyIntegrable (by norm_num)) hJ (fun φ hφ hφc ↦ by
    rw [hwe φ hφ hφc]; congr 1
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    rw [hx])
  let G := fun x ↦ d+∫ t in (0 : ℝ)..x, J t
  have hGc : Continuous G := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable hJ) 0)
  have hFG (x : ℝ) : F x = c+∫ t in (0 : ℝ)..x, G t := by
    change c+(∫ t in (0 : ℝ)..x, g t) = c+∫ t in (0 : ℝ)..x, G t
    congr 1
    exact intervalIntegral.integral_congr_ae (hd.mono fun _ hx _ ↦ hx)
  have hFd (x : ℝ) : HasDerivAt F (G x) x := by
    simp_rw [show F = fun x ↦ c+∫ t in (0 : ℝ)..x, G t from funext hFG]
    exact (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _) (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt).const_add c
  have hGa (a b : ℝ) : AbsolutelyContinuousOnInterval G a b := by
    have hi := locallyIntegrable_intervalIntegrable hJ (min 0 (min a b)) (max 0 (max a b))
    have h0 : (0 : ℝ) ∈ uIcc (min 0 (min a b)) (max 0 (max a b)) := by
      rw [uIcc_of_le (by exact (min_le_left _ _).trans (le_max_left _ _))]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    have h := hi.absolutelyContinuousOnInterval_intervalIntegral h0
    exact (((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ d)).contDiffOn.absolutelyContinuousOnInterval).add h).mono (by
      intro x hx
      rw [uIcc_of_le (by exact (min_le_left _ _).trans (le_max_left _ _))]
      exact ⟨(min_le_right _ _).trans hx.1,hx.2.trans (le_max_right _ _)⟩)
  have hGd : ∀ᵐ x, deriv G x = J x := by
    have hi : LocallyIntegrable J volume := hJ
    have hd' := LocallyIntegrable.ae_hasDerivAt_integral hi
    filter_upwards [hd'] with x hx
    exact ((hx 0).const_add d).deriv
  exact ⟨⟨F,G,hf.ae_eq hc,hg.ae_eq hd,hGc,hFd,hGa,hGd⟩,hc,hd⟩

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma clm_mul_real (L : ℂ →L[ℝ] ℝ) (z : ℂ) (a : ℝ) : L (z*(a : ℂ)) = L z*a := by
  rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

lemma integrable_h1_test (u : H1) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Integrable (fun x ↦ u.val x*(φ x : ℂ)) :=
  (u.val_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)

lemma integrable_potential_h1_test (u : H1) {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ (W x : ℂ)*u.val x*(φ x : ℂ)) := by
  obtain ⟨F,hF,hFe⟩ := h1_continuous_representative u
  have h := hW.integrable_smul_right_of_hasCompactSupport
    (hF.mul (Complex.continuous_ofReal.comp hφ))
    ((hφc.comp_left Complex.ofReal_zero).mul_left (f := F))
  apply h.congr
  filter_upwards [hFe] with x hx
  simp only [Complex.real_smul,hx,mul_assoc,Pi.mul_apply,Function.comp_apply]

lemma eigen_weak_second {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, u.grad x*((deriv φ x : ℝ) : ℂ)) =
      -(∫ x, ((k^2-W x : ℝ) : ℂ)*u.val x*(φ x : ℂ)) := by
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  let v := smoothH1 (fun x ↦ (φ x : ℂ)) (fun x ↦ ((deriv φ x : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (fun x ↦ (hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp)
    (Complex.continuous_ofReal.comp hφd)
    ((hφ.continuous.memLp_of_hasCompactSupport hφc).ofReal)
    ((hφd.memLp_of_hasCompactSupport hφc.deriv).ofReal)
  have he := hu.2 v
  change (∫ x, star (((deriv φ x : ℝ) : ℂ))*u.grad x) -
    (∫ x, (W x : ℂ)*star (φ x : ℂ)*u.val x) =
    -(k^2 : ℝ)*(∫ x, star (φ x : ℂ)*u.val x) at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hi := (integrable_h1_test u φ hφ.continuous hφc).const_mul ((k^2 : ℝ) : ℂ)
  have hwi := integrable_potential_h1_test u hW φ hφ.continuous hφc
  have hid : Integrable (fun x ↦ ((k^2 : ℝ) : ℂ)*u.val x*(φ x : ℂ)) := by
    simpa only [mul_assoc] using hi
  simp_rw [Complex.ofReal_sub,sub_mul]
  rw [integral_sub hid hwi]
  simp_rw [mul_assoc] at he ⊢
  rw [integral_const_mul]
  simp_rw [mul_comm (u.grad _),mul_comm (u.val _)]
  simpa only [neg_sub,sub_eq_add_neg,neg_mul,neg_add_rev,neg_neg,add_comm] using (sub_eq_iff_eq_add.mp he)

lemma eigen_project_weak_second {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, L (u.grad x)*deriv φ x) = -(∫ x, (k^2-W x)*L (u.val x)*φ x) := by
  have hi : Integrable (fun x ↦ u.grad x*((deriv φ x : ℝ) : ℂ)) :=
    (u.grad_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp)))
      (hφc.deriv.comp_left Complex.ofReal_zero)
  have hj := integrable_potential_h1_test u ((locallyIntegrable_const (c := k^2)).sub hW)
    φ hφ.continuous hφc
  change Integrable (fun x ↦ ((k^2-W x : ℝ) : ℂ)*u.val x*(φ x : ℂ)) at hj
  have he := congrArg L (eigen_weak_second hW hu φ hφ hφc)
  rw [map_neg,← L.integral_comp_comm hi,← L.integral_comp_comm hj] at he
  have hm (z : ℂ) (a : ℝ) : L ((a : ℂ)*z) = a*L z := by
    rw [mul_comm,clm_mul_real,mul_comm]
  simpa only [clm_mul_real,hm] using he

lemma eigen_project_representative {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ v : RealEigenfunction W k,
      (fun x ↦ L (u.val x)) =ᵐ[volume] v.val ∧
      (fun x ↦ L (u.grad x)) =ᵐ[volume] v.grad :=
  real_eigen_of_weak (L.comp_memLp' u.val_memLp) (L.comp_memLp' u.grad_memLp) hW
    (h1_project_weak u L) (eigen_project_weak_second hW hu L)

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set

lemma RealEigenfunction.toC1L2_eigen {W : ℝ → ℝ} {k : ℝ} (u : RealEigenfunction W k) :
    u.toC1L2.IsEigen W k := by
  intro a b
  change u.grad b-u.grad a = ∫ x in a..b, (k^2-W x)*u.val x
  rw [← (u.grad_ac a b).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [u.grad_deriv] with x hx _
  exact hx

lemma eigen_C1_representative {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ v : C1L2, v.IsEigen W k ∧ (fun x ↦ L (u.val x)) =ᵐ[volume] v.val := by
  obtain ⟨v,hv,_⟩ := eigen_project_representative hW hu L
  exact ⟨v.toC1L2,v.toC1L2_eigen,hv⟩

lemma re_l2Pairing {u v : H1} {ur ui vr vi : C1L2}
    (hur : (fun x ↦ (u.val x).re) =ᵐ[volume] ur.val)
    (hui : (fun x ↦ (u.val x).im) =ᵐ[volume] ui.val)
    (hvr : (fun x ↦ (v.val x).re) =ᵐ[volume] vr.val)
    (hvi : (fun x ↦ (v.val x).im) =ᵐ[volume] vi.val) :
    (l2Pairing u v).re = inner ℝ ur vr+inner ℝ ui vi := by
  have hint : Integrable (fun x ↦ star (u.val x)*v.val x) :=
    u.val_memLp.star.integrable_mul v.val_memLp
  have hreal := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hreal
  rw [l2Pairing,← hreal,C1L2.inner_eq_integral,C1L2.inner_eq_integral,
    ← integral_add (ur.integrable_val_mul vr) (ui.integrable_val_mul vi)]
  apply integral_congr_ae
  filter_upwards [hur,hui,hvr,hvi] with x h1 h2 h3 h4
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,h1,h2,h3,h4]
  ring

lemma im_l2Pairing {u v : H1} {ur ui vr vi : C1L2}
    (hur : (fun x ↦ (u.val x).re) =ᵐ[volume] ur.val)
    (hui : (fun x ↦ (u.val x).im) =ᵐ[volume] ui.val)
    (hvr : (fun x ↦ (v.val x).re) =ᵐ[volume] vr.val)
    (hvi : (fun x ↦ (v.val x).im) =ᵐ[volume] vi.val) :
    (l2Pairing u v).im = inner ℝ ur vi-inner ℝ ui vr := by
  have hint : Integrable (fun x ↦ star (u.val x)*v.val x) :=
    u.val_memLp.star.integrable_mul v.val_memLp
  have himag := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at himag
  rw [l2Pairing,← himag,C1L2.inner_eq_integral,C1L2.inner_eq_integral,
    ← integral_sub (ur.integrable_val_mul vi) (ui.integrable_val_mul vr)]
  apply integral_congr_ae
  filter_upwards [hur,hui,hvr,hvi] with x h1 h2 h3 h4
  simp only [Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,h1,h2,h3,h4]
  ring

end SharpLiebThirring.SobolevProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.EnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u171 u172 u173 u174 u175 u176 u177 u178


noncomputable section
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

@[simp] lemma val_sub (u v : C1L2) (x : ℝ) : (u-v).val x = u.val x-v.val x := rfl
@[simp] lemma grad_sub (u v : C1L2) (x : ℝ) : (u-v).grad x = u.grad x-v.grad x := rfl

lemma cut_tendsto (u : C1L2) : Tendsto (fun n ↦ u.cut n) atTop (𝓝 u) := by
  have h : Tendsto (fun n ↦ ∫ x, (cutoff n x-1)^2*(u.val x*u.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul] using integral_real_multiplier_tendsto (l := 0)
      (a := fun n x ↦ (cutoff n x-1)^2) (u.integrable_val_mul u)
      (fun n ↦ (((cutoff_contDiff n).continuous.sub continuous_const).pow 2).aestronglyMeasurable)
      (D := 4) (fun n x ↦ by
        rw [abs_pow]; have hb := abs_sub (cutoff n x) 1
        have hb' := cutoff_bound n x
        have hn := abs_nonneg (cutoff n x-1)
        norm_num at hb
        nlinarith)
      (fun x ↦ by simpa using ((cutoff_tendsto x).sub_const 1).pow 2)
  have heq (n : ℕ) : ‖u.cut n-u‖^2 = ∫ x, (cutoff n x-1)^2*(u.val x*u.val x) := by
    rw [← real_inner_self_eq_norm_sq,inner_eq_integral]
    apply integral_congr_ae
    exact ae_of_all _ (fun x ↦ by simp only [val_sub,cut_val]; ring)
  have hn : Tendsto (fun n ↦ ‖u.cut n-u‖) atTop (𝓝 0) := by
    have hh := h.sqrt
    simpa only [← heq,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma eventually_cut_linearIndependent {ι : Type u171} [Finite ι] {u : ι → C1L2}
    (hu : LinearIndependent ℝ u) : ∀ᶠ n in atTop, LinearIndependent ℝ (fun i ↦ (u i).cut n) :=
  (tendsto_pi_nhds.mpr (fun i ↦ (u i).cut_tendsto)).eventually hu.eventually

lemma val_sum {ι : Type u172} (s : Finset ι) (u : ι → C1L2) (x : ℝ) :
    (∑ i ∈ s, u i).val x = ∑ i ∈ s, (u i).val x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simpa only [Finset.sum_insert ha,val_add] using congrArg ((u a).val x+·) ih

lemma grad_sum {ι : Type u173} (s : Finset ι) (u : ι → C1L2) (x : ℝ) :
    (∑ i ∈ s, u i).grad x = ∑ i ∈ s, (u i).grad x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simpa only [Finset.sum_insert ha,grad_add] using congrArg ((u a).grad x+·) ih

lemma compact_smul (c : ℝ) {u : C1L2} (hu : HasCompactSupport u.val) :
    HasCompactSupport (c • u).val := hu.mul_left

lemma compact_sum {ι : Type u174} (s : Finset ι) (u : ι → C1L2)
    (hu : ∀ i ∈ s, HasCompactSupport (u i).val) : HasCompactSupport (∑ i ∈ s, u i).val := by
  classical
  convert HasCompactSupport.finset_sum hu using 1; try rfl
  funext x
  simp only [val_sum, Finset.sum_apply]

lemma compact_of_mem_span {ι : Type u175} (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) {v : C1L2}
    (hv : v ∈ Submodule.span ℝ (range u)) : HasCompactSupport v.val := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hu i
  | zero =>
      change IsCompact (tsupport (fun _ : ℝ ↦ (0 : ℝ)))
      simp
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact compact_smul c hx

lemma energy_add_left {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (u v w : C1L2) (hw : HasCompactSupport w.val) :
    energy W (u+v) w = energy W u w+energy W v w := by
  simp only [energy,grad_add,val_add,add_mul,mul_add]
  rw [integral_add (u.integrable_grad_mul w) (v.integrable_grad_mul w),
    integral_add (integrable_potential hW u w hw) (integrable_potential hW v w hw)]
  ring

lemma energy_smul_left (W : ℝ → ℝ) (c : ℝ) (u v : C1L2) :
    energy W (c • u) v = c*energy W u v := by
  simp only [energy,grad_smul,val_smul]
  simp_rw [show ∀ x, c*u.grad x*v.grad x = c*(u.grad x*v.grad x) by intros; ring,
    show ∀ x, W x*(c*u.val x)*v.val x = c*(W x*u.val x*v.val x) by intros; ring]
  rw [integral_const_mul,integral_const_mul]; ring

lemma energy_sum_left {ι : Type u176} {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (s : Finset ι) (u : ι → C1L2) (v : C1L2) (hv : HasCompactSupport v.val) :
    energy W (∑ i ∈ s, u i) v = ∑ i ∈ s, energy W (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy]
  | insert a s ha ih => rw [Finset.sum_insert ha,energy_add_left hW _ _ _ hv,ih,Finset.sum_insert ha]

lemma energy_sum_sum {ι : Type u177} [Fintype ι] {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) (c : ι → ℝ) :
    energy W (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i*c j*energy W (u i) (u j) := by
  classical
  rw [energy_sum_left hW _ _ _ (compact_sum _ _ (fun i _ ↦ compact_smul _ (hu i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [energy_symm,energy_sum_left hW _ _ _ (compact_smul _ (hu i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [energy_smul_left,energy_symm,energy_smul_left]
  ring

lemma inner_sum_sum {ι : Type u178} [Fintype ι] (u : ι → C1L2) (c : ι → ℝ) :
    inner ℝ (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i*c j*inner ℝ (u i) (u j) := by
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (u j) (u i)]

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlagApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Filter InnerProductSpace
open scoped Topology

lemma eventually_cut_prefix_negative {N : ℕ} {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : Fin N → C1L2) (k κ : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (hκ : ∀ i, 0 < κ i ∧ κ i < k i)
    (horder : Antitone k) :
    ∀ᶠ n in atTop, ∀ i (v : C1L2),
      v ∈ Submodule.span ℝ ((fun j ↦ (u j).cut n) '' Iic i) →
      energy W v v+κ i^2*inner ℝ v v ≤ 0 := by
  classical
  apply eventually_all.mpr
  intro i
  let d : Iic i → ℝ := fun j ↦ κ i^2-k j^2
  have hd (j : Iic i) : d j < 0 := by
    have hj := horder j.property
    have hki := hk i
    have hkj := hk j
    have hκi := hκ i
    dsimp [d]; nlinarith
  let M := fun n (j l : Iic i) ↦ energy W ((u j).cut n) ((u l).cut n)+
    κ i^2*inner ℝ ((u j).cut n) ((u l).cut n)
  have hM (j l : Iic i) : Tendsto (fun n ↦ M n j l) atTop (𝓝 (if j=l then d j else 0)) := by
    have hh := (cut_energy_tendsto (he j) hW (u l)).add (((u j).cutoff_inner_tendsto (u l)).const_mul (κ i^2))
    convert hh using 1
    rw [orthonormal_iff_ite.mp ho]
    by_cases hjl : j=l
    · simp [hjl,d]; ring
    · have hn : (j : Fin N) ≠ l := fun h ↦ hjl (Subtype.ext h)
      simp [hjl,hn]
  filter_upwards [eventually_negative_quadratic M d hd hM] with n hn v hv
  have him : ((fun j ↦ (u j).cut n) '' Iic i) = range (fun j : Iic i ↦ (u j).cut n) := by
    ext x
    simp
  rw [him,Submodule.mem_span_range_iff_exists_fun ℝ] at hv
  obtain ⟨c,rfl⟩ := hv
  rw [energy_sum_sum hW (fun j : Iic i ↦ (u j).cut n) (fun j ↦ (u j).cut_compact n),inner_sum_sum]
  convert hn c using 1
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,M]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- A compact orthonormal flag with the exact strict spectral margins. -/
lemma exists_compact_negative_flag {N : ℕ} {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : Fin N → C1L2) (k κ : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (hκ : ∀ i, 0 < κ i ∧ κ i < k i)
    (horder : Antitone k) :
    ∃ q : Fin N → C1L2, Orthonormal ℝ q ∧
      (∀ i, HasCompactSupport (q i).val) ∧
      ∀ i (v : C1L2), v ∈ Submodule.span ℝ (q '' Iic i) →
        energy W v v+κ i^2*inner ℝ v v ≤ 0 := by
  classical
  obtain ⟨n,hli,hn⟩ := ((eventually_cut_linearIndependent ho.linearIndependent).and
    (eventually_cut_prefix_negative hW u k κ ho he hk hκ horder)).exists
  let f := fun j ↦ (u j).cut n
  let q := gramSchmidtNormed ℝ f
  have hs (i : Fin N) : Submodule.span ℝ (q '' Iic i) = Submodule.span ℝ (f '' Iic i) := by
    rw [show q = gramSchmidtNormed ℝ f from rfl,span_gramSchmidtNormed,span_gramSchmidt_Iic]
  refine ⟨q,gramSchmidtNormed_orthonormal hli,?_,?_⟩
  · intro i
    apply compact_of_mem_span f (fun j ↦ (u j).cut_compact n)
    apply Submodule.span_mono (image_subset_range _ _)
    rw [← hs i]
    exact Submodule.subset_span (mem_image_of_mem q (mem_Iic.mpr le_rfl))
  · intro i v hv
    rw [hs i] at hv
    exact hn i v hv

end SharpLiebThirring.SpectralProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.SpectralTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u179


noncomputable section
namespace SharpLiebThirring.SpectralProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set ContinuationGap ActionProof
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma triangular_action_upper {σ l r : ℝ} (hσ : 0 < σ) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    {W : ℝ → ℝ} (hW : IntervalIntegrable W volume l r)
    (hWn : ∀ᵐ x ∂volume, 0 ≤ W x)
    (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (he : (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) ≤
      ∫ t in l..r, W t*(∑ i, a t i^2)) :
    (∫ t in l..r, actionDensity σ k (a t) (v t)) ≤
      actionYoungConstant σ * ∫ t, W t^(1+σ) := by
  let m := fun t ↦ ∑ i, a t i^2
  have hm : ContinuousOn m (Icc l r) := continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp ha i).pow 2)
  have hm0 (t : ℝ) : 0 ≤ m t := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmr : ContinuousOn (fun t ↦ m t^(1+1/σ)) (Icc l r) :=
    hm.rpow_const (fun _ _ ↦ Or.inr (by positivity))
  have hE : ContinuousOn (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) (Icc l r) :=
    (continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp hv i).pow 2)).add
      (continuousOn_finsetSum Finset.univ (fun i _ ↦ ((continuousOn_pi.mp ha i).pow 2).const_mul _))
  have hEi : IntervalIntegrable (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) volume l r := hE.intervalIntegrable_of_Icc hlr
  have hmri : IntervalIntegrable (fun t ↦ m t^(1+1/σ)) volume l r := hmr.intervalIntegrable_of_Icc hlr
  have hWmi : IntervalIntegrable (fun t ↦ W t*m t) volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlr] at hW ⊢
    exact hW.mul_continuousOn hm isCompact_Icc
  have hAi : IntervalIntegrable (fun t ↦ actionYoungConstant σ * W t^(1+σ)) volume l r := hWp.intervalIntegrable.const_mul (actionYoungConstant σ)
  calc
    (∫ t in l..r, actionDensity σ k (a t) (v t)) =
        (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) -
          ∫ t in l..r, m t^(1+1/σ) := intervalIntegral.integral_sub hEi hmri
    _ ≤ (∫ t in l..r, W t*m t) - ∫ t in l..r, m t^(1+1/σ) := sub_le_sub_right he _
    _ = ∫ t in l..r, W t*m t-m t^(1+1/σ) :=
      (intervalIntegral.integral_sub hWmi hmri).symm
    _ ≤ ∫ t in l..r, actionYoungConstant σ * W t^(1+σ) := by
      apply intervalIntegral.integral_mono_ae_restrict hlr (hWmi.sub hmri) hAi
      filter_upwards [ae_restrict_of_ae hWn] with t ht
      exact young_action_bound hσ ht (hm0 t)
    _ = actionYoungConstant σ * ∫ t in l..r, W t^(1+σ) := intervalIntegral.integral_const_mul _ _
    _ ≤ actionYoungConstant σ * ∫ t, W t^(1+σ) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold actionYoungConstant; positivity)
      rw [intervalIntegral.integral_of_le hlr]
      exact integral_mono_measure Measure.restrict_le_self
        (hWn.mono fun x hx ↦ Real.rpow_nonneg hx _) hWp

lemma finite_spectral_trial {σ l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    {W : ℝ → ℝ} (hW : IntervalIntegrable W volume l r)
    (hWn : ∀ᵐ x ∂volume, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (he : ∀ C : LowerSpace N,
      (∫ t in l..r, (∑ i, (C.val *ᵥ v t) i^2)+(∑ i, k i^2*(C.val *ᵥ u t) i^2)) ≤
        ∫ t in l..r, W t*(∑ i, (C.val *ᵥ u t) i^2)) :
    (∑ i, ∫ s in -(k i)..k i, (k i^2-s^2)^σ) ≤
      actionYoungConstant σ * ∫ t, W t^(1+σ) := by
  apply finite_action_upper_test hσ₀ hσ₁ hlr k hk u v hu hv hud hul hur ho
  intro C
  exact triangular_action_upper hσ₀ hlr k _ _
    ((show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hu)
    ((show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hv)
    hW hWn hWp (he C)

end SharpLiebThirring.SpectralProof

end


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Filter Matrix MatrixProof ContinuationGap
open scoped Topology Matrix.Norms.L2Operator

lemma compact_family_radius {ι : Type u179} [Fintype ι] (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) :
    ∃ R : ℝ, 0 < R ∧ ∀ i x, R ≤ |x| → (u i).val x = 0 ∧ (u i).grad x = 0 := by
  have hc : IsCompact (⋃ i, tsupport (u i).val) := isCompact_iUnion hu
  obtain ⟨R,hR,hs⟩ := hc.isBounded.subset_ball_lt 0 0
  refine ⟨R,hR,fun i x hx ↦ ?_⟩
  have hn : x ∉ tsupport (u i).val := by
    intro hm
    have hxb := hs (mem_iUnion.2 ⟨i,hm⟩)
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] at hxb
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hn,?_⟩
  rw [← deriv_val]
  apply Function.notMem_support.mp
  exact fun hd ↦ hn (support_deriv_subset hd)

lemma integral_eq_interval_of_vanish {R : ℝ} (_hR : 0 ≤ R) {f : ℝ → ℝ}
    (hf : ∀ x, R ≤ |x| → f x = 0) : (∫ x, f x) = ∫ x in -R..R, f x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hn : |x| < R := lt_of_not_ge (fun h ↦ hx (hf x h))
  exact ⟨by rw [abs_lt] at hn; linarith [hn.1],by rw [abs_lt] at hn; linarith [hn.2]⟩

lemma row_mem_prefix {N : ℕ} (q : Fin N → C1L2) (C : LowerSpace N) (i : Fin N) :
    (∑ j, C.val i j • q j) ∈ Submodule.span ℝ (q '' Iic i) := by
  classical
  apply Submodule.sum_mem
  intro j _
  by_cases hj : j ≤ i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_image_of_mem q (mem_Iic.mpr hj)))
  · rw [C.property i j (lt_of_not_ge hj),zero_smul]
    exact Submodule.zero_mem _

lemma compact_trial_energy {N : ℕ} {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (κ : Fin N → ℝ) (p : Fin N → C1L2) (hp : ∀ i, HasCompactSupport (p i).val)
    (he : ∀ i, energy W (p i) (p i)+κ i^2*inner ℝ (p i) (p i) ≤ 0) :
    (∫ x, (∑ i, (p i).grad x^2)+(∑ i, κ i^2*(p i).val x^2)) ≤
      ∫ x, W x*(∑ i, (p i).val x^2) := by
  have hgi (i : Fin N) : Integrable (fun x ↦ (p i).grad x^2) := by
    simpa only [pow_two] using (p i).integrable_grad_mul (p i)
  have hvi (i : Fin N) : Integrable (fun x ↦ κ i^2*(p i).val x^2) := by
    simpa only [pow_two] using ((p i).integrable_val_mul (p i)).const_mul (κ i*κ i)
  have hwi (i : Fin N) : Integrable (fun x ↦ W x*(p i).val x^2) := by
    simpa only [pow_two,mul_assoc] using integrable_potential hW (p i) (p i) (hp i)
  rw [integral_add (integrable_finsetSum _ (fun i _ ↦ hgi i))
    (integrable_finsetSum _ (fun i _ ↦ hvi i)),integral_finsetSum _ (fun i _ ↦ hgi i),
    integral_finsetSum _ (fun i _ ↦ hvi i)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hwi i),← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh := he i
  simp only [energy,inner_eq_integral,mul_assoc,← pow_two] at hh
  rw [integral_const_mul]
  linarith

lemma compact_trial_bound {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    (q : Fin N → C1L2) (ho : Orthonormal ℝ q)
    (hc : ∀ i, HasCompactSupport (q i).val)
    (he : ∀ i (v : C1L2), v ∈ Submodule.span ℝ (q '' Iic i) →
      energy W v v+κ i^2*inner ℝ v v ≤ 0) :
    (∑ i, ∫ s in -(κ i)..κ i, (κ i^2-s^2)^σ) ≤
      actionYoungConstant σ * ∫ x, W x^(1+σ) := by
  classical
  obtain ⟨R,hR,hvan⟩ := compact_family_radius q hc
  apply finite_spectral_trial hσ₀ hσ₁ (l := -R) (r := R) (by linarith) κ hκ
    (fun x i ↦ (q i).val x) (fun x i ↦ (q i).grad x)
    ((continuous_pi (fun i ↦ (q i).continuous)).continuousOn)
    ((continuous_pi (fun i ↦ (q i).grad_continuous)).continuousOn)
    (fun x _ i ↦ (q i).hasDerivAt x)
  · ext i; exact (hvan i (-R) (by simp [abs_of_pos hR])).1
  · ext i; exact (hvan i R (by simp [abs_of_pos hR])).1
  · intro i j
    rw [← integral_eq_interval_of_vanish hR.le (fun x hx ↦ by rw [(hvan i x hx).1,zero_mul]),
      ← inner_eq_integral]
    exact orthonormal_iff_ite.mp ho i j
  · exact locallyIntegrable_intervalIntegrable hW _ _
  · exact hWn
  · exact hWp
  · intro C
    let p := fun i ↦ ∑ j, C.val i j • q j
    have hp (i : Fin N) : HasCompactSupport (p i).val :=
      compact_sum _ _ (fun j _ ↦ compact_smul _ (hc j))
    have hpv (i : Fin N) (x : ℝ) : (p i).val x = (C.val *ᵥ (fun j ↦ (q j).val x)) i := by
      simp only [p,val_sum,val_smul,mulVec,dotProduct]
    have hpg (i : Fin N) (x : ℝ) : (p i).grad x = (C.val *ᵥ (fun j ↦ (q j).grad x)) i := by
      simp only [p,grad_sum,grad_smul,mulVec,dotProduct]
    have he' := compact_trial_energy hW κ p hp (fun i ↦ he i (p i) (row_mem_prefix q C i))
    have hz (i : Fin N) (x : ℝ) (hx : R ≤ |x|) : (p i).val x = 0 ∧ (p i).grad x = 0 := by
      constructor <;> simp only [p,val_sum,grad_sum,val_smul,grad_smul] <;>
        apply Finset.sum_eq_zero <;> intro j _ <;> simp [(hvan j x hx).1,(hvan j x hx).2]
    rw [integral_eq_interval_of_vanish hR.le (fun x hx ↦ by simp [(fun i ↦ (hz i x hx).1),(fun i ↦ (hz i x hx).2)]),
      integral_eq_interval_of_vanish hR.le (fun x hx ↦ by simp [(fun i ↦ (hz i x hx).1)])] at he'
    simpa only [hpv,hpg] using he'

end SharpLiebThirring.SpectralProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ComplexFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u180


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 ConstantProof MeasureTheory Set Filter
open scoped Topology

lemma real_family_bound_sorted {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (u : Fin N → C1L2) (k : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (horder : Antitone k) :
    (∑ i, k i^(1+2*σ))*betaAction σ ≤ actionYoungConstant σ*∫ x, W x^(1+σ) := by
  have hc : ContinuousAt (fun t : ℝ ↦ ∑ i, (t*k i)^(1+2*σ)*betaAction σ) 1 := by
    apply tendsto_finsetSum
    intro i _
    exact (((continuousAt_id.mul_const (k i)).rpow_const
      (Or.inl (by simpa using (hk i).ne'))).mul_const _)
  have ht : Tendsto (fun t : ℝ ↦ ∑ i, (t*k i)^(1+2*σ)*betaAction σ) (𝓝[<] 1)
      (𝓝 ((∑ i, k i^(1+2*σ))*betaAction σ)) := by
    simpa only [one_mul,Finset.sum_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht0
  have hκ (i : Fin N) : 0 < t*k i ∧ t*k i < k i :=
    ⟨mul_pos ht0 (hk i),by simpa using mul_lt_mul_of_pos_right (show t < 1 from ht) (hk i)⟩
  obtain ⟨q,hqo,hqc,hqe⟩ := exists_compact_negative_flag hW u k (fun i ↦ t*k i)
    ho he hk hκ horder
  have h := compact_trial_bound hσ₀ hσ₁ hW hWn hWp (fun i ↦ t*k i)
    (fun i ↦ (hκ i).1) q hqo hqc hqe
  simpa only [boundary_action_scaling hσ₀ (hκ _).1] using h

lemma real_family_action_bound {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (u : Fin N → C1L2) (k : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) :
    (∑ i, k i^(1+2*σ))*betaAction σ ≤ actionYoungConstant σ*∫ x, W x^(1+σ) := by
  let e := Tuple.sort (fun i ↦ -k i)
  have horder : Antitone (fun i ↦ k (e i)) := by
    intro i j hij
    have h := Tuple.monotone_sort (fun i ↦ -k i) hij
    dsimp at h
    linarith
  have h := real_family_bound_sorted hσ₀ hσ₁ hW hWn hWp
    (fun i ↦ u (e i)) (fun i ↦ k (e i)) (ho.comp e e.injective)
    (fun i ↦ he (e i)) (fun i ↦ hk (e i)) horder
  simpa only [Equiv.sum_comp e (fun i ↦ k i^(1+2*σ))] using h

lemma action_constant_eq_sharp {σ : ℝ} (hσ : 0 < σ) :
    actionYoungConstant σ / betaAction σ = sharpConstant (σ+1/2) := by
  rw [actionYoungConstant,young_over_beta hσ,sharpConstant,semiclassicalConstant]
  have h1 : σ+1/2-1/2 = σ := by ring
  have h2 : σ+1/2+1/2 = σ+1 := by ring
  have h3 : σ+1/2+1 = σ+3/2 := by ring
  have h4 : σ+1/2+3/2 = σ+2 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma real_family_bound {ι : Type u180} [Fintype ι] {γ : ℝ}
    (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (hWn : ∀ᵐ x, 0 ≤ W x)
    (hWp : Integrable (fun x ↦ W x^(γ+1/2)))
    (u : ι → C1L2) (k : ι → ℝ) (ho : Orthonormal ℝ u)
    (he : ∀ i, (u i).IsEigen W (k i)) (hk : ∀ i, 0 < k i) :
    (∑ i, k i^(2*γ)) ≤ sharpConstant γ*∫ x, W x^(γ+1/2) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hσ₀ : 0 < γ-1/2 := by linarith
  have hσ₁ : γ-1/2 < 1 := by linarith
  have he2 : 1+(γ-1/2) = γ+1/2 := by ring
  have h := real_family_action_bound hσ₀ hσ₁ hW hWn
    (by simpa only [he2] using hWp)
    (fun i ↦ u (e i)) (fun i ↦ k (e i)) (ho.comp e e.injective)
    (fun i ↦ he (e i)) (fun i ↦ hk (e i))
  rw [Equiv.sum_comp e (fun i ↦ k i^(1+2*(γ-1/2)))] at h
  have he1 : 1+2*(γ-1/2) = 2*γ := by ring
  rw [he1,he2] at h
  have hh := (le_div_iff₀ (betaAction_pos hσ₀)).mpr h
  rw [mul_div_right_comm,action_constant_eq_sharp hσ₀,sub_add_cancel] at hh
  exact hh

end SharpLiebThirring.SpectralProof

end


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Module

/-- Finite realification, retaining all complex multiplicities at each energy. -/
lemma realify_finite_family {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ι → ℝ)
    (hk : ∀ i, 0 < k i) (a b : ι → C1L2)
    (ha : ∀ i, (a i).IsEigen W (k i)) (hb : ∀ i, (b i).IsEigen W (k i))
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0)
    (p : ℝ) :
    ∃ (J : Type) (_ : Fintype J) (v : J → C1L2) (l : J → ℝ),
      Orthonormal ℝ v ∧ (∀ j, (v j).IsEigen W (l j)) ∧ (∀ j, 0 < l j) ∧
      (∑ i, k i^p) ≤ ∑ j, l j^p := by
  classical
  let T := range k
  let : Fintype T := (finite_range k).fintype
  let I := fun t : T ↦ {i : ι // k i = t.val}
  let g := fun (t : T) (z : I t × Bool) ↦ if z.2 then b z.1 else a z.1
  let E := fun t : T ↦ Submodule.span ℝ (range (g t))
  have (t : T) : FiniteDimensional ℝ (E t) := FiniteDimensional.span_of_finite ℝ (finite_range _)
  have hE (t : T) : E t ≤ eigenSubmodule hW t.val := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨i,c⟩,rfl⟩
    change (if c then b i else a i).IsEigen W t.val
    cases c
    · simpa only [i.property,Bool.false_eq_true,ite_false] using ha i
    · simpa only [i.property,ite_true] using hb i
  let ar := fun (t : T) (i : I t) ↦ (⟨a i,Submodule.subset_span (mem_range.mpr ⟨(i,false),rfl⟩)⟩ : E t)
  let br := fun (t : T) (i : I t) ↦ (⟨b i,Submodule.subset_span (mem_range.mpr ⟨(i,true),rfl⟩)⟩ : E t)
  have hdim (t : T) : Fintype.card (I t) ≤ finrank ℝ (E t) := by
    apply complex_family_card_le_real_dimension (ar t) (br t)
    · intro i j
      change inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = _
      rw [hr]
      congr 1
      exact propext Subtype.ext_iff.symm
    · intro i j
      exact hi i j
  let B := fun t : T ↦ stdOrthonormalBasis ℝ (E t)
  let J := (t : T) × Fin (finrank ℝ (E t))
  let v : J → C1L2 := fun z ↦ (B z.1 z.2).val
  let l : J → ℝ := fun z ↦ z.1.val
  have hl (t : T) : 0 < t.val := by obtain ⟨i,he⟩ := t.property; rw [← he]; exact hk i
  have hv (j : J) : (v j).IsEigen W (l j) := hE j.1 (B j.1 j.2).property
  refine ⟨J,inferInstance,v,l,?_,hv,fun j ↦ hl j.1,?_⟩
  · rw [orthonormal_iff_ite]
    rintro ⟨t,i⟩ ⟨s,j⟩
    by_cases hts : t=s
    · subst s
      have hh := (B t).orthonormal
      have heq := orthonormal_iff_ite.mp hh i j
      change inner ℝ (B t i) (B t j) = _
      rw [heq]
      congr 1
      apply propext
      constructor
      · intro h; subst j; rfl
      · intro h
        exact eq_of_heq (Sigma.mk.inj h).2
    · have hneq : t.val^2 ≠ s.val^2 := by
        intro he
        have hval : t.val = s.val := by nlinarith [hl t,hl s]
        exact hts (Subtype.ext hval)
      rw [eigen_orthogonal (hv ⟨t,i⟩) (hv ⟨s,j⟩) hW hneq,ite_eq_right]
      exact fun h ↦ hts (congrArg Sigma.fst h)
  · have heq : (∑ i, k i^p) = ∑ t : T, (Fintype.card (I t) : ℝ)*t.val^p := by
      let f : ι ≃ (t : T) × I t :=
        { toFun := fun i ↦ ⟨⟨k i,mem_range_self i⟩,⟨i,rfl⟩⟩
          invFun := fun z ↦ z.2.val
          left_inv := fun _ ↦ rfl
          right_inv := by rintro ⟨⟨t,ht⟩,⟨i,hi⟩⟩; dsimp at hi; subst t; rfl }
      calc
        (∑ i, k i^p) = ∑ z : (t : T) × I t, z.1.val^p :=
          Equiv.sum_comp f (fun z ↦ z.1.val^p)
        _ = _ := by
          rw [Fintype.sum_sigma]
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [heq,Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro t _
    simp only [l,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdim t) (Real.rpow_nonneg (hl t).le _)

end SharpLiebThirring.SpectralProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set
open SobolevProof SobolevProof.C1L2 SpectralProof ConstantProof

lemma Admissible.locallyIntegrable {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : LocallyIntegrable W volume := by
  apply hW.2.locallyIntegrable
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma Admissible.integrable_rpow {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    Integrable (fun x ↦ W x^(γ+1/2)) := by
  have hp : 0 < γ+1/2 := by linarith
  have hh := hW.2.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hh
  apply hh.congr
  filter_upwards [hW.1] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg hx]

lemma Admissible.mass_eq_ofReal {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    potentialMass γ W = ENNReal.ofReal (∫ x, W x^(γ+1/2)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hW.integrable_rpow hγ)]
  · apply lintegral_congr_ae
    filter_upwards [hW.1] with x hx
    exact ENNReal.ofReal_rpow_of_nonneg hx (by linarith)
  · filter_upwards [hW.1] with x hx
    exact Real.rpow_nonneg hx _

lemma Admissible.mass_ne_top {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : potentialMass γ W ≠ ⊤ := by
  rw [hW.mass_eq_ofReal hγ]
  exact ENNReal.ofReal_ne_top

lemma sharpConstant_pos {γ : ℝ} (hγ : 1/2 < γ) : 0 < sharpConstant γ := by
  have hσ : 0 < γ-1/2 := by linarith
  have he := action_constant_eq_sharp hσ
  rw [sub_add_cancel] at he
  rw [← he]
  apply div_pos _ (betaAction_pos hσ)
  unfold actionYoungConstant
  positivity

lemma finite_complex_eigenfamily_bound {N : ℕ} {γ : ℝ}
    (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) {W : ℝ → ℝ}
    (hW : Admissible γ W) (u : Fin N → H1) (k : Fin N → ℝ)
    (ho : IsOrthonormalFamily u) (he : ∀ i, IsNegativeEigenfunction W (k i) (u i)) :
    (∑ i, k i^(2*γ)) ≤ sharpConstant γ*∫ x, W x^(γ+1/2) := by
  have hWl := hW.locallyIntegrable hγ₀
  choose a ha har using (fun i ↦ eigen_C1_representative hWl (he i) Complex.reCLM)
  choose b hb hbi using (fun i ↦ eigen_C1_representative hWl (he i) Complex.imCLM)
  have hr (i j : Fin N) : inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0 := by
    have hh := congrArg Complex.re (ho i j)
    rw [re_l2Pairing (har i) (hbi i) (har j) (hbi j)] at hh
    simpa only [apply_ite,Complex.one_re,Complex.zero_re] using hh
  have hi (i j : Fin N) : inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0 := by
    have hh := congrArg Complex.im (ho i j)
    rw [im_l2Pairing (har i) (hbi i) (har j) (hbi j)] at hh
    simpa only [apply_ite,Complex.one_im,Complex.zero_im,ite_self] using hh
  obtain ⟨J,hJ,v,l,hvo,hve,hl,hs⟩ := realify_finite_family hWl k (fun i ↦ (he i).1) a b ha hb hr hi (2*γ)
  let := hJ
  exact hs.trans (real_family_bound hγ₀ hγ₁ hWl hW.1 (hW.integrable_rpow hγ₀) v l hvo hve hl)

/-- The full (unlimited-family-size) negative spectral moment estimate. -/
lemma negativeMoment_bound {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) :
    negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W := by
  unfold negativeMoment
  refine iSup_le (fun N ↦ iSup_le (fun u ↦ iSup_le (fun k ↦ iSup_le (fun ho ↦ iSup_le (fun he ↦ ?_)))))
  have hh := ENNReal.ofReal_le_ofReal (finite_complex_eigenfamily_bound hγ₀ hγ₁ hW u k ho he)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Real.rpow_nonneg (he i).1.le _),
    ENNReal.ofReal_mul (sharpConstant_pos hγ₀).le,← hW.mass_eq_ofReal hγ₀] at hh
  simpa only [ENNReal.ofReal_rpow_of_nonneg (he _).1.le (show 0 ≤ 2*γ by linarith)] using hh

end SharpLiebThirring

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ExtremizerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.ExtremizerProof
open ConstantProof SpectralProof MeasureTheory Set

/-- Exact substitution `z = tanh (r*x)`; no integrability convention is used to
    guess the integral, since the Jacobian theorem applies to the full line. -/
lemma potential_power_integral {r σ : ℝ} (hr : 0 < r) :
    (∫ x, (potential r x)^(1+σ)) = (r+1)^(1+σ)/r * betaAction σ := by
  let f : ℝ → ℝ := fun x ↦ Real.tanh (r*x)
  have hf' (x : ℝ) : HasDerivAt f ((Real.cosh (r*x))⁻¹^2*r) x := by
    convert! (tanh_hasDerivAt (r*x)).comp x ((hasDerivAt_id x).const_mul r) using 1
    simp
  have hinj : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ hr.ne' (Real.tanh_injective h)
  have himg : f '' univ = Ioo (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
    · intro hz
      obtain ⟨x,_,hx⟩ := Real.tanh_surjOn hz
      refine ⟨x/r,mem_univ _,?_⟩
      dsimp [f]
      rw [mul_div_cancel₀ _ hr.ne',hx]
  have hj := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hf' x).hasDerivWithinAt) hinj.injOn (fun z : ℝ ↦ (1-z^2)^σ)
  rw [himg,setIntegral_univ] at hj
  have halg (x : ℝ) : |(Real.cosh (r*x))⁻¹^2*r| * (1-f x^2)^σ =
      r*((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    have hs : 0 < (Real.cosh (r*x))⁻¹^2 := by positivity
    have ht : 1-f x^2 = (Real.cosh (r*x))⁻¹^2 := by
      dsimp [f]
      linarith [tanh_sq_add_sech_sq (r*x)]
    rw [abs_of_pos (mul_pos hs hr),ht,Real.rpow_add hs,Real.rpow_one]
    ring
  have hj' : betaAction σ = r*∫ x, ((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    rw [betaAction,intervalIntegral.integral_of_le (by norm_num),integral_Ioc_eq_integral_Ioo,hj]
    simp only [smul_eq_mul,halg]
    exact integral_const_mul _ _
  have hi : (∫ x, (potential r x)^(1+σ)) =
      (r+1)^(1+σ)*∫ x, ((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      dsimp only [potential]
      rw [Real.mul_rpow (by linarith : 0 ≤ r+1) (sq_nonneg _)])
  rw [hi,hj']
  field_simp

lemma young_times_extremizer_factor {σ : ℝ} (hσ : 0 < σ) :
    actionYoungConstant σ * ((σ⁻¹+1)^(1+σ)/σ⁻¹) = 1 := by
  have hp : 0 < 1+σ := by linarith
  have he : σ⁻¹+1 = (1+σ)/σ := by field_simp
  rw [actionYoungConstant,he,Real.div_rpow hp.le hσ.le]
  rw [Real.rpow_add hσ,Real.rpow_one]
  have hn : (1+σ)^(1+σ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hn' : σ^σ ≠ 0 := (Real.rpow_pos_of_pos hσ _).ne'
  field_simp

lemma sharp_times_extremizer_integral {γ : ℝ} (hγ : 1/2 < γ) :
    sharpConstant γ * (∫ x, (equalityPotential γ x)^(γ+1/2)) = 1 := by
  have hσ : 0 < γ-1/2 := by linarith
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr hσ
  have hpow : γ+1/2 = 1+(γ-1/2) := by ring
  change sharpConstant γ * (∫ x, (potential ((γ-1/2)⁻¹) x)^(γ+1/2)) = 1
  rw [hpow,potential_power_integral hr]
  have hc := action_constant_eq_sharp hσ
  rw [sub_add_cancel] at hc
  rw [← hc]
  calc
    _ = actionYoungConstant (γ-1/2)*(((γ-1/2)⁻¹+1)^(1+(γ-1/2))/(γ-1/2)⁻¹) := by
      rw [mul_comm _ (betaAction (γ-1/2)),← mul_assoc,div_mul_cancel₀ _ (betaAction_pos hσ).ne']
    _ = 1 := young_times_extremizer_factor hσ

end SharpLiebThirring.ExtremizerProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set ExtremizerProof

lemma sharp_times_extremizer_mass {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ)*potentialMass γ (equalityPotential γ) = 1 := by
  rw [(equalityPotential_admissible hγ).mass_eq_ofReal hγ,
    ← ENNReal.ofReal_mul (sharpConstant_pos hγ).le,
    sharp_times_extremizer_integral hγ,ENNReal.ofReal_one]

lemma optimalConstant_le_sharp {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) :
    optimalConstant γ ≤ ENNReal.ofReal (sharpConstant γ) := by
  unfold optimalConstant
  refine iSup_le (fun W ↦ iSup_le (fun hW ↦ iSup_le (fun _ ↦ ?_)))
  exact ENNReal.div_le_of_le_mul (negativeMoment_bound hγ₀ hγ₁ hW)

lemma sharp_le_oneStateConstant {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ) ≤ oneStateConstant γ := by
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr (by linarith)
  have hW := equalityPotential_admissible hγ
  have hpos : 0 < potentialMass γ (equalityPotential γ) := potential_mass_pos hr
  have hle : ENNReal.ofReal (sharpConstant γ) ≤
      oneStateMoment γ (equalityPotential γ) / potentialMass γ (equalityPotential γ) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl (hW.mass_ne_top hγ))).mpr
    rw [sharp_times_extremizer_mass hγ]
    exact one_le_oneStateMoment hr γ
  unfold oneStateConstant
  exact hle.trans (le_iSup_of_le (equalityPotential γ)
    (le_iSup_of_le hW (le_iSup_of_le hpos le_rfl)))

/-- Full sharp Lieb–Thirring bound, both optimal constants, and equality at the
explicit potential; no finite spectral cutoff is imposed. -/
theorem sharp_lieb_thirring_oai : MainClaim := by
  intro γ hγ₀ hγ₁
  have hupper := optimalConstant_le_sharp hγ₀ hγ₁
  have hlower := sharp_le_oneStateConstant hγ₀
  have hone := oneStateConstant_le_optimalConstant γ
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr (by linarith)
  have hW := equalityPotential_admissible hγ₀
  refine ⟨fun _ hW ↦ negativeMoment_bound hγ₀ hγ₁ hW,
    le_antisymm hupper (hlower.trans hone),le_antisymm (hone.trans hupper) hlower,
    hW,potential_mass_pos hr,?_⟩
  apply le_antisymm (negativeMoment_bound hγ₀ hγ₁ hW)
  rw [sharp_times_extremizer_mass hγ₀]
  exact one_le_negativeMoment hr γ

end SharpLiebThirring

end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.sharp_lieb_thirring_oai := @OAI.SharpLiebThirring.sharp_lieb_thirring_oai
