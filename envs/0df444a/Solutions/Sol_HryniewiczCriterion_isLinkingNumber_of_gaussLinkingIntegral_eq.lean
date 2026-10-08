-- Prove2me | solution 1 for HryniewiczCriterion.isLinkingNumber_of_gaussLinkingIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T21:07:34.6524+00:00
-- url     : https://prove2.me/submissions/2189f754-d130-4adb-a7fd-2cde133d68ff

import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open HryniewiczCriterion
open scoped ContDiff
open MeasureTheory Set

/-!
# Algebra and pointwise calculus for the Gauss linking integrand

`volumeIn N a b c = det(-N, a, b, c)` is written out explicitly. The key algebraic fact is
the Cramer identity for `u ⊥ N`:
`⟨u,a⟩ V(u,b,c) + ⟨u,b⟩ V(a,u,c) + ⟨u,c⟩ V(a,b,u) = |u|² V(a,b,c)`,
which makes the Gauss 2-form closed.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The explicit `4 × 4` determinant with rows `x, y, z, w`. -/
def gl_det4 (x y z w : R4) : ℝ :=
  x 0 * y 1 * z 2 * w 3 - x 0 * y 1 * z 3 * w 2 - x 0 * y 2 * z 1 * w 3 + x 0 * y 2 * z 3 * w 1 + x 0 * y 3 * z 1 * w 2 - x 0 * y 3 * z 2 * w 1 - x 1 * y 0 * z 2 * w 3 + x 1 * y 0 * z 3 * w 2 + x 1 * y 2 * z 0 * w 3 - x 1 * y 2 * z 3 * w 0 - x 1 * y 3 * z 0 * w 2 + x 1 * y 3 * z 2 * w 0 + x 2 * y 0 * z 1 * w 3 - x 2 * y 0 * z 3 * w 1 - x 2 * y 1 * z 0 * w 3 + x 2 * y 1 * z 3 * w 0 + x 2 * y 3 * z 0 * w 1 - x 2 * y 3 * z 1 * w 0 - x 3 * y 0 * z 1 * w 2 + x 3 * y 0 * z 2 * w 1 + x 3 * y 1 * z 0 * w 2 - x 3 * y 1 * z 2 * w 0 - x 3 * y 2 * z 0 * w 1 + x 3 * y 2 * z 1 * w 0

lemma gl_det_eq_det4 (x y z w : R4) : Matrix.det (Matrix.of ![x, y, z, w]) = gl_det4 x y z w := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, gl_det4, Fin.succAbove]
  ring

lemma gl_volumeIn_eq (N a b c : R4) : volumeIn N a b c = -gl_det4 N a b c := by
  rw [volumeIn, gl_det_eq_det4]; simp only [gl_det4, Pi.neg_apply]; ring

lemma gl_volumeIn_swap12 (N a b c : R4) : volumeIn N b a c = -volumeIn N a b c := by
  simp only [gl_volumeIn_eq, gl_det4]; ring

lemma gl_volumeIn_swap13 (N a b c : R4) : volumeIn N c b a = -volumeIn N a b c := by
  simp only [gl_volumeIn_eq, gl_det4]; ring

lemma gl_volumeIn_swap23 (N a b c : R4) : volumeIn N a c b = -volumeIn N a b c := by
  simp only [gl_volumeIn_eq, gl_det4]; ring

lemma gl_volumeIn_neg2 (N a b c : R4) : volumeIn N a (-b) c = -volumeIn N a b c := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.neg_apply]; ring

lemma gl_volumeIn_neg3 (N a b c : R4) : volumeIn N a b (-c) = -volumeIn N a b c := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.neg_apply]; ring

lemma gl_volumeIn_zero1 (N b c : R4) : volumeIn N 0 b c = 0 := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.zero_apply]; ring

lemma gl_volumeIn_zero2 (N a c : R4) : volumeIn N a 0 c = 0 := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.zero_apply]; ring

/-- Cramer identity for `u ⊥ N`. -/
lemma gl_cramer (N a b c u : R4) (hu : dot4 u N = 0) :
    dot4 u a * volumeIn N u b c + dot4 u b * volumeIn N a u c + dot4 u c * volumeIn N a b u =
      dot4 u u * volumeIn N a b c := by
  have hu' : gl_det4 u a b c * dot4 u N = 0 := by rw [hu, mul_zero]
  simp only [gl_volumeIn_eq, gl_det4, dot4, Fin.sum_univ_four, Pi.neg_apply] at hu' ⊢
  linear_combination hu'

/-- Derivative of `x ↦ V(a x, b x, c x)`. -/
lemma gl_hasDerivAt_volumeIn (N : R4) {a b c : ℝ → R4} {a' b' c' : R4} {x : ℝ}
    (ha' : HasDerivAt a a' x) (hb' : HasDerivAt b b' x) (hc' : HasDerivAt c c' x) :
    HasDerivAt (fun x => volumeIn N (a x) (b x) (c x))
      (volumeIn N a' (b x) (c x) + volumeIn N (a x) b' (c x) + volumeIn N (a x) (b x) c') x := by
  have ha : ∀ i, HasDerivAt (fun x => a x i) (a' i) x := fun i => (hasDerivAt_pi.1 ha') i
  have hb : ∀ i, HasDerivAt (fun x => b x i) (b' i) x := fun i => (hasDerivAt_pi.1 hb') i
  have hc : ∀ i, HasDerivAt (fun x => c x i) (c' i) x := fun i => (hasDerivAt_pi.1 hc') i
  have h := (((((((((((((((((((((((((((ha 1).mul (hb 2)).mul (hc 3)).const_mul (N 0)).sub ((((ha 1).mul (hb 3)).mul (hc 2)).const_mul (N 0))).sub ((((ha 2).mul (hb 1)).mul (hc 3)).const_mul (N 0))).add ((((ha 2).mul (hb 3)).mul (hc 1)).const_mul (N 0))).add ((((ha 3).mul (hb 1)).mul (hc 2)).const_mul (N 0))).sub ((((ha 3).mul (hb 2)).mul (hc 1)).const_mul (N 0))).sub ((((ha 0).mul (hb 2)).mul (hc 3)).const_mul (N 1))).add ((((ha 0).mul (hb 3)).mul (hc 2)).const_mul (N 1))).add ((((ha 2).mul (hb 0)).mul (hc 3)).const_mul (N 1))).sub ((((ha 2).mul (hb 3)).mul (hc 0)).const_mul (N 1))).sub ((((ha 3).mul (hb 0)).mul (hc 2)).const_mul (N 1))).add ((((ha 3).mul (hb 2)).mul (hc 0)).const_mul (N 1))).add ((((ha 0).mul (hb 1)).mul (hc 3)).const_mul (N 2))).sub ((((ha 0).mul (hb 3)).mul (hc 1)).const_mul (N 2))).sub ((((ha 1).mul (hb 0)).mul (hc 3)).const_mul (N 2))).add ((((ha 1).mul (hb 3)).mul (hc 0)).const_mul (N 2))).add ((((ha 3).mul (hb 0)).mul (hc 1)).const_mul (N 2))).sub ((((ha 3).mul (hb 1)).mul (hc 0)).const_mul (N 2))).sub ((((ha 0).mul (hb 1)).mul (hc 2)).const_mul (N 3))).add ((((ha 0).mul (hb 2)).mul (hc 1)).const_mul (N 3))).add ((((ha 1).mul (hb 0)).mul (hc 2)).const_mul (N 3))).sub ((((ha 1).mul (hb 2)).mul (hc 0)).const_mul (N 3))).sub ((((ha 2).mul (hb 0)).mul (hc 1)).const_mul (N 3))).add ((((ha 2).mul (hb 1)).mul (hc 0)).const_mul (N 3))).neg
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h
    (Filter.Eventually.of_forall fun y => ?_)) ?_
  · simp only [gl_volumeIn_eq, gl_det4, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]; ring
  · simp only [gl_volumeIn_eq, gl_det4, Pi.mul_apply]; ring

lemma gl_dot4_self_nonneg (u : R4) : 0 ≤ dot4 u u := by
  simp only [dot4, Fin.sum_univ_four]
  nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2),
    mul_self_nonneg (u 3)]

lemma gl_euclidNorm_sq (u : R4) : euclidNorm u ^ 2 = dot4 u u :=
  Real.sq_sqrt (gl_dot4_self_nonneg u)

lemma gl_dot4_self_pos {u : R4} (hu : u ≠ 0) : 0 < dot4 u u := by
  rcases (gl_dot4_self_nonneg u).lt_or_eq with h | h
  · exact h
  · exfalso; apply hu
    have h0 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 0 := by
      have := h.symm; simp only [dot4, Fin.sum_univ_four] at this; nlinarith
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (u 3)]

lemma gl_euclidNorm_pos {u : R4} (hu : u ≠ 0) : 0 < euclidNorm u :=
  Real.sqrt_pos.2 (gl_dot4_self_pos hu)

lemma gl_hasDerivAt_dot4 {a b : ℝ → R4} {a' b' : R4} {x : ℝ} (ha' : HasDerivAt a a' x)
    (hb' : HasDerivAt b b' x) :
    HasDerivAt (fun x => dot4 (a x) (b x)) (dot4 a' (b x) + dot4 (a x) b') x := by
  have ha : ∀ i, HasDerivAt (fun x => a x i) (a' i) x := fun i => (hasDerivAt_pi.1 ha') i
  have hb : ∀ i, HasDerivAt (fun x => b x i) (b' i) x := fun i => (hasDerivAt_pi.1 hb') i
  have h := ((((ha 0).mul (hb 0)).add ((ha 1).mul (hb 1))).add ((ha 2).mul (hb 2))).add
    ((ha 3).mul (hb 3))
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h
    (Filter.Eventually.of_forall fun y => ?_)) ?_
  · simp only [dot4, Fin.sum_univ_four, Pi.add_apply, Pi.mul_apply]
  · simp only [dot4, Fin.sum_univ_four]; ring

lemma gl_hasDerivAt_euclidNorm {u : ℝ → R4} {u' : R4} {x : ℝ} (hu' : HasDerivAt u u' x)
    (hne : u x ≠ 0) :
    HasDerivAt (fun x => euclidNorm (u x)) (dot4 (u x) u' / euclidNorm (u x)) x := by
  have hq := gl_hasDerivAt_dot4 hu' hu'
  have h := hq.sqrt (gl_dot4_self_pos hne).ne'
  have hs : dot4 u' (u x) = dot4 (u x) u' := by
    simp only [dot4, Fin.sum_univ_four]; ring
  refine HasDerivAt.congr_deriv (f := fun x => euclidNorm (u x)) h ?_
  rw [hs]; simp only [euclidNorm]; field_simp; ring

/-- The Gauss integrand `V(a, b, u) / |u|³`. -/
def gl_integrand (N a b u : R4) : ℝ := volumeIn N a b u / euclidNorm u ^ 3

/-- Its derivative along `(a', b', u')`. -/
def gl_integrandDeriv (N a b u a' b' u' : R4) : ℝ :=
  (volumeIn N a' b u + volumeIn N a b' u + volumeIn N a b u') / euclidNorm u ^ 3 -
    3 * volumeIn N a b u * dot4 u u' / euclidNorm u ^ 5

lemma gl_hasDerivAt_integrand (N : R4) {a b u : ℝ → R4} {a' b' u' : R4} {x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) (hu : HasDerivAt u u' x) (hne : u x ≠ 0) :
    HasDerivAt (fun x => gl_integrand N (a x) (b x) (u x))
      (gl_integrandDeriv N (a x) (b x) (u x) a' b' u') x := by
  have hV := gl_hasDerivAt_volumeIn N ha hb hu
  have hr := (gl_hasDerivAt_euclidNorm hu hne).pow 3
  have hpos := gl_euclidNorm_pos hne
  have h := hV.div hr (pow_pos hpos 3).ne'
  have e : (fun x => gl_integrand N (a x) (b x) (u x)) =
      fun x => volumeIn N (a x) (b x) (u x) / euclidNorm (u x) ^ 3 := rfl
  rw [e]
  refine HasDerivAt.congr_deriv h ?_
  simp only [gl_integrandDeriv, Pi.pow_apply]
  field_simp
  ring

/-- The closedness identity of the Gauss 2-form at a point (`u ⊥ N`, `u ≠ 0`):
`∂_τ f = ∂_s P - ∂_t Q` with `f = G(A_s, B_t, u)`, `P = G(u_τ, B_t, u)`, `Q = G(A_s, u_τ, u)`,
once the mixed partials `X = A_{sτ} = A_{τs}`, `Y = B_{tτ} = B_{τt}` are identified. -/
lemma gl_closed_identity (N a b c u X Y : R4) (hu : dot4 u N = 0) (hne : u ≠ 0) :
    gl_integrandDeriv N a b u X Y c =
      gl_integrandDeriv N c b u X 0 a - gl_integrandDeriv N a c u 0 (-Y) (-b) := by
  have hpos := gl_euclidNorm_pos hne
  have hsq := gl_euclidNorm_sq u
  have key := gl_cramer N a b c u hu
  have hneg : dot4 u (-b) = -dot4 u b := by
    simp only [dot4, Fin.sum_univ_four, Pi.neg_apply]; ring
  simp only [gl_integrandDeriv, gl_volumeIn_zero1, gl_volumeIn_zero2, gl_volumeIn_neg2,
    gl_volumeIn_neg3, hneg]
  rw [gl_volumeIn_swap13 N a b c, gl_volumeIn_swap23 N a b c, gl_volumeIn_swap13 N u b c,
    gl_volumeIn_swap23 N a u c]
  rw [← hsq] at key
  set r := euclidNorm u
  have hs : r * r⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  simp only [div_eq_mul_inv, ← inv_pow]
  set s := r⁻¹
  linear_combination (-3 * s ^ 5) * key + (-3 * volumeIn N a b c * s ^ 3 * (1 + r * s)) * hs

end HryniewiczCriterion

/-!
# Homotopy invariance of the Gauss linking integral (fixed pole)

If `A τ s`, `B τ t` are `C²` in `(τ, s)` / `(τ, t)`, `1`-periodic in the loop variable,
disjoint, and `A - B ⊥ N`, then
`∫₀¹∫₀¹ V(∂ₛA, ∂ₜB, A - B) / |A - B|³ dt ds` is the same at `τ = 0` and `τ = 1`.
-/


noncomputable section

namespace HryniewiczCriterion

/-! ### Partial derivatives of a `C²` map of two real variables -/

section Partials

variable {A : ℝ → ℝ → R4} (hA : ContDiff ℝ 2 (Function.uncurry A))
include hA

lemma gl_contDiff_fderiv : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry A)) :=
  hA.fderiv_right (m := 1) (by norm_num)

lemma gl_hasDerivAt_fst (τ s : ℝ) :
    HasDerivAt (fun τ => A τ s) (fderiv ℝ (Function.uncurry A) (τ, s) (1, 0)) τ := by
  have hd : HasFDerivAt (Function.uncurry A) (fderiv ℝ (Function.uncurry A) (τ, s)) (τ, s) :=
    ((hA.differentiable (by simp)) (τ, s)).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (l := Function.uncurry A) (f := fun τ => ((τ, s) : ℝ × ℝ)) τ hd
    ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ s))

lemma gl_hasDerivAt_snd (τ s : ℝ) :
    HasDerivAt (A τ) (fderiv ℝ (Function.uncurry A) (τ, s) (0, 1)) s := by
  have hd : HasFDerivAt (Function.uncurry A) (fderiv ℝ (Function.uncurry A) (τ, s)) (τ, s) :=
    ((hA.differentiable (by simp)) (τ, s)).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (l := Function.uncurry A) (f := fun s => ((τ, s) : ℝ × ℝ)) s hd
    ((hasDerivAt_const s τ).prodMk (hasDerivAt_id s))

lemma gl_hasDerivAt_fderiv_fst (τ s : ℝ) (v : ℝ × ℝ) :
    HasDerivAt (fun τ => fderiv ℝ (Function.uncurry A) (τ, s) v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry A)) (τ, s) (1, 0) v) τ := by
  have hD := gl_contDiff_fderiv hA
  have hd : HasFDerivAt (fderiv ℝ (Function.uncurry A))
      (fderiv ℝ (fderiv ℝ (Function.uncurry A)) (τ, s)) (τ, s) :=
    ((hD.differentiable (by simp)) (τ, s)).hasFDerivAt
  exact (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt τ
    (HasFDerivAt.comp_hasDerivAt (f := fun τ => ((τ, s) : ℝ × ℝ)) τ hd
      ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ s)))

lemma gl_hasDerivAt_fderiv_snd (τ s : ℝ) (v : ℝ × ℝ) :
    HasDerivAt (fun s => fderiv ℝ (Function.uncurry A) (τ, s) v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry A)) (τ, s) (0, 1) v) s := by
  have hD := gl_contDiff_fderiv hA
  have hd : HasFDerivAt (fderiv ℝ (Function.uncurry A))
      (fderiv ℝ (fderiv ℝ (Function.uncurry A)) (τ, s)) (τ, s) :=
    ((hD.differentiable (by simp)) (τ, s)).hasFDerivAt
  exact (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt s
    (HasFDerivAt.comp_hasDerivAt (f := fun s => ((τ, s) : ℝ × ℝ)) s hd
      ((hasDerivAt_const s τ).prodMk (hasDerivAt_id s)))

lemma gl_fderiv_symm (p v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (Function.uncurry A)) p v w =
      fderiv ℝ (fderiv ℝ (Function.uncurry A)) p w v :=
  hA.contDiffAt.isSymmSndFDerivAt (by simp) v w

lemma gl_continuous_fderiv_apply (v : ℝ × ℝ) :
    Continuous fun p => fderiv ℝ (Function.uncurry A) p v :=
  (gl_contDiff_fderiv hA).continuous.clm_apply continuous_const

lemma gl_continuous_fderiv2_apply (v w : ℝ × ℝ) :
    Continuous fun p => fderiv ℝ (fderiv ℝ (Function.uncurry A)) p v w :=
  (((gl_contDiff_fderiv hA).continuous_fderiv (by norm_num)).clm_apply
    continuous_const).clm_apply continuous_const

end Partials

/-! ### Continuity of the integrand -/

lemma gl_continuous_volumeIn {X : Type*} [TopologicalSpace X] (N : R4) {a b c : X → R4}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous fun p => volumeIn N (a p) (b p) (c p) := by
  have ha' := fun i => (continuous_apply i).comp ha
  have hb' := fun i => (continuous_apply i).comp hb
  have hc' := fun i => (continuous_apply i).comp hc
  simp only [gl_volumeIn_eq, gl_det4]
  simp only [Function.comp_def] at ha' hb' hc'
  fun_prop

lemma gl_continuous_euclidNorm {X : Type*} [TopologicalSpace X] {u : X → R4} (hu : Continuous u) :
    Continuous fun p => euclidNorm (u p) := by
  have hu' := fun i => (continuous_apply i).comp hu
  simp only [Function.comp_def] at hu'
  simp only [euclidNorm, dot4, Fin.sum_univ_four]
  fun_prop

lemma gl_continuous_dot4 {X : Type*} [TopologicalSpace X] {u v : X → R4} (hu : Continuous u)
    (hv : Continuous v) : Continuous fun p => dot4 (u p) (v p) := by
  have hu' := fun i => (continuous_apply i).comp hu
  have hv' := fun i => (continuous_apply i).comp hv
  simp only [Function.comp_def] at hu' hv'
  simp only [dot4, Fin.sum_univ_four]
  fun_prop

lemma gl_continuous_integrand {X : Type*} [TopologicalSpace X] (N : R4) {a b u : X → R4}
    (ha : Continuous a) (hb : Continuous b) (hu : Continuous u) (hne : ∀ p, u p ≠ 0) :
    Continuous fun p => gl_integrand N (a p) (b p) (u p) :=
  (gl_continuous_volumeIn N ha hb hu).div ((gl_continuous_euclidNorm hu).pow 3)
    fun p => pow_ne_zero 3 (gl_euclidNorm_pos (hne p)).ne'

lemma gl_continuous_integrandDeriv {X : Type*} [TopologicalSpace X] (N : R4)
    {a b u a' b' u' : X → R4} (ha : Continuous a) (hb : Continuous b) (hu : Continuous u)
    (ha' : Continuous a') (hb' : Continuous b') (hu' : Continuous u') (hne : ∀ p, u p ≠ 0) :
    Continuous fun p => gl_integrandDeriv N (a p) (b p) (u p) (a' p) (b' p) (u' p) := by
  have hr := gl_continuous_euclidNorm hu
  have hr0 : ∀ p, euclidNorm (u p) ≠ 0 := fun p => (gl_euclidNorm_pos (hne p)).ne'
  refine Continuous.sub ?_ ?_
  · exact ((((gl_continuous_volumeIn N ha' hb hu).add (gl_continuous_volumeIn N ha hb' hu)).add
      (gl_continuous_volumeIn N ha hb hu'))).div (hr.pow 3) fun p => pow_ne_zero 3 (hr0 p)
  · exact (((continuous_const.mul (gl_continuous_volumeIn N ha hb hu)).mul
      (gl_continuous_dot4 hu hu'))).div (hr.pow 5) fun p => pow_ne_zero 5 (hr0 p)

/-! ### Fubini bookkeeping on `[0,1]³` -/

/-- Fubini on `[0,1]²` for a continuous integrand. -/
lemma gl_integral_integral_swap_unit {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f x y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma gl_continuous_param {X : Type*} [TopologicalSpace X] {F : X → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ t in (0 : ℝ)..1, F x t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1

lemma gl_triple_swap {G : ℝ → ℝ → ℝ → ℝ}
    (hG : Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..1, G τ s t =
      ∫ τ in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, G τ s t := by
  have h1 : ∀ s, ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..1, G τ s t =
      ∫ τ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, G τ s t := fun s =>
    gl_integral_integral_swap_unit (f := fun t τ => G τ s t)
      (hG.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (q.2, s, q.1)))
  simp only [h1]
  refine gl_integral_integral_swap_unit (f := fun s τ => ∫ t in (0 : ℝ)..1, G τ s t) ?_
  exact gl_continuous_param (F := fun (q : ℝ × ℝ) t => G q.2 q.1 t)
    (hG.comp (by fun_prop : Continuous fun r : (ℝ × ℝ) × ℝ => (r.1.2, r.1.1, r.2)))

/-- The integral bookkeeping behind the homotopy invariance. -/
lemma gl_homotopy_assemble {f F' Ps Qt : ℝ → ℝ → ℝ → ℝ}
    (cf : Continuous fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
    (cF' : Continuous fun p : ℝ × ℝ × ℝ => F' p.1 p.2.1 p.2.2)
    (cPs : Continuous fun p : ℝ × ℝ × ℝ => Ps p.1 p.2.1 p.2.2)
    (cQt : Continuous fun p : ℝ × ℝ × ℝ => Qt p.1 p.2.1 p.2.2)
    (S1 : ∀ s t, f 1 s t - f 0 s t = ∫ τ in (0 : ℝ)..1, F' τ s t)
    (hclosed : ∀ τ s t, F' τ s t = Ps τ s t - Qt τ s t)
    (S2 : ∀ τ t, ∫ s in (0 : ℝ)..1, Ps τ s t = 0)
    (S3 : ∀ τ s, ∫ t in (0 : ℝ)..1, Qt τ s t = 0) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 0 s t =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 1 s t := by
  have int3 : ∀ {G : ℝ → ℝ → ℝ → ℝ}, (Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) →
      ∀ τ, Continuous fun s => ∫ t in (0 : ℝ)..1, G τ s t := by
    intro G hG τ
    exact gl_continuous_param (F := fun s t => G τ s t)
      (hG.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (τ, q.1, q.2)))
  have int3' : ∀ {G : ℝ → ℝ → ℝ → ℝ}, (Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) →
      ∀ τ s, Continuous fun t => G τ s t := by
    intro G hG τ s
    exact hG.comp (by fun_prop : Continuous fun t : ℝ => (τ, s, t))
  have step : ∀ τ, ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F' τ s t = 0 := by
    intro τ
    have e : ∀ s, ∫ t in (0 : ℝ)..1, F' τ s t =
        (∫ t in (0 : ℝ)..1, Ps τ s t) - ∫ t in (0 : ℝ)..1, Qt τ s t := by
      intro s
      simp only [hclosed]
      exact intervalIntegral.integral_sub ((int3' cPs τ s).intervalIntegrable 0 1)
        ((int3' cQt τ s).intervalIntegrable 0 1)
    simp only [e, S3, sub_zero]
    rw [gl_integral_integral_swap_unit (f := fun s t => Ps τ s t)
      (cPs.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (τ, q.1, q.2)))]
    simp only [S2, intervalIntegral.integral_zero]
  have total : (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 1 s t) -
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 0 s t = 0 := by
    have e : ∀ s, (∫ t in (0 : ℝ)..1, f 1 s t) - ∫ t in (0 : ℝ)..1, f 0 s t =
        ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..1, F' τ s t := by
      intro s
      rw [← intervalIntegral.integral_sub ((int3' cf 1 s).intervalIntegrable 0 1)
        ((int3' cf 0 s).intervalIntegrable 0 1)]
      simp only [S1]
    rw [← intervalIntegral.integral_sub ((int3 cf 1).intervalIntegrable 0 1)
      ((int3 cf 0).intervalIntegrable 0 1)]
    simp only [e]
    rw [gl_triple_swap (G := F') cF']
    simp only [step, intervalIntegral.integral_zero]
  exact (sub_eq_zero.1 total).symm

/-! ### The homotopy invariance -/

theorem gl_gauss_homotopy (N : R4) (A B : ℝ → ℝ → R4)
    (hA : ContDiff ℝ 2 (Function.uncurry A)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hAper : ∀ τ s, A τ (s + 1) = A τ s) (hBper : ∀ τ t, B τ (t + 1) = B τ t)
    (hN : ∀ τ s t, dot4 (A τ s - B τ t) N = 0) (hne : ∀ τ s t, A τ s ≠ B τ t) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        gl_integrand N (deriv (A 0) s) (deriv (B 0) t) (A 0 s - B 0 t) =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        gl_integrand N (deriv (A 1) s) (deriv (B 1) t) (A 1 s - B 1 t) := by
  set DA := fderiv ℝ (Function.uncurry A)
  set DB := fderiv ℝ (Function.uncurry B)
  set D2A := fderiv ℝ DA
  set D2B := fderiv ℝ DB
  set e1 : ℝ × ℝ := (1, 0)
  set e2 : ℝ × ℝ := (0, 1)
  -- the pieces, as functions of `(τ, s, t)`
  set As : ℝ → ℝ → R4 := fun τ s => DA (τ, s) e2
  set Bt : ℝ → ℝ → R4 := fun τ t => DB (τ, t) e2
  set c : ℝ → ℝ → ℝ → R4 := fun τ s t => DA (τ, s) e1 - DB (τ, t) e1
  set u : ℝ → ℝ → ℝ → R4 := fun τ s t => A τ s - B τ t
  set X : ℝ → ℝ → R4 := fun τ s => D2A (τ, s) e1 e2
  set Y : ℝ → ℝ → R4 := fun τ t => D2B (τ, t) e1 e2
  set f : ℝ → ℝ → ℝ → ℝ := fun τ s t => gl_integrand N (As τ s) (Bt τ t) (u τ s t)
  set F' : ℝ → ℝ → ℝ → ℝ := fun τ s t =>
    gl_integrandDeriv N (As τ s) (Bt τ t) (u τ s t) (X τ s) (Y τ t) (c τ s t)
  set Ps : ℝ → ℝ → ℝ → ℝ := fun τ s t =>
    gl_integrandDeriv N (c τ s t) (Bt τ t) (u τ s t) (X τ s) 0 (As τ s)
  set Qt : ℝ → ℝ → ℝ → ℝ := fun τ s t =>
    gl_integrandDeriv N (As τ s) (c τ s t) (u τ s t) 0 (-Y τ t) (-Bt τ t)
  have hu0 : ∀ τ s t, u τ s t ≠ 0 := fun τ s t => sub_ne_zero.2 (hne τ s t)
  have hderA : ∀ τ s, deriv (A τ) s = As τ s := fun τ s => (gl_hasDerivAt_snd hA τ s).deriv
  have hderB : ∀ τ t, deriv (B τ) t = Bt τ t := fun τ t => (gl_hasDerivAt_snd hB τ t).deriv
  -- continuity on `ℝ × ℝ × ℝ`
  have cA : Continuous fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 :=
    hA.continuous.comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1) : ℝ × ℝ))
  have cB : Continuous fun p : ℝ × ℝ × ℝ => B p.1 p.2.2 :=
    hB.continuous.comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.2) : ℝ × ℝ))
  have cDA : ∀ v, Continuous fun p : ℝ × ℝ × ℝ => DA (p.1, p.2.1) v := fun v =>
    (gl_continuous_fderiv_apply hA v).comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1) : ℝ × ℝ))
  have cDB : ∀ v, Continuous fun p : ℝ × ℝ × ℝ => DB (p.1, p.2.2) v := fun v =>
    (gl_continuous_fderiv_apply hB v).comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.2) : ℝ × ℝ))
  have cX : Continuous fun p : ℝ × ℝ × ℝ => X p.1 p.2.1 :=
    (gl_continuous_fderiv2_apply hA e1 e2).comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1) : ℝ × ℝ))
  have cY : Continuous fun p : ℝ × ℝ × ℝ => Y p.1 p.2.2 :=
    (gl_continuous_fderiv2_apply hB e1 e2).comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.1, p.2.2) : ℝ × ℝ))
  have cu : Continuous fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2 := cA.sub cB
  have cc : Continuous fun p : ℝ × ℝ × ℝ => c p.1 p.2.1 p.2.2 := (cDA e1).sub (cDB e1)
  have hu0' : ∀ p : ℝ × ℝ × ℝ, u p.1 p.2.1 p.2.2 ≠ 0 := fun p => hu0 _ _ _
  have cF' : Continuous fun p : ℝ × ℝ × ℝ => F' p.1 p.2.1 p.2.2 :=
    gl_continuous_integrandDeriv N (cDA e2) (cDB e2) cu cX cY cc hu0'
  have cPs : Continuous fun p : ℝ × ℝ × ℝ => Ps p.1 p.2.1 p.2.2 :=
    gl_continuous_integrandDeriv N cc (cDB e2) cu cX continuous_const (cDA e2) hu0'
  have cQt : Continuous fun p : ℝ × ℝ × ℝ => Qt p.1 p.2.1 p.2.2 :=
    gl_continuous_integrandDeriv N (cDA e2) cc cu continuous_const cY.neg (cDB e2).neg hu0'
  have cf : Continuous fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2 :=
    gl_continuous_integrand N (cDA e2) (cDB e2) cu hu0'
  -- pointwise closedness
  have hclosed : ∀ τ s t, F' τ s t = Ps τ s t - Qt τ s t := fun τ s t =>
    gl_closed_identity N (As τ s) (Bt τ t) (c τ s t) (u τ s t) (X τ s) (Y τ t) (hN τ s t)
      (hu0 τ s t)
  -- S1: FTC in `τ`
  have S1 : ∀ s t, f 1 s t - f 0 s t = ∫ τ in (0 : ℝ)..1, F' τ s t := by
    intro s t
    have hder : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun τ => f τ s t) (F' τ s t) τ := by
      intro τ _
      have hu : HasDerivAt (fun τ => u τ s t) (c τ s t) τ :=
        (gl_hasDerivAt_fst hA τ s).sub (gl_hasDerivAt_fst hB τ t)
      exact gl_hasDerivAt_integrand N (gl_hasDerivAt_fderiv_fst hA τ s e2)
        (gl_hasDerivAt_fderiv_fst hB τ t e2) hu (hu0 τ s t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((cF'.comp (by fun_prop : Continuous fun τ : ℝ => (τ, s, t))).intervalIntegrable 0 1)]
  -- S2: FTC in `s`, periodicity
  have S2 : ∀ τ t, ∫ s in (0 : ℝ)..1, Ps τ s t = 0 := by
    intro τ t
    have hder : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s => gl_integrand N (c τ s t) (Bt τ t) (u τ s t)) (Ps τ s t) s := by
      intro s _
      have hc : HasDerivAt (fun s => c τ s t) (X τ s) s := by
        have h := (gl_hasDerivAt_fderiv_snd hA τ s e1).sub_const (DB (τ, t) e1)
        rwa [gl_fderiv_symm hA (τ, s) e2 e1] at h
      have hu : HasDerivAt (fun s => u τ s t) (As τ s) s :=
        (gl_hasDerivAt_snd hA τ s).sub_const (B τ t)
      exact gl_hasDerivAt_integrand N hc (hasDerivAt_const s (Bt τ t)) hu (hu0 τ s t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((cPs.comp (by fun_prop : Continuous fun s : ℝ => (τ, s, t))).intervalIntegrable 0 1)]
    have h1 : A τ 1 = A τ 0 := by simpa using hAper τ 0
    have h2 : DA (τ, 1) e1 = DA (τ, 0) e1 := by
      have h := gl_hasDerivAt_fst hA τ 1
      have hfun : (fun τ => A τ 1) = fun τ => A τ 0 := funext fun τ => by simpa using hAper τ 0
      rw [hfun] at h
      exact h.unique (gl_hasDerivAt_fst hA τ 0)
    simp only [c, u, h1, h2, sub_self]
  -- S3: FTC in `t`, periodicity
  have S3 : ∀ τ s, ∫ t in (0 : ℝ)..1, Qt τ s t = 0 := by
    intro τ s
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun t => gl_integrand N (As τ s) (c τ s t) (u τ s t)) (Qt τ s t) t := by
      intro t _
      have hc : HasDerivAt (fun t => c τ s t) (-Y τ t) t := by
        have h := (gl_hasDerivAt_fderiv_snd hB τ t e1).const_sub (DA (τ, s) e1)
        rwa [gl_fderiv_symm hB (τ, t) e2 e1] at h
      have hu : HasDerivAt (fun t => u τ s t) (-Bt τ t) t :=
        (gl_hasDerivAt_snd hB τ t).const_sub (A τ s)
      exact gl_hasDerivAt_integrand N (hasDerivAt_const t (As τ s)) hc hu (hu0 τ s t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((cQt.comp (by fun_prop : Continuous fun t : ℝ => (τ, s, t))).intervalIntegrable 0 1)]
    have h1 : B τ 1 = B τ 0 := by simpa using hBper τ 0
    have h2 : DB (τ, 1) e1 = DB (τ, 0) e1 := by
      have h := gl_hasDerivAt_fst hB τ 1
      have hfun : (fun τ => B τ 1) = fun τ => B τ 0 := funext fun τ => by simpa using hBper τ 0
      rw [hfun] at h
      exact h.unique (gl_hasDerivAt_fst hB τ 0)
    simp only [c, u, h1, h2, sub_self]
  simp only [hderA, hderB]
  exact gl_homotopy_assemble cf cF' cPs cQt S1 hclosed S2 S3

end HryniewiczCriterion

/-!
# Moving the pole along a path

Reflections `S_v x = x - 2⟨x,v⟩/|v|² v` and the rotation `R = S_{a+N} ∘ S_a` (taking `a`
to `N` for unit `a, N` with `a + N ≠ 0`). The Gauss integrand is invariant under `R`, and
stereographic projection is `R`-equivariant, so moving the pole along a `C²` path
`P τ` (missing both loops, never antipodal to `P 0`) becomes a homotopy of the loops
with a fixed pole.
-/


noncomputable section

namespace HryniewiczCriterion

/-! ### Bilinearity of `dot4` -/

lemma gl_dot4_comm (x y : R4) : dot4 x y = dot4 y x := by
  simp only [dot4, Fin.sum_univ_four]; ring

lemma gl_dot4_add_left (x y v : R4) : dot4 (x + y) v = dot4 x v + dot4 y v := by
  simp only [dot4, Fin.sum_univ_four, Pi.add_apply]; ring

lemma gl_dot4_sub_left (x y v : R4) : dot4 (x - y) v = dot4 x v - dot4 y v := by
  simp only [dot4, Fin.sum_univ_four, Pi.sub_apply]; ring

lemma gl_dot4_smul_left (c : ℝ) (x v : R4) : dot4 (c • x) v = c * dot4 x v := by
  simp only [dot4, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring

lemma gl_dot4_sub_right (v x y : R4) : dot4 v (x - y) = dot4 v x - dot4 v y := by
  simp only [dot4, Fin.sum_univ_four, Pi.sub_apply]; ring

lemma gl_dot4_smul_right (c : ℝ) (v x : R4) : dot4 v (c • x) = c * dot4 v x := by
  simp only [dot4, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring

lemma gl_dot4_zero_right (v : R4) : dot4 v 0 = 0 := by
  simp [dot4]

lemma gl_eq_of_dot4_sub {x y : R4} (h : dot4 (x - y) (x - y) = 0) : x = y := by
  by_contra hne
  exact (gl_dot4_self_pos (sub_ne_zero.2 hne)).ne' h

lemma gl_dot4_self_of_unit {y : R4} (hy : euclidNorm y = 1) : dot4 y y = 1 := by
  rw [← gl_euclidNorm_sq, hy]; norm_num

/-- Unit vectors with inner product `1` coincide. -/
lemma gl_eq_of_dot4_eq_one {y N : R4} (hy : dot4 y y = 1) (hN : dot4 N N = 1)
    (h : dot4 y N = 1) : y = N := by
  apply gl_eq_of_dot4_sub
  rw [gl_dot4_sub_left, gl_dot4_sub_right, gl_dot4_sub_right, gl_dot4_comm N y, hy, hN, h]
  ring

/-! ### Reflections -/

/-- The reflection of `x` in the hyperplane `v^⊥`. -/
def gl_refl (v x : R4) : R4 := x - (2 * dot4 x v / dot4 v v) • v

lemma gl_refl_add (v x y : R4) : gl_refl v (x + y) = gl_refl v x + gl_refl v y := by
  simp only [gl_refl, gl_dot4_add_left]; ext i; simp only [Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]; ring

lemma gl_refl_sub (v x y : R4) : gl_refl v (x - y) = gl_refl v x - gl_refl v y := by
  simp only [gl_refl, gl_dot4_sub_left]; ext i; simp only [Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]; ring

lemma gl_refl_smul (v x : R4) (c : ℝ) : gl_refl v (c • x) = c • gl_refl v x := by
  simp only [gl_refl, gl_dot4_smul_left]; ext i; simp only [Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]; ring

lemma gl_refl_dot {v : R4} (hv : dot4 v v ≠ 0) (x y : R4) :
    dot4 (gl_refl v x) (gl_refl v y) = dot4 x y := by
  simp only [gl_refl, gl_dot4_sub_left, gl_dot4_sub_right, gl_dot4_smul_left,
    gl_dot4_smul_right, gl_dot4_comm v y, gl_dot4_comm x v]
  field_simp
  ring

lemma gl_det4_sub_smul (x y z w v : R4) (a b c d : ℝ) :
    gl_det4 (x - a • v) (y - b • v) (z - c • v) (w - d • v) =
      gl_det4 x y z w - a * gl_det4 v y z w - b * gl_det4 x v z w - c * gl_det4 x y v w -
        d * gl_det4 x y z v := by
  simp only [gl_det4, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma gl_cramer4 (v x y z w : R4) :
    dot4 x v * gl_det4 v y z w + dot4 y v * gl_det4 x v z w + dot4 z v * gl_det4 x y v w +
      dot4 w v * gl_det4 x y z v = dot4 v v * gl_det4 x y z w := by
  simp only [gl_det4, dot4, Fin.sum_univ_four]; ring

lemma gl_refl_det {v : R4} (hv : dot4 v v ≠ 0) (x y z w : R4) :
    gl_det4 (gl_refl v x) (gl_refl v y) (gl_refl v z) (gl_refl v w) = -gl_det4 x y z w := by
  simp only [gl_refl]
  rw [gl_det4_sub_smul]
  have key := gl_cramer4 v x y z w
  have hq : dot4 v v * (dot4 v v)⁻¹ = 1 := mul_inv_cancel₀ hv
  simp only [div_eq_mul_inv]
  linear_combination (-2 * (dot4 v v)⁻¹) * key + (-2 * gl_det4 x y z w) * hq

lemma gl_refl_self {v : R4} (hv : dot4 v v ≠ 0) : gl_refl v v = -v := by
  simp only [gl_refl]
  rw [mul_div_assoc, div_self hv, mul_one, two_smul]; abel

lemma gl_hasDerivAt_refl (v : R4) {g : ℝ → R4} {g' : R4} {s : ℝ} (hg : HasDerivAt g g' s) :
    HasDerivAt (fun s => gl_refl v (g s)) (gl_refl v g') s := by
  have h := hg.sub ((((gl_hasDerivAt_dot4 hg (hasDerivAt_const s v)).const_mul 2).div_const
    (dot4 v v)).smul_const v)
  refine HasDerivAt.congr_deriv h ?_
  simp only [gl_refl, gl_dot4_zero_right, add_zero]

lemma gl_contDiff_dot4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {x y : E → R4} (hx : ContDiff ℝ n x) (hy : ContDiff ℝ n y) :
    ContDiff ℝ n fun p => dot4 (x p) (y p) := by
  have hx' := fun i => contDiff_pi.1 hx i
  have hy' := fun i => contDiff_pi.1 hy i
  simp only [dot4, Fin.sum_univ_four]
  exact ((((hx' 0).mul (hy' 0)).add ((hx' 1).mul (hy' 1))).add ((hx' 2).mul (hy' 2))).add
    ((hx' 3).mul (hy' 3))

lemma gl_contDiff_refl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {v x : E → R4} (hv : ContDiff ℝ n v) (hx : ContDiff ℝ n x) (hne : ∀ p, dot4 (v p) (v p) ≠ 0) :
    ContDiff ℝ n fun p => gl_refl (v p) (x p) := by
  simp only [gl_refl]
  exact hx.sub (((contDiff_const.mul (gl_contDiff_dot4 hx hv)).div (gl_contDiff_dot4 hv hv)
    hne).smul hv)

lemma gl_contDiff_stereo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    (N : R4) {y : E → R4} (hy : ContDiff ℝ n y) (hne : ∀ p, 1 - dot4 (y p) N ≠ 0) :
    ContDiff ℝ n fun p => stereographicFrom N (y p) := by
  simp only [stereographicFrom]
  exact ((contDiff_const.sub (gl_contDiff_dot4 hy contDiff_const)).inv hne).smul
    (hy.sub ((gl_contDiff_dot4 hy contDiff_const).smul contDiff_const))

lemma gl_stereo_refl {v : R4} (hv : dot4 v v ≠ 0) (N y : R4) :
    stereographicFrom (gl_refl v N) (gl_refl v y) = gl_refl v (stereographicFrom N y) := by
  simp only [stereographicFrom, gl_refl_dot hv, gl_refl_smul, gl_refl_sub]

/-! ### The rotation `S_{a+N} ∘ S_a` -/

/-- The rotation `S_{a+N} ∘ S_a`. -/
def gl_rot (a N x : R4) : R4 := gl_refl (a + N) (gl_refl a x)

section Rot

variable {a N : R4} (ha : dot4 a a ≠ 0) (haN : dot4 (a + N) (a + N) ≠ 0)
include ha haN

lemma gl_rot_sub (x y : R4) : gl_rot a N (x - y) = gl_rot a N x - gl_rot a N y := by
  simp only [gl_rot, gl_refl_sub]

lemma gl_rot_dot (x y : R4) : dot4 (gl_rot a N x) (gl_rot a N y) = dot4 x y := by
  simp only [gl_rot, gl_refl_dot haN, gl_refl_dot ha]

lemma gl_rot_det (x y z w : R4) :
    gl_det4 (gl_rot a N x) (gl_rot a N y) (gl_rot a N z) (gl_rot a N w) = gl_det4 x y z w := by
  simp only [gl_rot, gl_refl_det haN, gl_refl_det ha, neg_neg]

lemma gl_rot_stereo (M y : R4) :
    stereographicFrom (gl_rot a N M) (gl_rot a N y) = gl_rot a N (stereographicFrom M y) := by
  simp only [gl_rot, gl_stereo_refl ha, gl_stereo_refl haN]

lemma gl_rot_volumeIn (M x y z : R4) :
    volumeIn (gl_rot a N M) (gl_rot a N x) (gl_rot a N y) (gl_rot a N z) = volumeIn M x y z := by
  simp only [gl_volumeIn_eq, gl_rot_det ha haN]

lemma gl_rot_euclidNorm (x : R4) : euclidNorm (gl_rot a N x) = euclidNorm x := by
  simp only [euclidNorm, gl_rot_dot ha haN]

lemma gl_rot_injective {x y : R4} (h : gl_rot a N x = gl_rot a N y) : x = y := by
  apply gl_eq_of_dot4_sub
  rw [← gl_rot_dot ha haN, gl_rot_sub ha haN, h, sub_self, gl_dot4_zero_right]

lemma gl_hasDerivAt_rot {g : ℝ → R4} {g' : R4} {s : ℝ} (hg : HasDerivAt g g' s) :
    HasDerivAt (fun s => gl_rot a N (g s)) (gl_rot a N g') s :=
  gl_hasDerivAt_refl (a + N) (gl_hasDerivAt_refl a hg)

end Rot

lemma gl_rot_self {a N : R4} (ha : dot4 a a = 1) (hN : dot4 N N = 1)
    (haN : dot4 (a + N) (a + N) ≠ 0) : gl_rot a N a = N := by
  have h1 : gl_refl a a = -a := gl_refl_self (by rw [ha]; norm_num)
  have hk : dot4 (a + N) (a + N) = 2 * (1 + dot4 a N) := by
    rw [gl_dot4_add_left, gl_dot4_comm a (a + N), gl_dot4_comm N (a + N), gl_dot4_add_left,
      gl_dot4_add_left, ha, hN, gl_dot4_comm N a]; ring
  have hk' : dot4 (-a) (a + N) = -(1 + dot4 a N) := by
    rw [gl_dot4_comm, gl_dot4_add_left]
    simp only [dot4, Fin.sum_univ_four, Pi.neg_apply] at ha ⊢
    linarith [ha]
  have hne : (1 + dot4 a N) ≠ 0 := by
    intro h0; apply haN; rw [hk, h0, mul_zero]
  rw [gl_rot, h1]
  simp only [gl_refl, hk', hk]
  have : 2 * -(1 + dot4 a N) / (2 * (1 + dot4 a N)) = -1 := by field_simp
  rw [this]; simp

/-! ### Stereographic projection: orthogonality and injectivity -/

lemma gl_stereo_dot_N {N : R4} (hN : dot4 N N = 1) (y : R4) :
    dot4 (stereographicFrom N y) N = 0 := by
  simp only [stereographicFrom, gl_dot4_smul_left, gl_dot4_sub_left, hN]; ring

lemma gl_stereo_inv {N y : R4} (hN : dot4 N N = 1) (hy : dot4 y y = 1) (hk : dot4 y N ≠ 1) :
    y = (dot4 (stereographicFrom N y) (stereographicFrom N y) + 1)⁻¹ •
      ((2 : ℝ) • stereographicFrom N y +
        (dot4 (stereographicFrom N y) (stereographicFrom N y) - 1) • N) := by
  obtain ⟨k, hkeq⟩ : ∃ k, dot4 y N = k := ⟨_, rfl⟩
  rw [hkeq] at hk
  have h1k : 1 - k ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have hst : stereographicFrom N y = (1 - k)⁻¹ • (y - k • N) := by
    rw [stereographicFrom, hkeq]
  have hpp : dot4 (stereographicFrom N y) (stereographicFrom N y) = (1 + k) / (1 - k) := by
    rw [hst]
    simp only [gl_dot4_smul_left, gl_dot4_smul_right, gl_dot4_sub_left,
      gl_dot4_sub_right, hy, hN, gl_dot4_comm N y, hkeq]
    field_simp
    ring
  rw [hpp, hst]
  have h2 : (1 + k) / (1 - k) + 1 = 2 / (1 - k) := by field_simp; ring
  rw [h2]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

lemma gl_stereo_injective {N y₁ y₂ : R4} (hN : dot4 N N = 1) (hy₁ : dot4 y₁ y₁ = 1)
    (hy₂ : dot4 y₂ y₂ = 1) (hk₁ : dot4 y₁ N ≠ 1) (hk₂ : dot4 y₂ N ≠ 1)
    (h : stereographicFrom N y₁ = stereographicFrom N y₂) : y₁ = y₂ := by
  rw [gl_stereo_inv hN hy₁ hk₁, gl_stereo_inv hN hy₂ hk₂, h]

/-! ### Moving the pole -/

theorem gl_gauss_pole_path (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    (P : ℝ → R4) (hP : ContDiff ℝ 2 P) (hPunit : ∀ τ, euclidNorm (P τ) = 1)
    (hPγ : ∀ τ s, γ₁ s ≠ P τ ∧ γ₂ s ≠ P τ) (hopp : ∀ τ, P τ + P 0 ≠ 0) :
    gaussLinkingIntegral (P 0) γ₁ γ₂ = gaussLinkingIntegral (P 1) γ₁ γ₂ := by
  set N := P 0 with hNdef
  have hPP : ∀ τ, dot4 (P τ) (P τ) = 1 := fun τ => gl_dot4_self_of_unit (hPunit τ)
  have hNN : dot4 N N = 1 := hPP 0
  have hP0 : ∀ τ, dot4 (P τ) (P τ) ≠ 0 := fun τ => by rw [hPP]; norm_num
  have hPN : ∀ τ, dot4 (P τ + N) (P τ + N) ≠ 0 := fun τ => (gl_dot4_self_pos (hopp τ)).ne'
  have hg₁ : ∀ s, dot4 (γ₁ s) (γ₁ s) = 1 := fun s => gl_dot4_self_of_unit (hunit₁ s)
  have hg₂ : ∀ s, dot4 (γ₂ s) (γ₂ s) = 1 := fun s => gl_dot4_self_of_unit (hunit₂ s)
  set R : ℝ → R4 → R4 := fun τ x => gl_rot (P τ) N x
  have hRP : ∀ τ, R τ (P τ) = N := fun τ => gl_rot_self (hPP τ) hNN (hPN τ)
  -- rotated points are unit and avoid `N`
  have hRk : ∀ τ y, dot4 y y = 1 → y ≠ P τ → dot4 (R τ y) N ≠ 1 := by
    intro τ y hy hyP h
    have hRy : dot4 (R τ y) (R τ y) = 1 := by simp only [R, gl_rot_dot (hP0 τ) (hPN τ), hy]
    apply hyP
    apply gl_rot_injective (hP0 τ) (hPN τ)
    exact (gl_eq_of_dot4_eq_one hRy hNN h).trans (hRP τ).symm
  have hRk₁ : ∀ τ s, 1 - dot4 (R τ (γ₁ s)) N ≠ 0 := fun τ s =>
    sub_ne_zero.2 (Ne.symm (hRk τ _ (hg₁ s) (hPγ τ s).1))
  have hRk₂ : ∀ τ s, 1 - dot4 (R τ (γ₂ s)) N ≠ 0 := fun τ s =>
    sub_ne_zero.2 (Ne.symm (hRk τ _ (hg₂ s) (hPγ τ s).2))
  set A : ℝ → ℝ → R4 := fun τ s => stereographicFrom N (R τ (γ₁ s))
  set B : ℝ → ℝ → R4 := fun τ t => stereographicFrom N (R τ (γ₂ t))
  have cP : ContDiff ℝ 2 fun p : ℝ × ℝ => P p.1 := hP.comp contDiff_fst
  have cN : ContDiff ℝ 2 fun p : ℝ × ℝ => P p.1 + N := cP.add contDiff_const
  have hA : ContDiff ℝ 2 (Function.uncurry A) :=
    gl_contDiff_stereo N (gl_contDiff_refl cN (gl_contDiff_refl cP (h₁.comp contDiff_snd)
      fun p => hP0 p.1) fun p => hPN p.1) fun p => hRk₁ p.1 p.2
  have hB : ContDiff ℝ 2 (Function.uncurry B) :=
    gl_contDiff_stereo N (gl_contDiff_refl cN (gl_contDiff_refl cP (h₂.comp contDiff_snd)
      fun p => hP0 p.1) fun p => hPN p.1) fun p => hRk₂ p.1 p.2
  have hAper : ∀ τ s, A τ (s + 1) = A τ s := fun τ s => by simp only [A, hper₁]
  have hBper : ∀ τ t, B τ (t + 1) = B τ t := fun τ t => by simp only [B, hper₂]
  have hperp : ∀ τ s t, dot4 (A τ s - B τ t) N = 0 := fun τ s t => by
    rw [gl_dot4_sub_left, gl_stereo_dot_N hNN, gl_stereo_dot_N hNN, sub_zero]
  have hne : ∀ τ s t, A τ s ≠ B τ t := by
    intro τ s t h
    have hR1 : dot4 (R τ (γ₁ s)) (R τ (γ₁ s)) = 1 := by
      simp only [R, gl_rot_dot (hP0 τ) (hPN τ), hg₁]
    have hR2 : dot4 (R τ (γ₂ t)) (R τ (γ₂ t)) = 1 := by
      simp only [R, gl_rot_dot (hP0 τ) (hPN τ), hg₂]
    exact hdisj s t (gl_rot_injective (hP0 τ) (hPN τ)
      (gl_stereo_injective hNN hR1 hR2 (hRk τ _ (hg₁ s) (hPγ τ s).1)
        (hRk τ _ (hg₂ t) (hPγ τ t).2) h))
  have hmain := gl_gauss_homotopy N A B hA hB hAper hBper hperp hne
  -- identify each end with the Gauss integral from the pole `P τ`
  have hend : ∀ τ, gaussLinkingIntegral (P τ) γ₁ γ₂ = (4 * Real.pi)⁻¹ *
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        gl_integrand N (deriv (A τ) s) (deriv (B τ) t) (A τ s - B τ t) := by
    intro τ
    have hk₁ : ∀ s, 1 - dot4 (γ₁ s) (P τ) ≠ 0 := fun s h0 =>
      (hPγ τ s).1 (gl_eq_of_dot4_eq_one (hg₁ s) (hPP τ) (by linarith))
    have hk₂ : ∀ s, 1 - dot4 (γ₂ s) (P τ) ≠ 0 := fun s h0 =>
      (hPγ τ s).2 (gl_eq_of_dot4_eq_one (hg₂ s) (hPP τ) (by linarith))
    have d₁ : Differentiable ℝ fun s => stereographicFrom (P τ) (γ₁ s) :=
      (gl_contDiff_stereo (P τ) h₁ hk₁).differentiable (by norm_num)
    have d₂ : Differentiable ℝ fun s => stereographicFrom (P τ) (γ₂ s) :=
      (gl_contDiff_stereo (P τ) h₂ hk₂).differentiable (by norm_num)
    have hRP' : gl_rot (P τ) N (P τ) = N := hRP τ
    have eA : A τ = fun s => R τ (stereographicFrom (P τ) (γ₁ s)) := by
      funext s
      have h := gl_rot_stereo (hP0 τ) (hPN τ) (P τ) (γ₁ s)
      rw [hRP'] at h
      exact h
    have eB : B τ = fun t => R τ (stereographicFrom (P τ) (γ₂ t)) := by
      funext t
      have h := gl_rot_stereo (hP0 τ) (hPN τ) (P τ) (γ₂ t)
      rw [hRP'] at h
      exact h
    have hv : ∀ x y z, volumeIn N (gl_rot (P τ) N x) (gl_rot (P τ) N y) (gl_rot (P τ) N z) =
        volumeIn (P τ) x y z := by
      intro x y z
      have h := gl_rot_volumeIn (hP0 τ) (hPN τ) (P τ) x y z
      rw [hRP'] at h
      exact h
    have dA : ∀ s, deriv (A τ) s = R τ (deriv (fun s => stereographicFrom (P τ) (γ₁ s)) s) :=
      fun s => by
        rw [eA]; exact (gl_hasDerivAt_rot (hP0 τ) (hPN τ) (d₁ s).hasDerivAt).deriv
    have dB : ∀ t, deriv (B τ) t = R τ (deriv (fun t => stereographicFrom (P τ) (γ₂ t)) t) :=
      fun t => by
        rw [eB]; exact (gl_hasDerivAt_rot (hP0 τ) (hPN τ) (d₂ t).hasDerivAt).deriv
    rw [gaussLinkingIntegral]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => intervalIntegral.integral_congr fun t _ => ?_
    simp only [dA, dB, gl_integrand]
    rw [eA, eB]
    simp only [R]
    rw [← gl_rot_sub (hP0 τ) (hPN τ), gl_rot_euclidNorm (hP0 τ) (hPN τ), hv]
  rw [hend 0, hend 1, hmain]

end HryniewiczCriterion

/-!
# Pole independence of the Gauss linking integral

Two poles `N, N'` are joined through a generic midpoint `M`: the normalized segments
`N → M` and `N' → M` miss both loops and the antipodes `-N`, `-N'`, because the bad
midpoints lie in images of null sets under differentiable maps.
-/


noncomputable section

namespace HryniewiczCriterion

/-! ### Bad midpoints form a null set -/

lemma gl_hyperplane_null : volume {p : R4 | p 3 = 0} = 0 := by
  let S : Submodule ℝ R4 := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3)
  have hS : (S : Set R4) = {p : R4 | p 3 = 0} := by
    ext p; simp [S]
  rw [← hS]
  refine Measure.addHaar_submodule volume S ?_
  intro htop
  have h : (Pi.single 3 1 : R4) ∈ S := htop ▸ Submodule.mem_top
  simp [S] at h

/-- Midpoints `M` with `(1-λ) N + λ M = c g(s)` for some `λ > 0` form a null set. -/
lemma gl_bad_null (g : ℝ → R4) (hg : Differentiable ℝ g) (N : R4) :
    volume {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • g s - (1 - l) • N)} = 0 := by
  set F : R4 → R4 := fun p => (p 0)⁻¹ • (p 1 • g (p 2) - (1 - p 0) • N)
  set S : Set R4 := {p : R4 | 0 < p 0 ∧ p 3 = 0}
  have hsub : {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • g s - (1 - l) • N)} ⊆ F '' S := by
    rintro M ⟨l, c, s, hl, rfl⟩
    refine ⟨![l, c, s, 0], ⟨by simpa using hl, by simp⟩, ?_⟩
    simp [F]
  have hS : volume S = 0 :=
    measure_mono_null (fun p hp => hp.2) gl_hyperplane_null
  have hF : DifferentiableOn ℝ F S := by
    intro p hp
    have h0 : p 0 ≠ 0 := hp.1.ne'
    have d0 : DifferentiableAt ℝ (fun p : R4 => p 0) p := differentiableAt_apply 0 p
    have d1 : DifferentiableAt ℝ (fun p : R4 => p 1) p := differentiableAt_apply 1 p
    have d2 : DifferentiableAt ℝ (fun p : R4 => g (p 2)) p :=
      (hg (p 2)).comp p (differentiableAt_apply 2 p)
    exact ((d0.inv h0).smul ((d1.smul d2).sub ((differentiableAt_const 1).sub d0 |>.smul
      (differentiableAt_const N)))).differentiableWithinAt
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF hS)

/-! ### Norms and normalization -/

lemma gl_euclidNorm_smul (c : ℝ) (v : R4) : euclidNorm (c • v) = |c| * euclidNorm v := by
  have h : dot4 (c • v) (c • v) = c ^ 2 * dot4 v v := by
    rw [gl_dot4_smul_left, gl_dot4_smul_right]; ring
  rw [euclidNorm, euclidNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma gl_euclidNorm_normalize {v : R4} (hv : v ≠ 0) : euclidNorm (radialNormalize v) = 1 := by
  have hp := gl_euclidNorm_pos hv
  rw [radialNormalize, gl_euclidNorm_smul, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']

lemma gl_normalize_of_unit {v : R4} (hv : euclidNorm v = 1) : radialNormalize v = v := by
  rw [radialNormalize, hv, inv_one, one_smul]

lemma gl_eq_smul_of_normalize {v y : R4} (hv : v ≠ 0) (h : radialNormalize v = y) :
    v = euclidNorm v • y := by
  rw [← h, radialNormalize, smul_smul, mul_inv_cancel₀ (gl_euclidNorm_pos hv).ne', one_smul]

/-! ### One segment -/

/-- Good midpoints: the segment `N → M` misses the cones over both loops and the ray `-N`. -/
def gl_GoodMid (γ₁ γ₂ : ℝ → R4) (N M : R4) : Prop :=
  (∀ l ∈ Icc (0 : ℝ) 1, ∀ c : ℝ, 0 < c → ∀ s,
    (1 - l) • N + l • M ≠ c • γ₁ s ∧ (1 - l) • N + l • M ≠ c • γ₂ s) ∧
  ∀ l ∈ Icc (0 : ℝ) 1, ∀ c : ℝ, 0 ≤ c → (1 - l) • N + l • M ≠ c • (-N)

lemma gl_segment_ne_zero {γ₁ γ₂ : ℝ → R4} {N M : R4} (hM : gl_GoodMid γ₁ γ₂ N M)
    {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : (1 - l) • N + l • M ≠ 0 := by
  have h := hM.2 l hl 0 le_rfl
  rwa [zero_smul] at h

theorem gl_gauss_segment (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) (N : R4) (hN : euclidNorm N = 1) (M : R4)
    (hM : gl_GoodMid γ₁ γ₂ N M) :
    gaussLinkingIntegral N γ₁ γ₂ = gaussLinkingIntegral (radialNormalize M) γ₁ γ₂ := by
  set h : ℝ → ℝ := fun τ => (1 - Real.cos (Real.pi * τ)) / 2
  have hmem : ∀ τ, h τ ∈ Icc (0 : ℝ) 1 := fun τ => by
    constructor <;> simp only [h] <;> linarith [Real.neg_one_le_cos (Real.pi * τ),
      Real.cos_le_one (Real.pi * τ)]
  set v : ℝ → R4 := fun τ => (1 - h τ) • N + h τ • M
  have hv0 : ∀ τ, v τ ≠ 0 := fun τ => gl_segment_ne_zero hM (hmem τ)
  set P : ℝ → R4 := fun τ => radialNormalize (v τ)
  have hh : ContDiff ℝ 2 h := by
    simp only [h]
    exact (contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const 2
  have hv : ContDiff ℝ 2 v :=
    ((contDiff_const.sub hh).smul contDiff_const).add (hh.smul contDiff_const)
  have hP : ContDiff ℝ 2 P := by
    simp only [P, radialNormalize, euclidNorm]
    have hq := gl_contDiff_dot4 hv hv
    have hq0 : ∀ τ, dot4 (v τ) (v τ) ≠ 0 := fun τ => (gl_dot4_self_pos (hv0 τ)).ne'
    exact ((hq.sqrt hq0).inv fun τ => (Real.sqrt_pos.2 (gl_dot4_self_pos (hv0 τ))).ne').smul hv
  have hPunit : ∀ τ, euclidNorm (P τ) = 1 := fun τ => gl_euclidNorm_normalize (hv0 τ)
  have h0 : h 0 = 0 := by simp [h]
  have h1 : h 1 = 1 := by simp [h]
  have hP0 : P 0 = N := by simp only [P, v, h0]; simp [gl_normalize_of_unit hN]
  have hP1 : P 1 = radialNormalize M := by simp only [P, v, h1]; simp
  have hPγ : ∀ τ s, γ₁ s ≠ P τ ∧ γ₂ s ≠ P τ := by
    intro τ s
    have hpos := gl_euclidNorm_pos (hv0 τ)
    constructor
    · intro he
      exact (hM.1 (h τ) (hmem τ) _ hpos s).1 (gl_eq_smul_of_normalize (hv0 τ) he.symm)
    · intro he
      exact (hM.1 (h τ) (hmem τ) _ hpos s).2 (gl_eq_smul_of_normalize (hv0 τ) he.symm)
  have hopp : ∀ τ, P τ + P 0 ≠ 0 := by
    intro τ he
    rw [hP0, add_eq_zero_iff_eq_neg] at he
    exact hM.2 (h τ) (hmem τ) _ (gl_euclidNorm_pos (hv0 τ)).le
      (gl_eq_smul_of_normalize (hv0 τ) he)
  have key := gl_gauss_pole_path γ₁ γ₂ h₁ h₂ hper₁ hper₂ hunit₁ hunit₂ hdisj P hP hPunit hPγ hopp
  rwa [hP0, hP1] at key

/-! ### Existence of a common good midpoint -/

lemma gl_goodMid_of_not_bad {γ₁ γ₂ : ℝ → R4} (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1)
    (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1) {N : R4} (hN : euclidNorm N = 1)
    (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) {M : R4}
    (hb₁ : M ∉ {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • γ₁ s - (1 - l) • N)})
    (hb₂ : M ∉ {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • γ₂ s - (1 - l) • N)})
    (hb₃ : M ∉ {M : R4 | ∃ l c s : ℝ, 0 < l ∧
      M = l⁻¹ • (c • (fun _ : ℝ => -N) s - (1 - l) • N)}) :
    gl_GoodMid γ₁ γ₂ N M := by
  have solve : ∀ {l : ℝ} {w : R4}, 0 < l → (1 - l) • N + l • M = w → M = l⁻¹ • (w - (1 - l) • N) := by
    intro l w hl he
    rw [← he, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  have unit_eq : ∀ {c : ℝ} {y : R4}, 0 < c → euclidNorm y = 1 → N = c • y → y = N := by
    intro c y hc hy he
    have hn := congrArg euclidNorm he
    rw [gl_euclidNorm_smul, hy, hN, abs_of_pos hc, mul_one] at hn
    rw [he, ← hn, one_smul]
  refine ⟨fun l hl c hc s => ⟨fun he => ?_, fun he => ?_⟩, fun l hl c hc he => ?_⟩
  · rcases hl.1.lt_or_eq with hl0 | hl0
    · exact hb₁ ⟨l, c, s, hl0, solve hl0 he⟩
    · subst hl0; simp at he
      exact (hNγ s).1 (unit_eq hc (hunit₁ s) he)
  · rcases hl.1.lt_or_eq with hl0 | hl0
    · exact hb₂ ⟨l, c, s, hl0, solve hl0 he⟩
    · subst hl0; simp at he
      exact (hNγ s).2 (unit_eq hc (hunit₂ s) he)
  · rcases hl.1.lt_or_eq with hl0 | hl0
    · exact hb₃ ⟨l, c, 0, hl0, solve hl0 he⟩
    · subst hl0; simp at he
      have hz : (1 + c) • N = 0 := by rw [add_smul, one_smul]; nth_rewrite 1 [he]; simp
      rcases smul_eq_zero.1 hz with h | h
      · linarith
      · rw [h] at hN; simp [euclidNorm, dot4] at hN

theorem gl_exists_goodMid (γ₁ γ₂ : ℝ → R4) (h₁ : Differentiable ℝ γ₁) (h₂ : Differentiable ℝ γ₂)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    {N N' : R4} (hN : euclidNorm N = 1) (hN' : euclidNorm N' = 1)
    (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) (hNγ' : ∀ s, γ₁ s ≠ N' ∧ γ₂ s ≠ N') :
    ∃ M, gl_GoodMid γ₁ γ₂ N M ∧ gl_GoodMid γ₁ γ₂ N' M := by
  set bad : R4 → (ℝ → R4) → Set R4 := fun N g =>
    {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • g s - (1 - l) • N)}
  have hc : ∀ N' : R4, Differentiable ℝ (fun _ : ℝ => -N') := fun _ => differentiable_const _
  set U := bad N γ₁ ∪ bad N γ₂ ∪ bad N (fun _ => -N) ∪
    (bad N' γ₁ ∪ bad N' γ₂ ∪ bad N' (fun _ => -N'))
  have hU : volume U = 0 := by
    simp only [U, measure_union_null_iff]
    exact ⟨⟨⟨gl_bad_null _ h₁ N, gl_bad_null _ h₂ N⟩, gl_bad_null _ (hc N) N⟩,
      ⟨⟨gl_bad_null _ h₁ N', gl_bad_null _ h₂ N'⟩, gl_bad_null _ (hc N') N'⟩⟩
  have hne : (Uᶜ).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hpos := isOpen_univ.measure_pos (volume : Measure R4) univ_nonempty
    rw [← hemp, hU] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨M, hM⟩ := hne
  simp only [U, mem_compl_iff, mem_union, not_or] at hM
  exact ⟨M, gl_goodMid_of_not_bad hunit₁ hunit₂ hN hNγ hM.1.1.1 hM.1.1.2 hM.1.2,
    gl_goodMid_of_not_bad hunit₁ hunit₂ hN' hNγ' hM.2.1.1 hM.2.1.2 hM.2.2⟩

/-! ### Pole independence -/

theorem gl_gauss_pole_indep (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    {N N' : R4} (hN : euclidNorm N = 1) (hN' : euclidNorm N' = 1)
    (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) (hNγ' : ∀ s, γ₁ s ≠ N' ∧ γ₂ s ≠ N') :
    gaussLinkingIntegral N γ₁ γ₂ = gaussLinkingIntegral N' γ₁ γ₂ := by
  obtain ⟨M, hM, hM'⟩ := gl_exists_goodMid γ₁ γ₂ (h₁.differentiable (by norm_num))
    (h₂.differentiable (by norm_num)) hunit₁ hunit₂ hN hN' hNγ hNγ'
  rw [gl_gauss_segment γ₁ γ₂ h₁ h₂ hper₁ hper₂ hunit₁ hunit₂ hdisj N hN M hM,
    gl_gauss_segment γ₁ γ₂ h₁ h₂ hper₁ hper₂ hunit₁ hunit₂ hdisj N' hN' M hM']

theorem isLinkingNumber_of_gaussLinkingIntegral_eq' (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N)
    (n : ℤ) (hG : gaussLinkingIntegral N γ₁ γ₂ = n) :
    IsLinkingNumber γ₁ γ₂ n :=
  ⟨⟨N, hN, hNγ⟩, fun N' hN' hNγ' => by
    rw [← gl_gauss_pole_indep γ₁ γ₂ h₁ h₂ hper₁ hper₂ hunit₁ hunit₂ hdisj hN hN' hNγ hNγ', hG]⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N)
    (n : ℤ) (hG : gaussLinkingIntegral N γ₁ γ₂ = n) :
    IsLinkingNumber γ₁ γ₂ n :=
  isLinkingNumber_of_gaussLinkingIntegral_eq' γ₁ γ₂ h₁ h₂ hper₁ hper₂ hunit₁ hunit₂ hdisj N hN hNγ n hG
