-- Prove2me | solution 1 for HryniewiczCriterion.gaussLinkingIntegral_strip_bump_jump
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T11:18:24.694414+00:00
-- url     : https://prove2.me/submissions/95fbcd44-615e-4c81-885c-347a3b4bd39e

import Definitions.Def_HryniewiczCriterion_GlobalSection
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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open HryniewiczCriterion
open scoped ContDiff
open MeasureTheory Set
open MeasureTheory Set Filter Topology
open Set
open Set Filter Topology

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
# Variation of the Gauss integral along a family of open arcs

Same set-up as `gl_gauss_homotopy`, except that `B τ` need not be closed: the
difference of the Gauss double integrals at `τ = 1` and `τ = 0` is the integral of the
boundary terms at `t = 0, 1`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The integral bookkeeping behind the variation formula. -/
lemma tw_variation_assemble {f F' Ps Qt : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (cf : Continuous fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
    (cF' : Continuous fun p : ℝ × ℝ × ℝ => F' p.1 p.2.1 p.2.2)
    (cPs : Continuous fun p : ℝ × ℝ × ℝ => Ps p.1 p.2.1 p.2.2)
    (cQt : Continuous fun p : ℝ × ℝ × ℝ => Qt p.1 p.2.1 p.2.2)
    (cW : Continuous fun p : ℝ × ℝ => W p.1 p.2)
    (S1 : ∀ s t, f 1 s t - f 0 s t = ∫ τ in (0 : ℝ)..1, F' τ s t)
    (hclosed : ∀ τ s t, F' τ s t = Ps τ s t - Qt τ s t)
    (S2 : ∀ τ t, ∫ s in (0 : ℝ)..1, Ps τ s t = 0)
    (S3 : ∀ τ s, ∫ t in (0 : ℝ)..1, Qt τ s t = W τ s) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 1 s t) -
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f 0 s t =
      -∫ τ in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, W τ s := by
  have int3 : ∀ {G : ℝ → ℝ → ℝ → ℝ}, (Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) →
      ∀ τ, Continuous fun s => ∫ t in (0 : ℝ)..1, G τ s t := by
    intro G hG τ
    exact gl_continuous_param (F := fun s t => G τ s t)
      (hG.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (τ, q.1, q.2)))
  have int3' : ∀ {G : ℝ → ℝ → ℝ → ℝ}, (Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) →
      ∀ τ s, Continuous fun t => G τ s t := by
    intro G hG τ s
    exact hG.comp (by fun_prop : Continuous fun t : ℝ => (τ, s, t))
  have step : ∀ τ, ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F' τ s t =
      -∫ s in (0 : ℝ)..1, W τ s := by
    intro τ
    have e : ∀ s, ∫ t in (0 : ℝ)..1, F' τ s t =
        (∫ t in (0 : ℝ)..1, Ps τ s t) - ∫ t in (0 : ℝ)..1, Qt τ s t := by
      intro s
      simp only [hclosed]
      exact intervalIntegral.integral_sub ((int3' cPs τ s).intervalIntegrable 0 1)
        ((int3' cQt τ s).intervalIntegrable 0 1)
    simp only [e, S3]
    rw [intervalIntegral.integral_sub (f := fun s => ∫ t in (0 : ℝ)..1, Ps τ s t)
      (g := fun s => W τ s) ((int3 cPs τ).intervalIntegrable 0 1)
      ((cW.comp (by fun_prop : Continuous fun s : ℝ => (τ, s))).intervalIntegrable 0 1)]
    rw [gl_integral_integral_swap_unit (f := fun s t => Ps τ s t)
      (cPs.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (τ, q.1, q.2)))]
    simp only [S2, intervalIntegral.integral_zero, zero_sub]
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
  simp only [step, intervalIntegral.integral_neg]

/-- Variation of the Gauss double integral when the second curve is a family of open arcs:
`A τ` closed (`1`-periodic), `B τ` arbitrary. -/
theorem tw_gauss_variation (N : R4) (A B : ℝ → ℝ → R4)
    (hA : ContDiff ℝ 2 (Function.uncurry A)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hAper : ∀ τ s, A τ (s + 1) = A τ s)
    (hN : ∀ τ s t, dot4 (A τ s - B τ t) N = 0) (hne : ∀ τ s t, A τ s ≠ B τ t) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        gl_integrand N (deriv (A 1) s) (deriv (B 1) t) (A 1 s - B 1 t)) -
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        gl_integrand N (deriv (A 0) s) (deriv (B 0) t) (A 0 s - B 0 t) =
      -∫ τ in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        (gl_integrand N (deriv (A τ) s)
            (fderiv ℝ (Function.uncurry A) (τ, s) (1, 0) - fderiv ℝ (Function.uncurry B) (τ, 1) (1, 0))
            (A τ s - B τ 1) -
          gl_integrand N (deriv (A τ) s)
            (fderiv ℝ (Function.uncurry A) (τ, s) (1, 0) - fderiv ℝ (Function.uncurry B) (τ, 0) (1, 0))
            (A τ s - B τ 0)) := by
  set DA := fderiv ℝ (Function.uncurry A)
  set DB := fderiv ℝ (Function.uncurry B)
  set D2A := fderiv ℝ DA
  set D2B := fderiv ℝ DB
  set e1 : ℝ × ℝ := (1, 0)
  set e2 : ℝ × ℝ := (0, 1)
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
  set W : ℝ → ℝ → ℝ := fun τ s =>
    gl_integrand N (As τ s) (c τ s 1) (u τ s 1) - gl_integrand N (As τ s) (c τ s 0) (u τ s 0)
  have hu0 : ∀ τ s t, u τ s t ≠ 0 := fun τ s t => sub_ne_zero.2 (hne τ s t)
  have hderA : ∀ τ s, deriv (A τ) s = As τ s := fun τ s => (gl_hasDerivAt_snd hA τ s).deriv
  have hderB : ∀ τ t, deriv (B τ) t = Bt τ t := fun τ t => (gl_hasDerivAt_snd hB τ t).deriv
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
  have cW : Continuous fun p : ℝ × ℝ => W p.1 p.2 := by
    have cAs : Continuous fun p : ℝ × ℝ => As p.1 p.2 := gl_continuous_fderiv_apply hA e2
    have ct : ∀ t₀ : ℝ, Continuous fun p : ℝ × ℝ =>
        gl_integrand N (As p.1 p.2) (c p.1 p.2 t₀) (u p.1 p.2 t₀) := by
      intro t₀
      have cc0 : Continuous fun p : ℝ × ℝ => c p.1 p.2 t₀ :=
        (gl_continuous_fderiv_apply hA e1).sub ((gl_continuous_fderiv_apply hB e1).comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => ((p.1, t₀) : ℝ × ℝ)))
      have cu0 : Continuous fun p : ℝ × ℝ => u p.1 p.2 t₀ :=
        hA.continuous.sub (hB.continuous.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => ((p.1, t₀) : ℝ × ℝ)))
      exact gl_continuous_integrand N cAs cc0 cu0 fun p => hu0 _ _ _
    exact (ct 1).sub (ct 0)
  have hclosed : ∀ τ s t, F' τ s t = Ps τ s t - Qt τ s t := fun τ s t =>
    gl_closed_identity N (As τ s) (Bt τ t) (c τ s t) (u τ s t) (X τ s) (Y τ t) (hN τ s t)
      (hu0 τ s t)
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
  have S3 : ∀ τ s, ∫ t in (0 : ℝ)..1, Qt τ s t = W τ s := by
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
  simp only [hderA, hderB]
  exact tw_variation_assemble cf cF' cPs cQt cW S1 hclosed S2 S3

end HryniewiczCriterion

/-!
# The torus twisting formula for the Gauss double integral

Let `Q t φ` be a `C²` torus (`1`-periodic in `t`, `2π`-periodic in `φ`) disjoint from a closed
curve `A`. For `θ` with `θ (t + 1) = θ t + 2πk`, the Gauss double integral of `A` with the
`(1, k)`-curve `t ↦ Q t (θ t)` equals that with `t ↦ Q t 0` plus `k` times that with the
meridian `φ ↦ Q 0 (2πφ)`. Proof: vary the open arcs `t ↦ Q t (τ θ t)`; only the boundary
terms at `t = 0, 1` survive, and they sweep the meridian from `θ 0` to `θ 0 + 2πk`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The raw Gauss double integral of two curves in `N^⊥` (without the factor `(4π)⁻¹`). -/
def tw_G (N : R4) (A B : ℝ → R4) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A s) (deriv B t) (A s - B t)

lemma tw_integrand_smul (N a b u : R4) (c : ℝ) :
    gl_integrand N a (c • b) u = c * gl_integrand N a b u := by
  simp only [gl_integrand, gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_integrand_zero_sub_smul (N a b u : R4) (c : ℝ) :
    gl_integrand N a (0 - c • b) u = -(c * gl_integrand N a b u) := by
  simp only [gl_integrand, gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.zero_apply]
  ring

theorem tw_torus_twist_R3 (N : R4) (A : ℝ → R4) (Q : ℝ → ℝ → R4)
    (hA : ContDiff ℝ 2 A) (hQ : ContDiff ℝ 2 (Function.uncurry Q))
    (hAper : ∀ s, A (s + 1) = A s) (hQper₁ : ∀ t φ, Q (t + 1) φ = Q t φ)
    (hQper₂ : ∀ t φ, Q t (φ + 2 * Real.pi) = Q t φ)
    (hN : ∀ s t φ, dot4 (A s - Q t φ) N = 0) (hne : ∀ s t φ, A s ≠ Q t φ)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 2 θ) (k : ℤ) (hθper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * k) :
    tw_G N A (fun t => Q t (θ t)) =
      tw_G N A (fun t => Q t 0) + k * tw_G N A (fun φ => Q 0 (2 * Real.pi * φ)) := by
  set Qφ : ℝ → ℝ → R4 := fun t φ => fderiv ℝ (Function.uncurry Q) (t, φ) (0, 1) with hQφ
  have hQφd : ∀ t φ, HasDerivAt (Q t) (Qφ t φ) φ := fun t φ => gl_hasDerivAt_snd hQ t φ
  -- periodicity of `Q 0` and of its derivative
  have hQ10 : ∀ φ, Q 1 φ = Q 0 φ := fun φ => by simpa using hQper₁ 0 φ
  have hQφ10 : ∀ φ, Qφ 1 φ = Qφ 0 φ := by
    intro φ
    have h := hQφd 1 φ
    have e : Q 1 = Q 0 := funext hQ10
    rw [e] at h
    exact h.unique (hQφd 0 φ)
  have hQ0per : ∀ φ, Q 0 (φ + 2 * Real.pi) = Q 0 φ := fun φ => hQper₂ 0 φ
  have hQφ0per : ∀ φ, Qφ 0 (φ + 2 * Real.pi) = Qφ 0 φ := by
    intro φ
    have h := (hQφd 0 (φ + 2 * Real.pi)).comp_add_const φ (2 * Real.pi)
    have e : (fun x => Q 0 (x + 2 * Real.pi)) = Q 0 := funext hQ0per
    rw [e] at h
    exact h.unique (hQφd 0 φ)
  -- continuity
  have cdA : Continuous (deriv A) := hA.continuous_deriv (by norm_num)
  have cQ : Continuous (Function.uncurry Q) := hQ.continuous
  have cQφ : Continuous fun p : ℝ × ℝ => Qφ p.1 p.2 := gl_continuous_fderiv_apply hQ (0, 1)
  set F : ℝ → ℝ → ℝ := fun φ s => gl_integrand N (deriv A s) (Qφ 0 φ) (A s - Q 0 φ) with hF
  have cF : Continuous fun p : ℝ × ℝ => F p.1 p.2 :=
    gl_continuous_integrand N (cdA.comp continuous_snd)
      (cQφ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((0 : ℝ), p.1)))
      (hA.continuous.comp continuous_snd |>.sub
        (cQ.comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((0 : ℝ), p.1))))
      fun p => sub_ne_zero.2 (hne _ _ _)
  set g : ℝ → ℝ := fun φ => ∫ s in (0 : ℝ)..1, F φ s with hg
  have cg : Continuous g := gl_continuous_param cF
  have gper : Function.Periodic g (2 * Real.pi) := by
    intro φ
    simp only [g, F, hQ0per, hQφ0per]
  have gint : ∀ a b, IntervalIntegrable g volume a b := fun a b => cg.intervalIntegrable a b
  -- the variation of the open arcs `t ↦ Q t (τ θ t)`
  set Af : ℝ → ℝ → R4 := fun _ s => A s
  set Bf : ℝ → ℝ → R4 := fun τ t => Q t (τ * θ t)
  have hAf : ContDiff ℝ 2 (Function.uncurry Af) := hA.comp contDiff_snd
  have hBf : ContDiff ℝ 2 (Function.uncurry Bf) := by
    have e : Function.uncurry Bf = Function.uncurry Q ∘ fun p : ℝ × ℝ => (p.2, p.1 * θ p.2) :=
      funext fun p => rfl
    rw [e]
    exact hQ.comp (contDiff_snd.prodMk (contDiff_fst.mul (hθ.comp contDiff_snd)))
  have hvar := tw_gauss_variation N Af Bf hAf hBf (fun _ s => hAper s)
    (fun _ s t => hN s t _) (fun _ s t => hne s t _)
  have hDA : ∀ τ s, fderiv ℝ (Function.uncurry Af) (τ, s) (1, 0) = 0 := fun τ s =>
    ((gl_hasDerivAt_fst hAf τ s).unique (hasDerivAt_const τ (A s)))
  have hDB : ∀ τ t, fderiv ℝ (Function.uncurry Bf) (τ, t) (1, 0) = θ t • Qφ t (τ * θ t) := by
    intro τ t
    have h1 := gl_hasDerivAt_fst hBf τ t
    have h2 : HasDerivAt (fun τ => Q t (τ * θ t)) (θ t • Qφ t (τ * θ t)) τ :=
      (hQφd t (τ * θ t)).scomp τ (hasDerivAt_mul_const (θ t))
    exact h1.unique h2
  have eB1 : Bf 1 = fun t => Q t (θ t) := funext fun t => by simp only [Bf, one_mul]
  have eB0 : Bf 0 = fun t => Q t 0 := funext fun t => by simp only [Bf, zero_mul]
  have eA : ∀ τ, Af τ = A := fun τ => rfl
  simp only [eB1, eB0, eA, hDA, hDB] at hvar
  -- boundary terms
  have hθ1 : θ 1 = θ 0 + 2 * Real.pi * k := by simpa using hθper 0
  have hb : ∀ τ, (∫ s in (0 : ℝ)..1,
      (gl_integrand N (deriv A s) (0 - θ 1 • Qφ 1 (τ * θ 1)) (A s - Bf τ 1) -
        gl_integrand N (deriv A s) (0 - θ 0 • Qφ 0 (τ * θ 0)) (A s - Bf τ 0))) =
      -(θ 1 * g (θ 1 * τ)) + θ 0 * g (θ 0 * τ) := by
    intro τ
    have eb1 : ∀ s, gl_integrand N (deriv A s) (0 - θ 1 • Qφ 1 (τ * θ 1)) (A s - Bf τ 1) =
        -(θ 1 * F (θ 1 * τ) s) := by
      intro s
      simp only [Bf, hQ10, hQφ10, tw_integrand_zero_sub_smul, F, mul_comm τ]
    have eb0 : ∀ s, gl_integrand N (deriv A s) (0 - θ 0 • Qφ 0 (τ * θ 0)) (A s - Bf τ 0) =
        -(θ 0 * F (θ 0 * τ) s) := by
      intro s
      simp only [Bf, tw_integrand_zero_sub_smul, F, mul_comm τ]
    simp only [eb1, eb0]
    have ci : ∀ c : ℝ, IntervalIntegrable (fun s => -(c * F (c * τ) s)) volume 0 1 := fun c =>
      ((cF.comp (by fun_prop : Continuous fun s : ℝ => (c * τ, s))).const_smul c).neg.intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub (ci _) (ci _), intervalIntegral.integral_neg,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  simp only [hb] at hvar
  -- integrate in `τ`
  have hτ : ∀ c : ℝ, ∫ τ in (0 : ℝ)..1, c * g (c * τ) = ∫ φ in (0 : ℝ)..c, g φ := by
    intro c
    rw [intervalIntegral.integral_const_mul, intervalIntegral.mul_integral_comp_mul_left]
    simp
  have hsum : ∫ τ in (0 : ℝ)..1, (-(θ 1 * g (θ 1 * τ)) + θ 0 * g (θ 0 * τ)) =
      -((∫ φ in (0 : ℝ)..θ 1, g φ) - ∫ φ in (0 : ℝ)..θ 0, g φ) := by
    have ci : ∀ c : ℝ, IntervalIntegrable (fun τ => c * g (c * τ)) volume 0 1 := fun c =>
      ((cg.comp (continuous_const.mul continuous_id)).const_smul c).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add (f := fun τ => -(θ 1 * g (θ 1 * τ)))
      (g := fun τ => θ 0 * g (θ 0 * τ)) (ci _).neg (ci _), intervalIntegral.integral_neg, hτ, hτ]
    ring
  rw [hsum, intervalIntegral.integral_interval_sub_left (gint _ _) (gint _ _), hθ1] at hvar
  have hk : ∫ φ in θ 0..θ 0 + 2 * Real.pi * k, g φ = k * ∫ φ in (0 : ℝ)..2 * Real.pi, g φ := by
    have h := gper.intervalIntegral_add_zsmul_eq k (θ 0) gint
    rw [zsmul_eq_mul, gper.intervalIntegral_add_eq (θ 0) 0, zero_add] at h
    rw [show θ 0 + 2 * Real.pi * k = θ 0 + k * (2 * Real.pi) by ring, h, zsmul_eq_mul]
  rw [hk, neg_neg] at hvar
  -- the meridian
  have hmer : tw_G N A (fun φ => Q 0 (2 * Real.pi * φ)) = ∫ φ in (0 : ℝ)..2 * Real.pi, g φ := by
    have hd : ∀ φ, deriv (fun φ => Q 0 (2 * Real.pi * φ)) φ =
        (2 * Real.pi) • Qφ 0 (2 * Real.pi * φ) := fun φ =>
      ((hQφd 0 (2 * Real.pi * φ)).scomp φ (hasDerivAt_const_mul (2 * Real.pi))).deriv
    simp only [tw_G, hd, tw_integrand_smul]
    have e : ∀ s, ∫ φ in (0 : ℝ)..1, 2 * Real.pi *
        gl_integrand N (deriv A s) (Qφ 0 (2 * Real.pi * φ)) (A s - Q 0 (2 * Real.pi * φ)) =
        ∫ φ in (0 : ℝ)..1, 2 * Real.pi * F (2 * Real.pi * φ) s := fun s => rfl
    rw [intervalIntegral.integral_congr fun s _ => e s]
    have cM : Continuous fun p : ℝ × ℝ => 2 * Real.pi * F (2 * Real.pi * p.2) p.1 :=
      continuous_const.mul (cF.comp (f := fun p : ℝ × ℝ => ((2 * Real.pi * p.2, p.1) : ℝ × ℝ))
        (by fun_prop))
    rw [gl_integral_integral_swap_unit (f := fun s φ => 2 * Real.pi * F (2 * Real.pi * φ) s) cM]
    have e2 : ∀ φ, ∫ s in (0 : ℝ)..1, 2 * Real.pi * F (2 * Real.pi * φ) s =
        2 * Real.pi * g (2 * Real.pi * φ) := fun φ => intervalIntegral.integral_const_mul _ _
    simp only [e2]
    rw [hτ]
  rw [hmer]
  unfold tw_G
  linarith

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
# Homotopy invariance and the torus twisting formula on `S³`

The `ℝ³` statements `gl_gauss_homotopy` and `tw_torus_twist_R3`, transported to loops on the
unit sphere through stereographic projection from a fixed pole `N`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma tw_gauss_eq_G (N : R4) (γ₁ γ₂ : ℝ → R4) :
    gaussLinkingIntegral N γ₁ γ₂ = (4 * Real.pi)⁻¹ *
      tw_G N (fun s => stereographicFrom N (γ₁ s)) (fun t => stereographicFrom N (γ₂ t)) := rfl

lemma tw_one_sub_dot_ne {N y : R4} (hN : euclidNorm N = 1) (hy : euclidNorm y = 1) (hyN : y ≠ N) :
    1 - dot4 y N ≠ 0 := fun h0 =>
  hyN (gl_eq_of_dot4_eq_one (gl_dot4_self_of_unit hy) (gl_dot4_self_of_unit hN) (by linarith))

lemma tw_stereo_ne {N y₁ y₂ : R4} (hN : euclidNorm N = 1) (hy₁ : euclidNorm y₁ = 1)
    (hy₂ : euclidNorm y₂ = 1) (h₁ : y₁ ≠ N) (h₂ : y₂ ≠ N) (hne : y₁ ≠ y₂) :
    stereographicFrom N y₁ ≠ stereographicFrom N y₂ := fun h =>
  hne (gl_stereo_injective (gl_dot4_self_of_unit hN) (gl_dot4_self_of_unit hy₁)
    (gl_dot4_self_of_unit hy₂) (fun e => (tw_one_sub_dot_ne hN hy₁ h₁) (by rw [e]; ring))
    (fun e => (tw_one_sub_dot_ne hN hy₂ h₂) (by rw [e]; ring)) h)

/-- Homotopy invariance on `S³` with a fixed pole: the second loop moves through a `C²` family
of closed loops missing the first loop and the pole. -/
theorem tw_gauss_homotopy_S3 (N : R4) (hN : euclidNorm N = 1) (γ : ℝ → R4) (R : ℝ → ℝ → R4)
    (hγ : ContDiff ℝ 2 γ) (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hγper : ∀ s, γ (s + 1) = γ s) (hRper : ∀ τ t, R τ (t + 1) = R τ t)
    (hγunit : ∀ s, euclidNorm (γ s) = 1) (hRunit : ∀ τ t, euclidNorm (R τ t) = 1)
    (hγN : ∀ s, γ s ≠ N) (hRN : ∀ τ t, R τ t ≠ N) (hne : ∀ τ s t, γ s ≠ R τ t) :
    gaussLinkingIntegral N γ (R 0) = gaussLinkingIntegral N γ (R 1) := by
  have hNN : dot4 N N = 1 := gl_dot4_self_of_unit hN
  set A : ℝ → ℝ → R4 := fun _ s => stereographicFrom N (γ s)
  set B : ℝ → ℝ → R4 := fun τ t => stereographicFrom N (R τ t)
  have hA : ContDiff ℝ 2 (Function.uncurry A) :=
    gl_contDiff_stereo N (hγ.comp contDiff_snd) fun p => tw_one_sub_dot_ne hN (hγunit _) (hγN _)
  have hB : ContDiff ℝ 2 (Function.uncurry B) :=
    gl_contDiff_stereo N hR fun p => tw_one_sub_dot_ne hN (hRunit _ _) (hRN _ _)
  have h := gl_gauss_homotopy N A B hA hB (fun _ s => by simp only [A, hγper])
    (fun τ t => by simp only [B, hRper])
    (fun τ s t => by rw [gl_dot4_sub_left, gl_stereo_dot_N hNN, gl_stereo_dot_N hNN, sub_zero])
    (fun τ s t => tw_stereo_ne hN (hγunit s) (hRunit τ t) (hγN s) (hRN τ t) (hne τ s t))
  rw [tw_gauss_eq_G, tw_gauss_eq_G]
  exact congrArg (fun x => (4 * Real.pi)⁻¹ * x) h

/-- The torus twisting formula on `S³`. -/
theorem tw_torus_twist_S3 (N : R4) (hN : euclidNorm N = 1) (γ : ℝ → R4) (P : ℝ → ℝ → R4)
    (hγ : ContDiff ℝ 2 γ) (hP : ContDiff ℝ 2 (Function.uncurry P))
    (hγper : ∀ s, γ (s + 1) = γ s) (hPper₁ : ∀ t φ, P (t + 1) φ = P t φ)
    (hPper₂ : ∀ t φ, P t (φ + 2 * Real.pi) = P t φ)
    (hγunit : ∀ s, euclidNorm (γ s) = 1) (hPunit : ∀ t φ, euclidNorm (P t φ) = 1)
    (hγN : ∀ s, γ s ≠ N) (hPN : ∀ t φ, P t φ ≠ N) (hne : ∀ s t φ, γ s ≠ P t φ)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 2 θ) (k : ℤ) (hθper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * k) :
    gaussLinkingIntegral N γ (fun t => P t (θ t)) =
      gaussLinkingIntegral N γ (fun t => P t 0) +
        k * gaussLinkingIntegral N γ (fun φ => P 0 (2 * Real.pi * φ)) := by
  have hNN : dot4 N N = 1 := gl_dot4_self_of_unit hN
  set A : ℝ → R4 := fun s => stereographicFrom N (γ s)
  set Q : ℝ → ℝ → R4 := fun t φ => stereographicFrom N (P t φ)
  have hA : ContDiff ℝ 2 A :=
    gl_contDiff_stereo N hγ fun s => tw_one_sub_dot_ne hN (hγunit _) (hγN _)
  have hQ : ContDiff ℝ 2 (Function.uncurry Q) :=
    gl_contDiff_stereo N hP fun p => tw_one_sub_dot_ne hN (hPunit _ _) (hPN _ _)
  have h := tw_torus_twist_R3 N A Q hA hQ (fun s => by simp only [A, hγper])
    (fun t φ => by simp only [Q, hPper₁]) (fun t φ => by simp only [Q, hPper₂])
    (fun s t φ => by rw [gl_dot4_sub_left, gl_stereo_dot_N hNN, gl_stereo_dot_N hNN, sub_zero])
    (fun s t φ => tw_stereo_ne hN (hγunit s) (hPunit t φ) (hγN s) (hPN t φ) (hne s t φ))
    θ hθ k hθper
  rw [tw_gauss_eq_G, tw_gauss_eq_G, tw_gauss_eq_G]
  have e : ∀ x y z : ℝ, x = y + k * z →
      (4 * Real.pi)⁻¹ * x = (4 * Real.pi)⁻¹ * y + k * ((4 * Real.pi)⁻¹ * z) := by
    intro x y z hx; rw [hx]; ring
  exact e _ _ _ h

end HryniewiczCriterion

/-!
# The lens identity for the chart Gauss integral

If `Λ` runs along `A₁ ∘ s` on `[0, ½]` and along `A₀ ∘ s` on `[½, 1]`, where
`s(σ) = s₀ - d cos 2πσ` sweeps `[s₀ - d, s₀ + d]` forth and back, and `A₁ = A₀` off that window,
then `G(Λ) = G(A₁) - G(A₀)`: substitute `x = s(σ)` on each half of the outer integral.
-/


noncomputable section

namespace HryniewiczCriterion

lemma jl_integrand_smul_first (N a b u : R4) (c : ℝ) :
    gl_integrand N (c • a) b u = c * gl_integrand N a b u := by
  simp only [gl_integrand, gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]
  ring

/-- The sweep `s₀ - d cos 2πσ`. -/
def jl_sweep (s₀ d σ : ℝ) : ℝ := s₀ - d * Real.cos (2 * Real.pi * σ)

lemma jl_sweep_hasDerivAt (s₀ d σ : ℝ) :
    HasDerivAt (jl_sweep s₀ d) (d * (2 * Real.pi * Real.sin (2 * Real.pi * σ))) σ := by
  have h := (((Real.hasDerivAt_cos (2 * Real.pi * σ)).comp σ
    ((hasDerivAt_id' σ).const_mul (2 * Real.pi))).const_mul d).const_sub s₀
  refine h.congr_deriv ?_
  ring

lemma jl_inner_continuous (N : R4) {A B : ℝ → R4} (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hAB : ∀ x t, A x - B t ≠ 0) :
    Continuous fun x => ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A x) (deriv B t) (A x - B t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact gl_continuous_integrand N ((hA.continuous_deriv le_rfl).comp continuous_fst)
    ((hB.continuous_deriv le_rfl).comp continuous_snd)
    ((hA.continuous.comp continuous_fst).sub (hB.continuous.comp continuous_snd))
    fun p => hAB p.1 p.2

lemma jl_inner_periodic (N : R4) {A B : ℝ → R4} (hAper : ∀ x, A (x + 1) = A x) :
    Function.Periodic (fun x => ∫ t in (0 : ℝ)..1,
      gl_integrand N (deriv A x) (deriv B t) (A x - B t)) 1 := by
  intro x
  have h' : deriv A (x + 1) = deriv A x := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f x) (funext hAper)
  simp only [hAper x, h']

/-- One half of the lens: substitution `x = s(σ)`. -/
lemma jl_half (N : R4) {A B Λ : ℝ → R4} (s₀ d a b : ℝ) (hA : ContDiff ℝ 1 A)
    (hB : ContDiff ℝ 1 B) (hAB : ∀ x t, A x - B t ≠ 0) (hab : a ≤ b)
    (hΛ : ∀ σ ∈ Icc a b, Λ =ᶠ[𝓝 σ] fun σ => A (jl_sweep s₀ d σ)) :
    (∫ σ in a..b, ∫ t in (0 : ℝ)..1, gl_integrand N (deriv Λ σ) (deriv B t) (Λ σ - B t)) =
      ∫ x in jl_sweep s₀ d a..jl_sweep s₀ d b,
        ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A x) (deriv B t) (A x - B t) := by
  set J := fun x => ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A x) (deriv B t) (A x - B t)
  have hJc : Continuous J := jl_inner_continuous N hA hB hAB
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hpt : ∀ σ ∈ uIcc a b, (∫ t in (0 : ℝ)..1,
      gl_integrand N (deriv Λ σ) (deriv B t) (Λ σ - B t)) =
      (J ∘ jl_sweep s₀ d) σ * (d * (2 * Real.pi * Real.sin (2 * Real.pi * σ))) := by
    intro σ hσ
    rw [uIcc_of_le hab] at hσ
    have he := hΛ σ hσ
    have hv : Λ σ = A (jl_sweep s₀ d σ) := he.self_of_nhds
    have hd : deriv Λ σ = (d * (2 * Real.pi * Real.sin (2 * Real.pi * σ))) •
        deriv A (jl_sweep s₀ d σ) := by
      rw [he.deriv_eq]
      exact ((hAd _).hasDerivAt.scomp σ (jl_sweep_hasDerivAt s₀ d σ)).deriv
    simp only [hv, hd, jl_integrand_smul_first, J, Function.comp_apply]
    rw [intervalIntegral.integral_const_mul, mul_comm]
  rw [intervalIntegral.integral_congr hpt]
  exact intervalIntegral.integral_comp_mul_deriv (fun x _ => jl_sweep_hasDerivAt s₀ d x)
    (by fun_prop) hJc

theorem jl_lens (N : R4) (A₁ A₀ B Λ : ℝ → R4) (s₀ d : ℝ) (hd : d ≤ 1 / 2)
    (hA₁ : ContDiff ℝ 1 A₁) (hA₀ : ContDiff ℝ 1 A₀) (hB : ContDiff ℝ 1 B) (hΛc : ContDiff ℝ 1 Λ)
    (hA₁per : ∀ x, A₁ (x + 1) = A₁ x) (hA₀per : ∀ x, A₀ (x + 1) = A₀ x)
    (h₁B : ∀ x t, A₁ x - B t ≠ 0) (h₀B : ∀ x t, A₀ x - B t ≠ 0) (hΛB : ∀ x t, Λ x - B t ≠ 0)
    (hagree : ∀ x ∈ Icc (s₀ + d) (s₀ - d + 1), A₁ =ᶠ[𝓝 x] A₀)
    (hΛ₁ : ∀ σ ∈ Icc (0 : ℝ) (1 / 2), Λ =ᶠ[𝓝 σ] fun σ => A₁ (jl_sweep s₀ d σ))
    (hΛ₀ : ∀ σ ∈ Icc (1 / 2 : ℝ) 1, Λ =ᶠ[𝓝 σ] fun σ => A₀ (jl_sweep s₀ d σ)) :
    tw_G N Λ B = tw_G N A₁ B - tw_G N A₀ B := by
  set J₁ := fun x => ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A₁ x) (deriv B t) (A₁ x - B t)
  set J₀ := fun x => ∫ t in (0 : ℝ)..1, gl_integrand N (deriv A₀ x) (deriv B t) (A₀ x - B t)
  set JΛ := fun x => ∫ t in (0 : ℝ)..1, gl_integrand N (deriv Λ x) (deriv B t) (Λ x - B t)
  have hJ₁c : Continuous J₁ := jl_inner_continuous N hA₁ hB h₁B
  have hJ₀c : Continuous J₀ := jl_inner_continuous N hA₀ hB h₀B
  have hJΛc : Continuous JΛ := jl_inner_continuous N hΛc hB hΛB
  have hs0 : jl_sweep s₀ d 0 = s₀ - d := by simp [jl_sweep]
  have hsh : jl_sweep s₀ d (1 / 2) = s₀ + d := by
    simp only [jl_sweep]
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]; ring
  have hs1 : jl_sweep s₀ d 1 = s₀ - d := by simp [jl_sweep]
  have hG : tw_G N Λ B = (∫ x in (0 : ℝ)..1, JΛ x) := rfl
  have hG₁ : tw_G N A₁ B = (∫ x in (0 : ℝ)..1, J₁ x) := rfl
  have hG₀ : tw_G N A₀ B = (∫ x in (0 : ℝ)..1, J₀ x) := rfl
  have hsplit : (∫ x in (0 : ℝ)..1, JΛ x) = (∫ x in (0 : ℝ)..1 / 2, JΛ x) +
      ∫ x in (1 / 2 : ℝ)..1, JΛ x :=
    (intervalIntegral.integral_add_adjacent_intervals (hJΛc.intervalIntegrable _ _)
      (hJΛc.intervalIntegrable _ _)).symm
  have hup : (∫ x in (0 : ℝ)..1 / 2, JΛ x) = ∫ x in s₀ - d..s₀ + d, J₁ x := by
    have h := jl_half N s₀ d 0 (1 / 2) hA₁ hB h₁B (by norm_num) hΛ₁
    rw [hs0, hsh] at h; exact h
  have hlow : (∫ x in (1 / 2 : ℝ)..1, JΛ x) = -∫ x in s₀ - d..s₀ + d, J₀ x := by
    have h := jl_half N s₀ d (1 / 2) 1 hA₀ hB h₀B (by norm_num) hΛ₀
    rw [hsh, hs1] at h; exact h.trans (intervalIntegral.integral_symm _ _)
  have hper : ∀ J : ℝ → ℝ, Continuous J → Function.Periodic J 1 →
      (∫ x in (0 : ℝ)..1, J x) = (∫ x in s₀ - d..s₀ + d, J x) + ∫ x in s₀ + d..s₀ - d + 1, J x := by
    intro J hJ hJp
    have h0 := hJp.intervalIntegral_add_eq 0 (s₀ - d)
    rw [zero_add] at h0
    rw [h0, show s₀ - d + 1 = s₀ - d + 1 from rfl, ← intervalIntegral.integral_add_adjacent_intervals (hJ.intervalIntegrable _ _)
        (hJ.intervalIntegrable _ _)]
  have hfar : (∫ x in s₀ + d..s₀ - d + 1, J₁ x) = ∫ x in s₀ + d..s₀ - d + 1, J₀ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have he := hagree x hx
    simp only [J₁, J₀, he.self_of_nhds, he.deriv_eq]
  rw [hG, hG₁, hG₀, hsplit, hup, hlow, hper J₁ hJ₁c (jl_inner_periodic N hA₁per),
    hper J₀ hJ₀c (jl_inner_periodic N hA₀per), hfar]
  ring

end HryniewiczCriterion

/-!
# Planar facts for the strip bump jump

Strip coordinates `Ψ(μ, s) = c + μ (∂(s) - c)`: injectivity near a puncture, second-order
Taylor bounds for the circle, and the elementary inequalities used by the shrinking homotopies.
-/


noncomputable section

namespace HryniewiczCriterion

/-- Strip coordinates from the centre `c`. -/
def jb_psi (c : Plane) (μ s : ℝ) : Plane := c + μ • (circlePoint s - c)

lemma jb_psi_apply0 (c : Plane) (μ s : ℝ) :
    jb_psi c μ s 0 = c 0 + μ * (Real.cos (2 * Real.pi * s) - c 0) := by
  simp only [jb_psi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, circlePoint,
    Matrix.cons_val_zero]

lemma jb_psi_apply1 (c : Plane) (μ s : ℝ) :
    jb_psi c μ s 1 = c 1 + μ * (Real.sin (2 * Real.pi * s) - c 1) := by
  simp only [jb_psi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, circlePoint,
    Matrix.cons_val_one, Matrix.cons_val_zero]

lemma jb_cp_contDiff : ContDiff ℝ 2 circlePoint := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [circlePoint] <;> fun_prop

lemma jb_cp_periodic (s : ℝ) : circlePoint (s + 1) = circlePoint s := by
  ext i
  fin_cases i <;> simp [circlePoint, mul_add, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma jb_mem_disk {c : Plane} (hc : c ∈ openUnitDisk) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (s : ℝ) :
    jb_psi c μ s ∈ closedUnitDisk := by
  have hc' : c 0 ^ 2 + c 1 ^ 2 < 1 := hc
  have hp : Real.cos (2 * Real.pi * s) ^ 2 + Real.sin (2 * Real.pi * s) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  show (jb_psi c μ s) 0 ^ 2 + (jb_psi c μ s) 1 ^ 2 ≤ 1
  rw [jb_psi_apply0, jb_psi_apply1]
  set p0 := Real.cos (2 * Real.pi * s)
  set p1 := Real.sin (2 * Real.pi * s)
  have hm : 0 ≤ μ * (1 - μ) := mul_nonneg h0 (by linarith)
  have hm2 : 0 ≤ (1 - μ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hm (add_nonneg (sq_nonneg (c 0 - p0)) (sq_nonneg (c 1 - p1))),
    mul_nonneg hm2 (by linarith : (0 : ℝ) ≤ 1 - (c 0 ^ 2 + c 1 ^ 2)),
    mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 - (c 0 ^ 2 + c 1 ^ 2))]

/-- Two rays from an interior point `c` meet the unit circle once: the algebraic core. -/
lemma jb_inj_core {c0 c1 p0 p1 q0 q1 M a : ℝ} (hc : c0 ^ 2 + c1 ^ 2 < 1)
    (hp : p0 ^ 2 + p1 ^ 2 = 1) (hq : q0 ^ 2 + q1 ^ 2 = 1) (hM : 0 ≤ M) (ha : 0 < a)
    (h0 : M * (p0 - c0) = a * (q0 - c0)) (h1 : M * (p1 - c1) = a * (q1 - c1)) :
    M = a ∧ p0 = q0 ∧ p1 = q1 := by
  have e0 : M * p0 = (M - a) * c0 + a * q0 := by linarith
  have e1 : M * p1 = (M - a) * c1 + a * q1 := by linarith
  have key : (M - a) * (M * (1 - (c0 ^ 2 + c1 ^ 2)) + a * ((c0 - q0) ^ 2 + (c1 - q1) ^ 2)) = 0 := by
    linear_combination (-(M ^ 2)) * hp + a * M * hq +
      (M * p0 + ((M - a) * c0 + a * q0)) * e0 + (M * p1 + ((M - a) * c1 + a * q1)) * e1
  have hMa : M = a := by
    rcases mul_eq_zero.1 key with h | h
    · linarith
    · exfalso
      have h1' : 0 ≤ M * (1 - (c0 ^ 2 + c1 ^ 2)) := mul_nonneg hM (by linarith)
      have h2' : 0 ≤ (c0 - q0) ^ 2 + (c1 - q1) ^ 2 := by positivity
      have h3 : a * ((c0 - q0) ^ 2 + (c1 - q1) ^ 2) = 0 := by nlinarith
      have h4 : (c0 - q0) ^ 2 + (c1 - q1) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h3 with h | h
        · linarith
        · exact h
      have h5 : c0 = q0 := by nlinarith [sq_nonneg (c0 - q0), sq_nonneg (c1 - q1)]
      have h6 : c1 = q1 := by nlinarith [sq_nonneg (c0 - q0), sq_nonneg (c1 - q1)]
      subst h5 h6
      linarith
  subst hMa
  refine ⟨rfl, ?_, ?_⟩
  · have : M * (p0 - q0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · have : M * (p1 - q1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith

/-- The circle point is injective on windows of length `< 1`. -/
lemma jb_cp_inj {S s₀ : ℝ} (hS : |S - s₀| < 1 / 2)
    (h0 : Real.cos (2 * Real.pi * S) = Real.cos (2 * Real.pi * s₀))
    (h1 : Real.sin (2 * Real.pi * S) = Real.sin (2 * Real.pi * s₀)) : S = s₀ := by
  have hc : Real.cos (2 * Real.pi * (S - s₀)) = 1 := by
    rw [show 2 * Real.pi * (S - s₀) = 2 * Real.pi * S - 2 * Real.pi * s₀ by ring, Real.cos_sub,
      h0, h1, ← sq, ← sq, Real.cos_sq_add_sin_sq]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn' : (n : ℝ) = S - s₀ := by
    have : (n : ℝ) * (2 * Real.pi) = (S - s₀) * (2 * Real.pi) := by linarith
    exact mul_right_cancel₀ (by positivity) this
  have habs : |(n : ℝ)| < 1 / 2 := by rw [hn']; exact hS
  have hn0 : n = 0 := by
    have h2 := abs_lt.1 habs
    have h3 : -1 < n := by
      have : (-1 : ℝ) < n := by linarith
      exact_mod_cast this
    have h4 : n < 1 := by
      have : (n : ℝ) < 1 := by linarith
      exact_mod_cast this
    omega
  subst hn0
  simp at hn'
  linarith

/-- Injectivity of the strip map near a puncture at height `a₀ > 0`. -/
lemma jb_psi_inj {c : Plane} (hc : c ∈ openUnitDisk) {M S a₀ s₀ : ℝ} (hM : 0 ≤ M) (ha : 0 < a₀)
    (hS : |S - s₀| < 1 / 2) (h : jb_psi c M S = jb_psi c a₀ s₀) : S = s₀ ∧ M = a₀ := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [jb_psi_apply0, jb_psi_apply0] at h0
  rw [jb_psi_apply1, jb_psi_apply1] at h1
  obtain ⟨hMa, hp0, hp1⟩ := jb_inj_core (c0 := c 0) (c1 := c 1) hc
    (Real.cos_sq_add_sin_sq (2 * Real.pi * S)) (Real.cos_sq_add_sin_sq (2 * Real.pi * s₀)) hM ha
    (by linarith) (by linarith)
  exact ⟨jb_cp_inj hS hp0 hp1, hMa⟩

/-! ### Taylor bounds -/

lemma jb_taylor_cos {A h : ℝ} (hh : |h| ≤ 1) :
    |Real.cos (A + h) - Real.cos A + h * Real.sin A| ≤ h ^ 2 := by
  have e : Real.cos (A + h) - Real.cos A + h * Real.sin A =
      Real.cos A * (Real.cos h - 1) - Real.sin A * (Real.sin h - h) := by
    rw [Real.cos_add]; ring
  have c1 : |Real.cos h - 1| ≤ h ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    · have := Real.cos_le_one h; nlinarith [sq_nonneg h]
  have s1 : |Real.sin h - h| ≤ h ^ 2 / 6 := by
    have h3 := Real.abs_sub_sin_le h
    rw [abs_sub_comm] at h3
    have : |h| ^ 3 ≤ h ^ 2 := by
      have hh0 : 0 ≤ |h| := abs_nonneg h
      calc |h| ^ 3 = |h| * |h| ^ 2 := by ring
        _ ≤ 1 * |h| ^ 2 := by gcongr
        _ = h ^ 2 := by rw [one_mul, sq_abs]
    linarith
  rw [e]
  calc |Real.cos A * (Real.cos h - 1) - Real.sin A * (Real.sin h - h)|
      ≤ |Real.cos A * (Real.cos h - 1)| + |Real.sin A * (Real.sin h - h)| := abs_sub _ _
    _ = |Real.cos A| * |Real.cos h - 1| + |Real.sin A| * |Real.sin h - h| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 * (h ^ 2 / 2) + 1 * (h ^ 2 / 6) := by
        gcongr
        · exact Real.abs_cos_le_one A
        · exact Real.abs_sin_le_one A
    _ ≤ h ^ 2 := by nlinarith [sq_nonneg h]

lemma jb_taylor_sin {A h : ℝ} (hh : |h| ≤ 1) :
    |Real.sin (A + h) - Real.sin A - h * Real.cos A| ≤ h ^ 2 := by
  have e : Real.sin (A + h) - Real.sin A - h * Real.cos A =
      Real.sin A * (Real.cos h - 1) + Real.cos A * (Real.sin h - h) := by
    rw [Real.sin_add]; ring
  have c1 : |Real.cos h - 1| ≤ h ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    · have := Real.cos_le_one h; nlinarith [sq_nonneg h]
  have s1 : |Real.sin h - h| ≤ h ^ 2 / 6 := by
    have h3 := Real.abs_sub_sin_le h
    rw [abs_sub_comm] at h3
    have : |h| ^ 3 ≤ h ^ 2 := by
      have hh0 : 0 ≤ |h| := abs_nonneg h
      calc |h| ^ 3 = |h| * |h| ^ 2 := by ring
        _ ≤ 1 * |h| ^ 2 := by gcongr
        _ = h ^ 2 := by rw [one_mul, sq_abs]
    linarith
  rw [e]
  calc |Real.sin A * (Real.cos h - 1) + Real.cos A * (Real.sin h - h)|
      ≤ |Real.sin A * (Real.cos h - 1)| + |Real.cos A * (Real.sin h - h)| := abs_add_le _ _
    _ = |Real.sin A| * |Real.cos h - 1| + |Real.cos A| * |Real.sin h - h| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 * (h ^ 2 / 2) + 1 * (h ^ 2 / 6) := by
        gcongr
        · exact Real.abs_sin_le_one A
        · exact Real.abs_cos_le_one A
    _ ≤ h ^ 2 := by nlinarith [sq_nonneg h]

/-- The remainder of the strip map at `(a₀ + x, s₀ + y)` against its linearization, one
component at a time (`f = cos` or `sin`, `f'` its derivative). -/
lemma jb_rem_bound {a₀ x y r P Q f f' : ℝ} (ha0 : 0 ≤ a₀) (ha1 : a₀ ≤ 1) (hx : |x| ≤ r)
    (hy : |y| ≤ r) (hr : 2 * Real.pi * r ≤ 1)
    (hP : |P - Q| ≤ 2 * Real.pi * |y|) (hT : |P - Q - 2 * Real.pi * y * f'| ≤ (2 * Real.pi * y) ^ 2) :
    |x * (P - Q) + a₀ * (P - Q - 2 * Real.pi * y * f')| ≤
      (2 * Real.pi + 4 * Real.pi ^ 2) * r ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hr0 : 0 ≤ r := le_trans (abs_nonneg x) hx
  calc |x * (P - Q) + a₀ * (P - Q - 2 * Real.pi * y * f')|
      ≤ |x * (P - Q)| + |a₀ * (P - Q - 2 * Real.pi * y * f')| := abs_add_le _ _
    _ = |x| * |P - Q| + |a₀| * |P - Q - 2 * Real.pi * y * f'| := by rw [abs_mul, abs_mul]
    _ ≤ r * (2 * Real.pi * r) + 1 * (2 * Real.pi * r) ^ 2 := by
        gcongr
        · calc |P - Q| ≤ 2 * Real.pi * |y| := hP
            _ ≤ 2 * Real.pi * r := by gcongr
        · rw [abs_of_nonneg ha0]; exact ha1
        · calc |P - Q - 2 * Real.pi * y * f'| ≤ (2 * Real.pi * y) ^ 2 := hT
            _ = (2 * Real.pi * |y|) ^ 2 := by simp only [mul_pow, sq_abs]
            _ ≤ (2 * Real.pi * r) ^ 2 := by gcongr
    _ = (2 * Real.pi + 4 * Real.pi ^ 2) * r ^ 2 := by ring

/-- Lower bound for `|sin·u - cos·v|²` from `det(u, v)`. -/
lemma jb_quad_lower {u0 u1 v0 v1 C S : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) :
    (u0 * v1 - u1 * v0) ^ 2 ≤
      ((S * u0 - C * v0) ^ 2 + (S * u1 - C * v1) ^ 2) * (u0 ^ 2 + u1 ^ 2 + v0 ^ 2 + v1 ^ 2) := by
  set X0 := S * u0 - C * v0
  set X1 := S * u1 - C * v1
  set Y0 := C * u0 + S * v0
  set Y1 := C * u1 + S * v1
  have hdet : X0 * Y1 - X1 * Y0 = u0 * v1 - u1 * v0 := by
    simp only [X0, X1, Y0, Y1]; linear_combination (u0 * v1 - u1 * v0) * hCS
  have hlag : (X0 * Y1 - X1 * Y0) ^ 2 ≤ (X0 ^ 2 + X1 ^ 2) * (Y0 ^ 2 + Y1 ^ 2) := by
    nlinarith [sq_nonneg (X0 * Y0 + X1 * Y1)]
  have hY0 : Y0 ^ 2 ≤ u0 ^ 2 + v0 ^ 2 := by
    simp only [Y0]; nlinarith [sq_nonneg (C * v0 - S * u0)]
  have hY1 : Y1 ^ 2 ≤ u1 ^ 2 + v1 ^ 2 := by
    simp only [Y1]; nlinarith [sq_nonneg (C * v1 - S * u1)]
  rw [← hdet]
  calc (X0 * Y1 - X1 * Y0) ^ 2 ≤ (X0 ^ 2 + X1 ^ 2) * (Y0 ^ 2 + Y1 ^ 2) := hlag
    _ ≤ (X0 ^ 2 + X1 ^ 2) * (u0 ^ 2 + u1 ^ 2 + v0 ^ 2 + v1 ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `α e^{iθ} + t β e^{-iθ} ≠ 0` when `|β| < |α|` and `0 ≤ t ≤ 1`, in real coordinates. -/
lemma jb_ab_ne {ar ai br bi C S t : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hab : br ^ 2 + bi ^ 2 < ar ^ 2 + ai ^ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ar * C - ai * S + t * (br * C + bi * S)) ^ 2 +
      (ar * S + ai * C + t * (bi * C - br * S)) ^ 2 ≠ 0 := by
  intro h
  have h0 : ar * C - ai * S + t * (br * C + bi * S) = 0 := by nlinarith [sq_nonneg (ar * S + ai * C + t * (bi * C - br * S))]
  have h1 : ar * S + ai * C + t * (bi * C - br * S) = 0 := by nlinarith [sq_nonneg (ar * C - ai * S + t * (br * C + bi * S))]
  have hA : (ar * C - ai * S) ^ 2 + (ar * S + ai * C) ^ 2 = ar ^ 2 + ai ^ 2 := by
    linear_combination (ar ^ 2 + ai ^ 2) * hCS
  have hB : (br * C + bi * S) ^ 2 + (bi * C - br * S) ^ 2 = br ^ 2 + bi ^ 2 := by
    linear_combination (br ^ 2 + bi ^ 2) * hCS
  have e0 : ar * C - ai * S = -(t * (br * C + bi * S)) := by linarith
  have e1 : ar * S + ai * C = -(t * (bi * C - br * S)) := by linarith
  have : ar ^ 2 + ai ^ 2 = t ^ 2 * (br ^ 2 + bi ^ 2) := by
    rw [← hA, ← hB, e0, e1]; ring
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg br, sq_nonneg bi]

end HryniewiczCriterion

/-!
# The lens height for the strip bump jump

With `δ' = 3δ/2` and the sweep `s(σ) = s₀ - δ' cos 2πσ`, the extra height
`B(σ) = b(s σ) · φ(2 sin 2πσ)` (`φ` the smooth transition) equals `b(s σ)` on the upper half
`sin ≥ 0` and vanishes on the lower half: wherever `b(s σ) ≠ 0` we have `|sin 2πσ| > 1/2`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- `b` vanishes at distance in `(δ, 1 - δ)` from `s₀` when supported within `δ` of `s₀ + ℤ`. -/
lemma jb_b_zero_far {b : ℝ → ℝ} {s₀ δ : ℝ}
    (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ) {x : ℝ}
    (h1 : δ < |x - s₀|) (h2 : |x - s₀| < 1 - δ) : b x = 0 := by
  by_contra hb
  obtain ⟨n, hn⟩ := hbsupp x hb
  rcases lt_trichotomy n 0 with hn0 | rfl | hn0
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    rw [abs_lt] at hn h2
    linarith
  · simp at hn; linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    rw [abs_lt] at hn h2
    linarith

/-- The extra height of the lens. -/
def jb_B (b : ℝ → ℝ) (s₀ δ σ : ℝ) : ℝ :=
  b (jl_sweep s₀ (3 * δ / 2) σ) * Real.smoothTransition (2 * Real.sin (2 * Real.pi * σ))

section

variable {b : ℝ → ℝ} {s₀ δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
  (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ)
include hδ hδ' hbsupp

lemma jb_sweep_far {σ : ℝ} (h : 2 / 3 < |Real.cos (2 * Real.pi * σ)|) :
    b (jl_sweep s₀ (3 * δ / 2) σ) = 0 := by
  apply jb_b_zero_far hbsupp
  · simp only [jl_sweep, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * δ / 2)]
    nlinarith
  · simp only [jl_sweep, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * δ / 2)]
    have := Real.abs_cos_le_one (2 * Real.pi * σ)
    nlinarith

lemma jb_sin_big {σ : ℝ} (h : b (jl_sweep s₀ (3 * δ / 2) σ) ≠ 0) :
    1 / 2 < |Real.sin (2 * Real.pi * σ)| := by
  have hc : |Real.cos (2 * Real.pi * σ)| ≤ 2 / 3 := by
    by_contra h'
    exact h (jb_sweep_far hδ hδ' hbsupp (not_le.1 h'))
  have hc2 : Real.cos (2 * Real.pi * σ) ^ 2 ≤ 4 / 9 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos (2 * Real.pi * σ))]
  have hs2 : 5 / 9 ≤ Real.sin (2 * Real.pi * σ) ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * σ)]
  rw [← sq_lt_sq₀ (by norm_num) (abs_nonneg _), sq_abs]
  linarith

lemma jb_B_up {σ : ℝ} (h : 0 ≤ Real.sin (2 * Real.pi * σ)) :
    jb_B b s₀ δ σ = b (jl_sweep s₀ (3 * δ / 2) σ) := by
  unfold jb_B
  by_cases hb : b (jl_sweep s₀ (3 * δ / 2) σ) = 0
  · rw [hb, zero_mul]
  · have := jb_sin_big hδ hδ' hbsupp hb
    rw [abs_of_nonneg h] at this
    rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]

lemma jb_B_low {σ : ℝ} (h : Real.sin (2 * Real.pi * σ) ≤ 0) : jb_B b s₀ δ σ = 0 := by
  unfold jb_B
  by_cases hb : b (jl_sweep s₀ (3 * δ / 2) σ) = 0
  · rw [hb, zero_mul]
  · have := jb_sin_big hδ hδ' hbsupp hb
    rw [abs_of_nonpos h] at this
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

/-- On the open set `sin > 0 ∨ |cos| > 2/3` the lens runs on the upper graph. -/
lemma jb_B_eventually_up {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ᶠ σ' in 𝓝 σ, jb_B b s₀ δ σ' = b (jl_sweep s₀ (3 * δ / 2) σ') := by
  have hO : IsOpen ({σ' : ℝ | 0 < Real.sin (2 * Real.pi * σ')} ∪
      {σ' : ℝ | 2 / 3 < |Real.cos (2 * Real.pi * σ')|}) := by
    exact IsOpen.union (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))
  have hmem : σ ∈ ({σ' : ℝ | 0 < Real.sin (2 * Real.pi * σ')} ∪
      {σ' : ℝ | 2 / 3 < |Real.cos (2 * Real.pi * σ')|}) := by
    have hpi := Real.pi_pos
    have hs : 0 ≤ Real.sin (2 * Real.pi * σ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hσ.1]) (by nlinarith [hσ.2])
    rcases hs.lt_or_eq with h | h
    · exact Or.inl h
    · right
      have h1 := Real.cos_sq_add_sin_sq (2 * Real.pi * σ)
      rw [← h] at h1
      have hc1 : |Real.cos (2 * Real.pi * σ)| ^ 2 = 1 := by rw [sq_abs]; nlinarith
      show 2 / 3 < |Real.cos (2 * Real.pi * σ)|
      nlinarith [abs_nonneg (Real.cos (2 * Real.pi * σ))]
  filter_upwards [hO.mem_nhds hmem] with σ' h'
  rcases h' with h' | h'
  · exact jb_B_up hδ hδ' hbsupp h'.le
  · have h0 := jb_sweep_far hδ hδ' hbsupp h'
    unfold jb_B; rw [h0, zero_mul]

/-- On the open set `sin < 0 ∨ |cos| > 2/3` the lens runs on the lower graph. -/
lemma jb_B_eventually_low {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    ∀ᶠ σ' in 𝓝 σ, jb_B b s₀ δ σ' = 0 := by
  have hO : IsOpen ({σ' : ℝ | Real.sin (2 * Real.pi * σ') < 0} ∪
      {σ' : ℝ | 2 / 3 < |Real.cos (2 * Real.pi * σ')|}) := by
    exact IsOpen.union (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))
  have hmem : σ ∈ ({σ' : ℝ | Real.sin (2 * Real.pi * σ') < 0} ∪
      {σ' : ℝ | 2 / 3 < |Real.cos (2 * Real.pi * σ')|}) := by
    have hpi := Real.pi_pos
    have hs : Real.sin (2 * Real.pi * σ) ≤ 0 := by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [hσ.2]) (by nlinarith [hσ.1])
    rcases hs.lt_or_eq with h | h
    · exact Or.inl h
    · right
      have h1 := Real.cos_sq_add_sin_sq (2 * Real.pi * σ)
      rw [h] at h1
      have hc1 : |Real.cos (2 * Real.pi * σ)| ^ 2 = 1 := by rw [sq_abs]; nlinarith
      show 2 / 3 < |Real.cos (2 * Real.pi * σ)|
      nlinarith [abs_nonneg (Real.cos (2 * Real.pi * σ))]
  filter_upwards [hO.mem_nhds hmem] with σ' h'
  rcases h' with h' | h'
  · exact jb_B_low hδ hδ' hbsupp h'.le
  · have h0 := jb_sweep_far hδ hδ' hbsupp h'
    unfold jb_B; rw [h0, zero_mul]

/-- Off the window `[s₀ - δ', s₀ + δ']` the bump vanishes near every point. -/
lemma jb_b_eventually_zero {x : ℝ} (hx : x ∈ Icc (s₀ + 3 * δ / 2) (s₀ - 3 * δ / 2 + 1)) :
    ∀ᶠ y in 𝓝 x, b y = 0 := by
  have hmem : x ∈ Ioo (s₀ + δ) (s₀ + 1 - δ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with y hy
  apply jb_b_zero_far hbsupp
  · rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.1]
  · rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.2]

end

lemma jb_B_nonneg {b : ℝ → ℝ} (hb : ∀ s, 0 ≤ b s) (s₀ δ σ : ℝ) : 0 ≤ jb_B b s₀ δ σ :=
  mul_nonneg (hb _) (Real.smoothTransition.nonneg _)

lemma jb_B_le {b : ℝ → ℝ} (hb : ∀ s, 0 ≤ b s) (s₀ δ σ : ℝ) :
    jb_B b s₀ δ σ ≤ b (jl_sweep s₀ (3 * δ / 2) σ) :=
  mul_le_of_le_one_right (hb _) (Real.smoothTransition.le_one _)

lemma jb_sweep_periodic (s₀ d σ : ℝ) : jl_sweep s₀ d (σ + 1) = jl_sweep s₀ d σ := by
  simp only [jl_sweep, mul_add, mul_one, Real.cos_add_two_pi]

lemma jb_sin_periodic (σ : ℝ) : Real.sin (2 * Real.pi * (σ + 1)) = Real.sin (2 * Real.pi * σ) := by
  rw [mul_add, mul_one, Real.sin_add_two_pi]

lemma jb_cos_periodic (σ : ℝ) : Real.cos (2 * Real.pi * (σ + 1)) = Real.cos (2 * Real.pi * σ) := by
  rw [mul_add, mul_one, Real.cos_add_two_pi]

lemma jb_B_periodic (b : ℝ → ℝ) (s₀ δ σ : ℝ) : jb_B b s₀ δ (σ + 1) = jb_B b s₀ δ σ := by
  simp only [jb_B, jb_sweep_periodic, jb_sin_periodic]

lemma jb_sweep_contDiff (s₀ d : ℝ) : ContDiff ℝ 2 (jl_sweep s₀ d) := by
  unfold jl_sweep; fun_prop

lemma jb_B_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ 2 b) (s₀ δ : ℝ) : ContDiff ℝ 2 (jb_B b s₀ δ) := by
  unfold jb_B
  have hφ : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hb.comp (jb_sweep_contDiff s₀ _)).mul (hφ.comp (by fun_prop))

end HryniewiczCriterion

/-!
# The four homotopy stages of the strip bump jump

`G` is any functional on parameter loops that is invariant under `C²` periodic homotopies
inside `K` (the Gauss integral of `E ∘ ·`, by the planar homotopy lemma). The stages:
1. lens `→` small circle `Ψ(a₀ + r sin, s₀ - r cos)` in strip coordinates;
2. that circle `→` its linearization `z + r (sin · u - cos · v)` (Taylor, straight line);
3. kill the antiholomorphic part `β e^{-iθ}` (`|β| < |α|` since `det = |α|² - |β|² > 0`);
4. rotate the phase and change the radius to `z + ρ ∂`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- Homotopy invariance of `G` on loops in `K`. -/
def jm_HInv (K : Set Plane) (G : (ℝ → Plane) → ℝ) : Prop :=
  ∀ L : ℝ → ℝ → Plane, ContDiff ℝ 2 (Function.uncurry L) → (∀ τ s, L τ (s + 1) = L τ s) →
    (∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K) → G (L 0) = G (L 1)

/-! ### Stage 1: lens to a small strip circle -/

theorem jm_stage1 {K : Set Plane} {G : (ℝ → Plane) → ℝ} (hG : jm_HInv K G) {c : Plane}
    {a₀ s₀ δ r : ℝ} {g b : ℝ → ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hg : ContDiff ℝ 2 g)
    (hb : ContDiff ℝ 2 b) (hgb : ∀ s, 0 ≤ g s ∧ 0 ≤ b s ∧ g s + b s ≤ 1)
    (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ)
    (hlow : g s₀ < a₀) (hhigh : a₀ < g s₀ + b s₀) (hr : 0 < r) (hra : r ≤ a₀) (hra' : r ≤ 1 - a₀)
    (hrd : r ≤ 3 * δ / 2)
    (hK : ∀ M S, 0 ≤ M → M ≤ 1 → |S - s₀| ≤ 2 * δ → (S = s₀ → M ≠ a₀) → jb_psi c M S ∈ K) :
    G (fun σ => jb_psi c (g (jl_sweep s₀ (3 * δ / 2) σ) + jb_B b s₀ δ σ)
        (jl_sweep s₀ (3 * δ / 2) σ)) =
      G (fun σ => jb_psi c (a₀ + r * Real.sin (2 * Real.pi * σ)) (s₀ - r * Real.cos (2 * Real.pi * σ))) := by
  set L : ℝ → ℝ → Plane := fun τ σ => jb_psi c
    ((1 - τ) * (g (jl_sweep s₀ (3 * δ / 2) σ) + jb_B b s₀ δ σ) +
      τ * (a₀ + r * Real.sin (2 * Real.pi * σ)))
    (s₀ - ((1 - τ) * (3 * δ / 2) + τ * r) * Real.cos (2 * Real.pi * σ)) with hL
  have hcp := jb_cp_contDiff
  have hB := jb_B_contDiff hb s₀ δ
  have hsw := jb_sweep_contDiff s₀ (3 * δ / 2)
  have hsm : ContDiff ℝ 2 (Function.uncurry L) := by
    show ContDiff ℝ 2 fun p : ℝ × ℝ => L p.1 p.2
    simp only [hL, jb_psi]
    fun_prop
  have hper : ∀ τ s, L τ (s + 1) = L τ s := by
    intro τ s
    simp only [hL, jb_sweep_periodic, jb_B_periodic, jb_sin_periodic, jb_cos_periodic]
  have hLK : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K := by
    intro τ hτ σ
    obtain ⟨hτ0, hτ1⟩ := hτ
    set C := Real.cos (2 * Real.pi * σ) with hC
    set Sn := Real.sin (2 * Real.pi * σ) with hSn
    have hCS : C ^ 2 + Sn ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hC1 : |C| ≤ 1 := Real.abs_cos_le_one _
    have hS1 : |Sn| ≤ 1 := Real.abs_sin_le_one _
    obtain ⟨hSlo, hShi⟩ := abs_le.1 hS1
    set w := jl_sweep s₀ (3 * δ / 2) σ with hw
    have hBnn := jb_B_nonneg (fun s => (hgb s).2.1) s₀ δ σ
    have hBle := jb_B_le (fun s => (hgb s).2.1) s₀ δ σ
    have hm0 : 0 ≤ g w + jb_B b s₀ δ σ := add_nonneg (hgb w).1 hBnn
    have hm1 : g w + jb_B b s₀ δ σ ≤ 1 := by linarith [(hgb w).2.2]
    have he0 : 0 ≤ a₀ + r * Sn := by nlinarith
    have he1 : a₀ + r * Sn ≤ 1 := by nlinarith
    have hcoef : 0 < (1 - τ) * (3 * δ / 2) + τ * r := by
      rcases hτ0.lt_or_eq with h | h
      · nlinarith
      · subst h; nlinarith
    have hcoef' : (1 - τ) * (3 * δ / 2) + τ * r ≤ 3 * δ / 2 := by nlinarith
    show jb_psi c ((1 - τ) * (g w + jb_B b s₀ δ σ) + τ * (a₀ + r * Sn))
      (s₀ - ((1 - τ) * (3 * δ / 2) + τ * r) * C) ∈ K
    apply hK
    · nlinarith [mul_nonneg (sub_nonneg.2 hτ1) hm0, mul_nonneg hτ0 he0]
    · nlinarith [mul_nonneg (sub_nonneg.2 hτ1) (sub_nonneg.2 hm1), mul_nonneg hτ0 (sub_nonneg.2 he1)]
    · rw [show s₀ - ((1 - τ) * (3 * δ / 2) + τ * r) * C - s₀ =
          -(((1 - τ) * (3 * δ / 2) + τ * r) * C) by ring, abs_neg, abs_mul, abs_of_pos hcoef]
      nlinarith [abs_nonneg C]
    · intro hS
      have hC0 : C = 0 := by
        have : ((1 - τ) * (3 * δ / 2) + τ * r) * C = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      have hw0 : w = s₀ := by simp only [hw, jl_sweep, ← hC, hC0, mul_zero, sub_zero]
      have hS2 : Sn ^ 2 = 1 := by rw [hC0] at hCS; linarith
      have hfac : (Sn - 1) * (Sn + 1) = 0 := by linear_combination hS2
      rcases le_or_gt 0 Sn with hs | hs
      · have hs1 : Sn = 1 := by
          rcases mul_eq_zero.1 hfac with h | h
          · linarith
          · linarith
        have hBv : jb_B b s₀ δ σ = b s₀ := by rw [jb_B_up hδ hδ' hbsupp hs, ← hw, hw0]
        rw [hw0, hBv, hs1]
        intro h
        have k : (1 - τ) * (g s₀ + b s₀ - a₀) + τ * r = 0 := by linear_combination h
        rcases hτ0.lt_or_eq with h' | h'
        · have k1 : 0 ≤ (1 - τ) * (g s₀ + b s₀ - a₀) := mul_nonneg (by linarith) (by linarith)
          have k2 : 0 < τ * r := mul_pos h' hr
          linarith
        · subst h'
          linarith
      · have hs1 : Sn = -1 := by
          rcases mul_eq_zero.1 hfac with h | h
          · linarith
          · linarith
        have hBv : jb_B b s₀ δ σ = 0 := jb_B_low hδ hδ' hbsupp hs.le
        rw [hw0, hBv, hs1]
        intro h
        have k : (1 - τ) * (g s₀ - a₀) - τ * r = 0 := by linear_combination h
        rcases hτ0.lt_or_eq with h' | h'
        · have k1 : (1 - τ) * (g s₀ - a₀) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          have k2 : 0 < τ * r := mul_pos h' hr
          linarith
        · subst h'
          linarith
  have h := hG L hsm hper hLK
  have e0 : L 0 = fun σ => jb_psi c (g (jl_sweep s₀ (3 * δ / 2) σ) + jb_B b s₀ δ σ)
      (jl_sweep s₀ (3 * δ / 2) σ) := by
    funext σ
    simp only [hL, jl_sweep]
    congr 1 <;> ring
  have e1 : L 1 = fun σ => jb_psi c (a₀ + r * Real.sin (2 * Real.pi * σ))
      (s₀ - r * Real.cos (2 * Real.pi * σ)) := by
    funext σ
    simp only [hL]
    congr 1 <;> ring
  rw [← e0, ← e1]
  exact h

/-! ### Stage 2: Taylor straight line -/

/-- The numerics of stage 2. -/
lemma jm_num2 {q0 q1 e0 e1 t X0 X1 r Dd Ws K2 Bd ε : ℝ} (hq0 : q0 = r * X0) (hq1 : q1 = r * X1)
    (he0 : |e0| ≤ K2 * r ^ 2) (he1 : |e1| ≤ K2 * r ^ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hD : Dd ^ 2 ≤ (X0 ^ 2 + X1 ^ 2) * Ws) (hWs : 0 ≤ Ws) (hr : 0 < r)
    (hsmall : 2 * K2 ^ 2 * r ^ 2 * Ws < Dd ^ 2) (hX0 : |X0| ≤ Bd) (hX1 : |X1| ≤ Bd)
    (hK2 : K2 * r ≤ 1) (hnear : 2 * r ^ 2 * (Bd + 1) ^ 2 < ε ^ 2) :
    (q0 + t * e0) ^ 2 + (q1 + t * e1) ^ 2 < ε ^ 2 ∧ ¬ (q0 + t * e0 = 0 ∧ q1 + t * e1 = 0) := by
  have hK2nn : 0 ≤ K2 * r ^ 2 := le_trans (abs_nonneg _) he0
  have hr2 : 0 < r ^ 2 := by positivity
  have hKr : K2 * r ^ 2 ≤ r := by
    calc K2 * r ^ 2 = r * (K2 * r) := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hK2 hr.le
      _ = r := mul_one r
  constructor
  · have b0 : |q0 + t * e0| ≤ r * (Bd + 1) := by
      calc |q0 + t * e0| ≤ |q0| + |t * e0| := abs_add_le _ _
        _ = r * |X0| + t * |e0| := by rw [hq0, abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg ht0]
        _ ≤ r * Bd + 1 * (K2 * r ^ 2) := by gcongr
        _ ≤ r * (Bd + 1) := by linarith [hKr]
    have b1 : |q1 + t * e1| ≤ r * (Bd + 1) := by
      calc |q1 + t * e1| ≤ |q1| + |t * e1| := abs_add_le _ _
        _ = r * |X1| + t * |e1| := by rw [hq1, abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg ht0]
        _ ≤ r * Bd + 1 * (K2 * r ^ 2) := by gcongr
        _ ≤ r * (Bd + 1) := by linarith [hKr]
    have s0 : (q0 + t * e0) ^ 2 ≤ (r * (Bd + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b0 2
    have s1 : (q1 + t * e1) ^ 2 ≤ (r * (Bd + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b1 2
    have : (r * (Bd + 1)) ^ 2 = r ^ 2 * (Bd + 1) ^ 2 := by ring
    linarith
  · rintro ⟨h0, h1⟩
    have f0 : q0 ^ 2 = t ^ 2 * e0 ^ 2 := by
      have : q0 = -(t * e0) := by linarith
      rw [this]; ring
    have f1 : q1 ^ 2 = t ^ 2 * e1 ^ 2 := by
      have : q1 = -(t * e1) := by linarith
      rw [this]; ring
    have g0 : e0 ^ 2 ≤ (K2 * r ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he0 2
    have g1 : e1 ^ 2 ≤ (K2 * r ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he1 2
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
    have hsum : r ^ 2 * (X0 ^ 2 + X1 ^ 2) ≤ r ^ 2 * (2 * K2 ^ 2 * r ^ 2) := by
      have : q0 ^ 2 + q1 ^ 2 = r ^ 2 * (X0 ^ 2 + X1 ^ 2) := by rw [hq0, hq1]; ring
      rw [← this, f0, f1]
      have k1 : t ^ 2 * (e0 ^ 2 + e1 ^ 2) ≤ e0 ^ 2 + e1 ^ 2 :=
        mul_le_of_le_one_left (by positivity) ht2
      have k2 : (K2 * r ^ 2) ^ 2 = r ^ 2 * (K2 ^ 2 * r ^ 2) := by ring
      linarith
    have hX : X0 ^ 2 + X1 ^ 2 ≤ 2 * K2 ^ 2 * r ^ 2 := le_of_mul_le_mul_left hsum hr2
    have k3 := mul_le_mul_of_nonneg_right hX hWs
    linarith

theorem jm_stage2 {K : Set Plane} {G : (ℝ → Plane) → ℝ} (hG : jm_HInv K G) {c z u v : Plane}
    {a₀ s₀ r ε : ℝ} (hz : z = jb_psi c a₀ s₀) (ha0 : 0 ≤ a₀) (ha1 : a₀ ≤ 1)
    (hu0 : u 0 = Real.cos (2 * Real.pi * s₀) - c 0) (hu1 : u 1 = Real.sin (2 * Real.pi * s₀) - c 1)
    (hv0 : v 0 = -(a₀ * (2 * Real.pi * Real.sin (2 * Real.pi * s₀))))
    (hv1 : v 1 = a₀ * (2 * Real.pi * Real.cos (2 * Real.pi * s₀)))
    (hr : 0 < r) (hr1 : 2 * Real.pi * r ≤ 1) (hr2 : (2 * Real.pi + 4 * Real.pi ^ 2) * r ≤ 1)
    (hr3 : 2 * (2 * Real.pi + 4 * Real.pi ^ 2) ^ 2 * r ^ 2 * (u 0 ^ 2 + u 1 ^ 2 + v 0 ^ 2 + v 1 ^ 2) <
      (u 0 * v 1 - u 1 * v 0) ^ 2)
    (hr4 : 2 * r ^ 2 * (|u 0| + |u 1| + |v 0| + |v 1| + 1) ^ 2 < ε ^ 2)
    (hnear : ∀ w : Plane, w 0 ^ 2 + w 1 ^ 2 < ε ^ 2 → w ≠ 0 → z + w ∈ K) :
    G (fun σ => jb_psi c (a₀ + r * Real.sin (2 * Real.pi * σ)) (s₀ - r * Real.cos (2 * Real.pi * σ))) =
      G (fun σ => z + ((r * Real.sin (2 * Real.pi * σ)) • u - (r * Real.cos (2 * Real.pi * σ)) • v)) := by
  set P : ℝ → Plane := fun σ => jb_psi c (a₀ + r * Real.sin (2 * Real.pi * σ))
    (s₀ - r * Real.cos (2 * Real.pi * σ)) with hP
  set Q : ℝ → Plane := fun σ => (r * Real.sin (2 * Real.pi * σ)) • u -
    (r * Real.cos (2 * Real.pi * σ)) • v with hQ
  set L : ℝ → ℝ → Plane := fun τ σ => z + (Q σ + (1 - τ) • (P σ - z - Q σ)) with hL
  have hcp := jb_cp_contDiff
  have hsm : ContDiff ℝ 2 (Function.uncurry L) := by
    show ContDiff ℝ 2 fun p : ℝ × ℝ => L p.1 p.2
    simp only [hL, hP, hQ, jb_psi]
    fun_prop
  have hper : ∀ τ s, L τ (s + 1) = L τ s := by
    intro τ s
    simp only [hL, hP, hQ, jb_sin_periodic, jb_cos_periodic]
  set K2 := 2 * Real.pi + 4 * Real.pi ^ 2 with hK2
  have hpi := Real.pi_pos
  have hLK : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K := by
    intro τ hτ σ
    set C := Real.cos (2 * Real.pi * σ) with hC
    set Sn := Real.sin (2 * Real.pi * σ) with hSn
    have hCS : C ^ 2 + Sn ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hC1 : |C| ≤ 1 := Real.abs_cos_le_one _
    have hS1 : |Sn| ≤ 1 := Real.abs_sin_le_one _
    have hx : |r * Sn| ≤ r := by rw [abs_mul, abs_of_pos hr]; exact mul_le_of_le_one_right hr.le hS1
    have hy : |-(r * C)| ≤ r := by
      rw [abs_neg, abs_mul, abs_of_pos hr]; exact mul_le_of_le_one_right hr.le hC1
    have hh : |2 * Real.pi * -(r * C)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      calc 2 * Real.pi * |-(r * C)| ≤ 2 * Real.pi * r := by gcongr
        _ ≤ 1 := hr1
    -- the remainder, one component at a time
    have hR0 : |(P σ - z - Q σ) 0| ≤ K2 * r ^ 2 := by
      have e : (P σ - z - Q σ) 0 = (r * Sn) * (Real.cos (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) -
          Real.cos (2 * Real.pi * s₀)) + a₀ * (Real.cos (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) -
          Real.cos (2 * Real.pi * s₀) - 2 * Real.pi * -(r * C) * -Real.sin (2 * Real.pi * s₀)) := by
        simp only [hP, hQ, hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, jb_psi_apply0, hu0, hv0]
        rw [show 2 * Real.pi * (s₀ - r * C) = 2 * Real.pi * s₀ + 2 * Real.pi * -(r * C) by ring]
        ring
      rw [e]
      apply jb_rem_bound (f := 0) ha0 ha1 hx hy hr1
      · have := Real.abs_cos_sub_cos_le (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) (2 * Real.pi * s₀)
        rw [show 2 * Real.pi * s₀ + 2 * Real.pi * -(r * C) - 2 * Real.pi * s₀ =
          2 * Real.pi * -(r * C) by ring, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
        exact this
      · have := jb_taylor_cos (A := 2 * Real.pi * s₀) hh
        rw [show Real.cos (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) - Real.cos (2 * Real.pi * s₀) -
          2 * Real.pi * -(r * C) * -Real.sin (2 * Real.pi * s₀) =
          Real.cos (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) - Real.cos (2 * Real.pi * s₀) +
          2 * Real.pi * -(r * C) * Real.sin (2 * Real.pi * s₀) by ring]
        exact this
    have hR1 : |(P σ - z - Q σ) 1| ≤ K2 * r ^ 2 := by
      have e : (P σ - z - Q σ) 1 = (r * Sn) * (Real.sin (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) -
          Real.sin (2 * Real.pi * s₀)) + a₀ * (Real.sin (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) -
          Real.sin (2 * Real.pi * s₀) - 2 * Real.pi * -(r * C) * Real.cos (2 * Real.pi * s₀)) := by
        simp only [hP, hQ, hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, jb_psi_apply1, hu1, hv1]
        rw [show 2 * Real.pi * (s₀ - r * C) = 2 * Real.pi * s₀ + 2 * Real.pi * -(r * C) by ring]
        ring
      rw [e]
      apply jb_rem_bound (f := 0) ha0 ha1 hx hy hr1
      · have := Real.abs_sin_sub_sin_le (2 * Real.pi * s₀ + 2 * Real.pi * -(r * C)) (2 * Real.pi * s₀)
        rw [show 2 * Real.pi * s₀ + 2 * Real.pi * -(r * C) - 2 * Real.pi * s₀ =
          2 * Real.pi * -(r * C) by ring, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
        exact this
      · exact jb_taylor_sin (A := 2 * Real.pi * s₀) hh
    have hQ0 : Q σ 0 = r * (Sn * u 0 - C * v 0) := by
      simp only [hQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hQ1 : Q σ 1 = r * (Sn * u 1 - C * v 1) := by
      simp only [hQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hX0 : |Sn * u 0 - C * v 0| ≤ |u 0| + |u 1| + |v 0| + |v 1| := by
      calc |Sn * u 0 - C * v 0| ≤ |Sn * u 0| + |C * v 0| := abs_sub _ _
        _ = |Sn| * |u 0| + |C| * |v 0| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |u 0| + 1 * |v 0| := by gcongr
        _ ≤ |u 0| + |u 1| + |v 0| + |v 1| := by linarith [abs_nonneg (u 1), abs_nonneg (v 1)]
    have hX1 : |Sn * u 1 - C * v 1| ≤ |u 0| + |u 1| + |v 0| + |v 1| := by
      calc |Sn * u 1 - C * v 1| ≤ |Sn * u 1| + |C * v 1| := abs_sub _ _
        _ = |Sn| * |u 1| + |C| * |v 1| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |u 1| + 1 * |v 1| := by gcongr
        _ ≤ |u 0| + |u 1| + |v 0| + |v 1| := by linarith [abs_nonneg (u 0), abs_nonneg (v 0)]
    have hD := jb_quad_lower (u0 := u 0) (u1 := u 1) (v0 := v 0) (v1 := v 1) hCS
    obtain ⟨hn, hne⟩ := jm_num2 (t := 1 - τ) hQ0 hQ1 hR0 hR1 (by linarith [hτ.2]) (by linarith [hτ.1])
      hD (by positivity) hr hr3 hX0 hX1 hr2 hr4
    apply hnear
    · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hn
    · intro h0
      apply hne
      constructor
      · have := congrFun h0 0; simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
      · have := congrFun h0 1; simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  have h := hG L hsm hper hLK
  have e0 : L 0 = P := by
    funext σ; simp only [hL, sub_zero, one_smul]; abel
  have e1 : L 1 = fun σ => z + Q σ := by
    funext σ; simp only [hL, sub_self, zero_smul, add_zero]
  rw [e0, e1] at h
  exact h

/-! ### Stage 3: kill the antiholomorphic part -/

theorem jm_stage3 {K : Set Plane} {G : (ℝ → Plane) → ℝ} (hG : jm_HInv K G) {z : Plane}
    {r ar ai br bi ε : ℝ} (hr : 0 < r) (hab : br ^ 2 + bi ^ 2 < ar ^ 2 + ai ^ 2)
    (hr5 : 2 * r ^ 2 * (|ar| + |ai| + |br| + |bi|) ^ 2 < ε ^ 2)
    (hnear : ∀ w : Plane, w 0 ^ 2 + w 1 ^ 2 < ε ^ 2 → w ≠ 0 → z + w ∈ K) :
    G (fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] + Real.sin (2 * Real.pi * σ) • ![-ai, ar] +
      (Real.cos (2 * Real.pi * σ) • ![br, bi] + Real.sin (2 * Real.pi * σ) • ![bi, -br]))) =
    G (fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] + Real.sin (2 * Real.pi * σ) • ![-ai, ar])) := by
  set L : ℝ → ℝ → Plane := fun τ σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] +
    Real.sin (2 * Real.pi * σ) • ![-ai, ar] + (1 - τ) • (Real.cos (2 * Real.pi * σ) • ![br, bi] +
      Real.sin (2 * Real.pi * σ) • ![bi, -br])) with hL
  have hsm : ContDiff ℝ 2 (Function.uncurry L) := by
    show ContDiff ℝ 2 fun p : ℝ × ℝ => L p.1 p.2
    simp only [hL]
    fun_prop
  have hper : ∀ τ s, L τ (s + 1) = L τ s := by
    intro τ s
    simp only [hL, jb_sin_periodic, jb_cos_periodic]
  have hLK : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K := by
    intro τ hτ σ
    set C := Real.cos (2 * Real.pi * σ) with hC
    set Sn := Real.sin (2 * Real.pi * σ) with hSn
    have hCS : C ^ 2 + Sn ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hC1 : |C| ≤ 1 := Real.abs_cos_le_one _
    have hS1 : |Sn| ≤ 1 := Real.abs_sin_le_one _
    set t := 1 - τ with ht
    have ht0 : 0 ≤ t := by linarith [hτ.2]
    have ht1 : t ≤ 1 := by linarith [hτ.1]
    set w0 := ar * C - ai * Sn + t * (br * C + bi * Sn) with hw0
    set w1 := ar * Sn + ai * C + t * (bi * C - br * Sn) with hw1
    have hv0 : (r • (C • ![ar, ai] + Sn • ![-ai, ar] + t • (C • ![br, bi] + Sn • ![bi, -br]))) 0 =
        r * w0 := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.cons_val_zero, hw0]; ring
    have hv1 : (r • (C • ![ar, ai] + Sn • ![-ai, ar] + t • (C • ![br, bi] + Sn • ![bi, -br]))) 1 =
        r * w1 := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, hw1]; ring
    have hne := jb_ab_ne hCS hab ht0 ht1
    have hB : |w0| ≤ |ar| + |ai| + |br| + |bi| ∧ |w1| ≤ |ar| + |ai| + |br| + |bi| := by
      have k1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
      constructor
      · calc |w0| ≤ |ar * C| + |ai * Sn| + |t| * (|br * C| + |bi * Sn|) := by
              rw [hw0]
              calc |ar * C - ai * Sn + t * (br * C + bi * Sn)|
                  ≤ |ar * C - ai * Sn| + |t * (br * C + bi * Sn)| := abs_add_le _ _
                _ ≤ (|ar * C| + |ai * Sn|) + |t| * (|br * C| + |bi * Sn|) := by
                  rw [abs_mul]; gcongr
                  · exact abs_sub _ _
                  · exact abs_add_le _ _
                _ = _ := by ring
          _ ≤ |ar| * 1 + |ai| * 1 + 1 * (|br| * 1 + |bi| * 1) := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]; gcongr
          _ = |ar| + |ai| + |br| + |bi| := by ring
      · calc |w1| ≤ |ar * Sn| + |ai * C| + |t| * (|bi * C| + |br * Sn|) := by
              rw [hw1]
              calc |ar * Sn + ai * C + t * (bi * C - br * Sn)|
                  ≤ |ar * Sn + ai * C| + |t * (bi * C - br * Sn)| := abs_add_le _ _
                _ ≤ (|ar * Sn| + |ai * C|) + |t| * (|bi * C| + |br * Sn|) := by
                  rw [abs_mul]; gcongr
                  · exact abs_add_le _ _
                  · exact abs_sub _ _
                _ = _ := by ring
          _ ≤ |ar| * 1 + |ai| * 1 + 1 * (|bi| * 1 + |br| * 1) := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]; gcongr
          _ = |ar| + |ai| + |br| + |bi| := by ring
    apply hnear
    · rw [hv0, hv1]
      set Bα := |ar| + |ai| + |br| + |bi|
      have s0 : w0 ^ 2 ≤ Bα ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB.1 2
      have s1 : w1 ^ 2 ≤ Bα ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB.2 2
      have hr2 : 0 < r ^ 2 := by positivity
      have k0 := mul_le_mul_of_nonneg_left s0 hr2.le
      have k1 := mul_le_mul_of_nonneg_left s1 hr2.le
      rw [mul_pow, mul_pow]
      linarith
    · intro h0
      have a0 := congrFun h0 0
      have a1 := congrFun h0 1
      rw [hv0] at a0
      rw [hv1] at a1
      simp only [Pi.zero_apply, mul_eq_zero, hr.ne', false_or] at a0 a1
      exact hne (by rw [← hw0, ← hw1, a0, a1]; ring)
  have h := hG L hsm hper hLK
  have e0 : L 0 = fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] +
      Real.sin (2 * Real.pi * σ) • ![-ai, ar] + (Real.cos (2 * Real.pi * σ) • ![br, bi] +
      Real.sin (2 * Real.pi * σ) • ![bi, -br])) := by
    funext σ; simp only [hL, sub_zero, one_smul]
  have e1 : L 1 = fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] +
      Real.sin (2 * Real.pi * σ) • ![-ai, ar]) := by
    funext σ; simp only [hL, sub_self, zero_smul, add_zero]
  rw [e0, e1] at h
  exact h

/-! ### Stage 4: phase and radius -/

theorem jm_stage4 {K : Set Plane} {G : (ℝ → Plane) → ℝ} (hG : jm_HInv K G) {z : Plane}
    {R φ ρ ε : ℝ} (hR : 0 < R) (hRε : R < ε) (hρ : 0 < ρ) (hρε : ρ < ε)
    (hnear : ∀ w : Plane, w 0 ^ 2 + w 1 ^ 2 < ε ^ 2 → w ≠ 0 → z + w ∈ K) :
    G (fun σ => z + R • circlePoint (σ + φ)) = G (fun σ => z + ρ • circlePoint σ) := by
  set L : ℝ → ℝ → Plane := fun τ σ => z + ((1 - τ) * R + τ * ρ) • circlePoint (σ + (1 - τ) * φ)
    with hL
  have hcp := jb_cp_contDiff
  have hsm : ContDiff ℝ 2 (Function.uncurry L) := by
    show ContDiff ℝ 2 fun p : ℝ × ℝ => L p.1 p.2
    simp only [hL]
    fun_prop
  have hper : ∀ τ s, L τ (s + 1) = L τ s := by
    intro τ s
    simp only [hL, show s + 1 + (1 - τ) * φ = s + (1 - τ) * φ + 1 by ring, jb_cp_periodic]
  have hLK : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K := by
    intro τ hτ σ
    obtain ⟨hτ0, hτ1⟩ := hτ
    have hpos : 0 < (1 - τ) * R + τ * ρ := by
      rcases hτ0.lt_or_eq with h | h
      · nlinarith
      · subst h; simpa using hR
    have hlt : (1 - τ) * R + τ * ρ < ε := by
      have k1 : (1 - τ) * R ≤ (1 - τ) * max R ρ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
      have k2 : τ * ρ ≤ τ * max R ρ := mul_le_mul_of_nonneg_left (le_max_right _ _) hτ0
      have k3 : max R ρ < ε := max_lt hRε hρε
      linarith
    have hcs := Real.cos_sq_add_sin_sq (2 * Real.pi * (σ + (1 - τ) * φ))
    apply hnear
    · simp only [Pi.smul_apply, smul_eq_mul, circlePoint, Matrix.cons_val_zero, Matrix.cons_val_one]
      have : ((1 - τ) * R + τ * ρ) ^ 2 < ε ^ 2 := by
        exact pow_lt_pow_left₀ hlt hpos.le (by norm_num)
      nlinarith
    · intro h0
      have a0 := congrFun h0 0
      have a1 := congrFun h0 1
      simp only [Pi.smul_apply, smul_eq_mul, circlePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.zero_apply, mul_eq_zero, hpos.ne', false_or] at a0 a1
      rw [a0, a1] at hcs
      norm_num at hcs
  have h := hG L hsm hper hLK
  have e0 : L 0 = fun σ => z + R • circlePoint (σ + φ) := by
    funext σ; simp only [hL, sub_zero, one_mul, zero_mul, add_zero]
  have e1 : L 1 = fun σ => z + ρ • circlePoint σ := by
    funext σ; simp only [hL, sub_self, zero_mul, one_mul, zero_add, add_zero]
  rw [e0, e1] at h
  exact h

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

/-!
# Seifert push-off: Gauss-integral tools

* moving the first loop through a fixed-pole homotopy in `S³`;
* the Gauss integral of a constant first loop vanishes;
* a pole missing the radial projection of a surface `f : Plane → R4` and a loop.
-/


noncomputable section

namespace HryniewiczCriterion

lemma sf_contDiff_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : E → R4} (hy : ContDiff ℝ 2 y) (hne : ∀ p, y p ≠ 0) :
    ContDiff ℝ 2 fun p => radialNormalize (y p) := by
  have hd : ContDiff ℝ 2 fun p => dot4 (y p) (y p) := gl_contDiff_dot4 hy hy
  have hs : ContDiff ℝ 2 fun p => euclidNorm (y p) :=
    hd.sqrt fun p => (gl_dot4_self_pos (hne p)).ne'
  exact (hs.inv fun p => (gl_euclidNorm_pos (hne p)).ne').smul hy

lemma sf_ne_normalize {x y : R4} (hx0 : x ≠ 0) (h : ∀ μ : ℝ, 0 < μ → x ≠ μ • y) :
    y ≠ radialNormalize x := fun he =>
  h (euclidNorm x) (gl_euclidNorm_pos hx0) (gl_eq_smul_of_normalize hx0 he.symm)

/-- Homotopy invariance on `S³` with a fixed pole: the first loop moves through a `C²` family
of closed loops missing the second loop and the pole. -/
theorem sf_gauss_homotopy_left (N : R4) (hN : euclidNorm N = 1) (R : ℝ → ℝ → R4) (γ : ℝ → R4)
    (hR : ContDiff ℝ 2 (Function.uncurry R)) (hγ : ContDiff ℝ 2 γ)
    (hRper : ∀ τ s, R τ (s + 1) = R τ s) (hγper : ∀ t, γ (t + 1) = γ t)
    (hRunit : ∀ τ s, euclidNorm (R τ s) = 1) (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (hRN : ∀ τ s, R τ s ≠ N) (hγN : ∀ t, γ t ≠ N) (hne : ∀ τ s t, R τ s ≠ γ t) :
    gaussLinkingIntegral N (R 0) γ = gaussLinkingIntegral N (R 1) γ := by
  have hNN : dot4 N N = 1 := gl_dot4_self_of_unit hN
  set A : ℝ → ℝ → R4 := fun τ s => stereographicFrom N (R τ s)
  set B : ℝ → ℝ → R4 := fun _ t => stereographicFrom N (γ t)
  have hA : ContDiff ℝ 2 (Function.uncurry A) :=
    gl_contDiff_stereo N hR fun p => tw_one_sub_dot_ne hN (hRunit _ _) (hRN _ _)
  have hB : ContDiff ℝ 2 (Function.uncurry B) :=
    gl_contDiff_stereo N (hγ.comp contDiff_snd) fun p => tw_one_sub_dot_ne hN (hγunit _) (hγN _)
  have h := gl_gauss_homotopy N A B hA hB (fun τ s => by simp only [A, hRper])
    (fun _ t => by simp only [B, hγper])
    (fun τ s t => by rw [gl_dot4_sub_left, gl_stereo_dot_N hNN, gl_stereo_dot_N hNN, sub_zero])
    (fun τ s t => tw_stereo_ne hN (hRunit τ s) (hγunit t) (hRN τ s) (hγN t) (hne τ s t))
  rw [tw_gauss_eq_G, tw_gauss_eq_G]
  exact congrArg (fun x => (4 * Real.pi)⁻¹ * x) h

/-- A constant first loop has vanishing Gauss integral. -/
lemma sf_gauss_const (N c : R4) (γ : ℝ → R4) : gaussLinkingIntegral N (fun _ => c) γ = 0 := by
  have h0 : ∀ b c' : R4, volumeIn N 0 b c' = 0 := fun b c' =>
    Matrix.det_eq_zero_of_row_eq_zero 1 (fun j => by simp)
  simp [gaussLinkingIntegral, h0]

/-- The cone `{c • f v}` over a differentiable surface is null. -/
lemma sf_cone_null (f : Plane → R4) (hf : Differentiable ℝ f) :
    volume {M : R4 | ∃ (c : ℝ) (v : Plane), M = c • f v} = 0 := by
  set F : R4 → R4 := fun p => p 2 • f ![p 0, p 1]
  have hsub : {M : R4 | ∃ (c : ℝ) (v : Plane), M = c • f v} ⊆ F '' {p : R4 | p 3 = 0} := by
    rintro M ⟨c, v, rfl⟩
    refine ⟨![v 0, v 1, c, 0], by simp, ?_⟩
    have hv : (![v 0, v 1] : Plane) = v := by ext i; fin_cases i <;> rfl
    simp [F, hv]
  have hF : DifferentiableOn ℝ F {p : R4 | p 3 = 0} := by
    intro p _
    have hl : Differentiable ℝ (fun p : R4 => (![p 0, p 1] : Plane)) := by
      rw [differentiable_pi]; intro i; fin_cases i <;> simp <;> fun_prop
    exact ((differentiableAt_apply 2 p).smul ((hf _).comp p (hl p))).differentiableWithinAt
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF gl_hyperplane_null)

/-- A unit pole missing the radial projection of a surface and a unit loop. -/
theorem sf_exists_pole (f : Plane → R4) (hf : Differentiable ℝ f) (g : ℝ → R4)
    (hg : Differentiable ℝ g) (hgu : ∀ s, euclidNorm (g s) = 1) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ v, f v ≠ 0 → radialNormalize (f v) ≠ N) ∧
      ∀ s, g s ≠ N := by
  set bad := {M : R4 | ∃ (c : ℝ) (v : Plane), M = c • f v} ∪
    {M : R4 | ∃ l c s : ℝ, 0 < l ∧ M = l⁻¹ • (c • g s - (1 - l) • (0 : R4))}
  have hU : volume bad = 0 := measure_union_null (sf_cone_null f hf) (gl_bad_null g hg 0)
  have hne : (badᶜ).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hpos := isOpen_univ.measure_pos (volume : Measure R4) univ_nonempty
    rw [← hemp, hU] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨M, hM⟩ := hne
  have hM1 : ∀ (c : ℝ) v, M ≠ c • f v := fun c v he => hM (Or.inl ⟨c, v, he⟩)
  have hM2 : ∀ c s, M ≠ c • g s := fun c s he => hM (Or.inr ⟨1, c, s, one_pos, by simp [he]⟩)
  have hM0 : M ≠ 0 := fun h0 => hM2 0 0 (by simp [h0])
  refine ⟨radialNormalize M, gl_euclidNorm_normalize hM0, ?_, ?_⟩
  · intro v hv he
    have h1 := gl_eq_smul_of_normalize hv he
    have h2 := gl_eq_smul_of_normalize hM0 rfl
    apply hM1 (euclidNorm M * (euclidNorm (f v))⁻¹) v
    calc M = euclidNorm M • radialNormalize M := h2
      _ = (euclidNorm M * (euclidNorm (f v))⁻¹) • (euclidNorm (f v) • radialNormalize M) := by
          rw [smul_smul, mul_assoc, inv_mul_cancel₀ (gl_euclidNorm_pos hv).ne', mul_one]
      _ = _ := by rw [← h1]
  · intro s he
    apply hM2 (euclidNorm M) s
    rw [he]
    exact gl_eq_smul_of_normalize hM0 rfl

end HryniewiczCriterion

/-!
# Planar homotopy invariance of surface-loop Gauss integrals

Reparametrize the homotopy parameter by the smooth transition function, so the homotopy is
`C²` on all of `ℝ²` and stays in `K` for every `τ`; then apply `sf_gauss_homotopy_left`.
-/


noncomputable section

namespace HryniewiczCriterion

theorem gaussLinkingIntegral_planar_homotopy' (E : Plane → R4) (U : Set Plane) (hU : IsOpen U)
    (K : Set Plane) (hKU : K ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ K, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hKγ : ∀ v ∈ K, ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N) (hNE : ∀ v ∈ K, E v ≠ N)
    (L : ℝ → ℝ → Plane) (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hLper : ∀ τ s, L τ (s + 1) = L τ s) (hLK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K) :
    gaussLinkingIntegral N (fun s => E (L 0 s)) γ =
      gaussLinkingIntegral N (fun s => E (L 1 s)) γ := by
  set φ := Real.smoothTransition
  have hφ : ∀ τ, φ τ ∈ Icc (0 : ℝ) 1 := fun τ =>
    ⟨Real.smoothTransition.nonneg τ, Real.smoothTransition.le_one τ⟩
  have hφ0 : φ 0 = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  have hφ1 : φ 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
  have hM : ContDiff ℝ 2 (fun p : ℝ × ℝ => L (φ p.1) p.2) :=
    hL.comp ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  have hR : ContDiff ℝ 2 (Function.uncurry fun τ s => E (L (φ τ) s)) :=
    hE.comp_contDiff hM fun p => hKU (hLK _ (hφ p.1) p.2)
  have h := sf_gauss_homotopy_left N hN (fun τ s => E (L (φ τ) s)) γ hR hγ
    (fun τ s => by simp only [hLper]) hγper
    (fun τ s => hEunit _ (hLK _ (hφ τ) s)) hγunit
    (fun τ s => hNE _ (hLK _ (hφ τ) s)) hNγ
    (fun τ s t => hKγ _ (hLK _ (hφ τ) s) t)
  simpa only [hφ0, hφ1] using h

end HryniewiczCriterion

/-!
# `gaussLinkingIntegral_strip_bump_jump`

Raising the graph loop `ℓ_g` to `ℓ_{g+b}` over the single puncture `z = Ψ(a₀, s₀)` adds the Gauss
integral of a small round loop around `z`:
* lens identity (`jl_lens`): `G(ℓ_{g+b}) - G(ℓ_g) = G(lens)`, by substitution only;
* stages 1–4 (`jm_stage1`–`jm_stage4`): `lens ≃ small strip circle ≃ linearization ≃ z + ρ ∂`
  inside `closedUnitDisk \ Z`, each by the planar homotopy lemma.
-/


noncomputable section

namespace HryniewiczCriterion

lemma jm_open_disk {c : Plane} (hc : c ∈ openUnitDisk) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) (s : ℝ) :
    jb_psi c μ s ∈ openUnitDisk := by
  have hc' : c 0 ^ 2 + c 1 ^ 2 < 1 := hc
  have hp : Real.cos (2 * Real.pi * s) ^ 2 + Real.sin (2 * Real.pi * s) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  show (jb_psi c μ s) 0 ^ 2 + (jb_psi c μ s) 1 ^ 2 < 1
  rw [jb_psi_apply0, jb_psi_apply1]
  set p0 := Real.cos (2 * Real.pi * s)
  set p1 := Real.sin (2 * Real.pi * s)
  have hm : 0 ≤ μ * (1 - μ) := mul_nonneg h0 (by linarith)
  have hm2 : 0 < (1 - μ) ^ 2 := by have : 0 < 1 - μ := by linarith
                                   positivity
  nlinarith [mul_nonneg hm (add_nonneg (sq_nonneg (c 0 - p0)) (sq_nonneg (c 1 - p1))),
    mul_pos hm2 (by linarith : (0 : ℝ) < 1 - (c 0 ^ 2 + c 1 ^ 2)),
    mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 - (c 0 ^ 2 + c 1 ^ 2))]

lemma jm_ev {f : ℝ → ℝ} (hf : Continuous f) {X : ℝ} (h0 : f 0 < X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), f r < X :=
  nhdsWithin_le_nhds (hf.continuousAt.eventually_lt continuousAt_const h0)

theorem gaussLinkingIntegral_strip_bump_jump' (E : Plane → R4) (U : Set Plane) (hU : IsOpen U)
    (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N)
    (c : Plane) (hc : c ∈ openUnitDisk) (z : Plane) (a₀ s₀ δ : ℝ)
    (hz : z = c + a₀ • (circlePoint s₀ - c)) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (g b : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hb : ContDiff ℝ 2 b)
    (hgper : ∀ s, g (s + 1) = g s) (hbper : ∀ s, b (s + 1) = b s)
    (hgb : ∀ s, 0 ≤ g s ∧ 0 ≤ b s ∧ g s + b s ≤ 1)
    (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ)
    (hlow : g s₀ < a₀) (hhigh : a₀ < g s₀ + b s₀)
    (hstrip : ∀ s μ : ℝ, |s - s₀| ≤ 2 * δ → 0 ≤ μ → μ ≤ 1 →
      c + μ • (circlePoint s - c) ∈ Z → c + μ • (circlePoint s - c) = z)
    (hgZ : ∀ s, c + g s • (circlePoint s - c) ∉ Z)
    (hgbZ : ∀ s, c + (g s + b s) • (circlePoint s - c) ∉ Z) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (c + (g s + b s) • (circlePoint s - c))) γ =
        gaussLinkingIntegral N (fun s => E (c + g s • (circlePoint s - c))) γ +
          gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ := by
  have hpi := Real.pi_pos
  have ha0 : 0 < a₀ := lt_of_le_of_lt (hgb s₀).1 hlow
  have ha1 : a₀ < 1 := lt_of_lt_of_le hhigh (hgb s₀).2.2
  have hz' : z = jb_psi c a₀ s₀ := hz
  -- the region `K` and the functional `G`
  set K : Set Plane := closedUnitDisk \ (Z : Set Plane) with hKdef
  have hKU : K ⊆ U := fun v hv => hDU hv.1
  have hEunitK : ∀ v ∈ K, euclidNorm (E v) = 1 := fun v hv => hEunit v hv.1
  have hKγ : ∀ v ∈ K, ∀ t, E v ≠ γ t := fun v hv => hmiss v hv.1 hv.2
  have hNEK : ∀ v ∈ K, E v ≠ N := fun v hv => hNE v hv.1
  set G : (ℝ → Plane) → ℝ := fun ℓ => gaussLinkingIntegral N (fun s => E (ℓ s)) γ with hGdef
  have hG : jm_HInv K G := fun L hL hLper hLK =>
    gaussLinkingIntegral_planar_homotopy' E U hU K hKU hE hEunitK γ hγ hγper hγunit hKγ N hN hNγ
      hNEK L hL hLper hLK
  -- strip membership
  have hK1 : ∀ M S, 0 ≤ M → M ≤ 1 → |S - s₀| ≤ 2 * δ → (S = s₀ → M ≠ a₀) → jb_psi c M S ∈ K := by
    intro M S h0 h1 hS hne
    refine ⟨jb_mem_disk hc h0 h1 S, fun hZ => ?_⟩
    have h2 := hstrip S M hS h0 h1 hZ
    have h3 := jb_psi_inj hc h0 ha0 (by linarith) (h2.trans hz')
    exact hne h3.1 h3.2
  -- a ball around `z`
  have hzO : z ∈ openUnitDisk := hz' ▸ jm_open_disk hc ha0.le ha1 s₀
  have hWopen : IsOpen (openUnitDisk ∩ ((Z.erase z : Finset Plane) : Set Plane)ᶜ) := by
    refine IsOpen.inter ?_ (Z.erase z).isClosed.isOpen_compl
    show IsOpen {u : Plane | u 0 ^ 2 + u 1 ^ 2 < 1}
    exact isOpen_lt (by fun_prop) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWopen z ⟨hzO, by simp⟩
  have hnear : ∀ w : Plane, w 0 ^ 2 + w 1 ^ 2 < ε ^ 2 → w ≠ 0 → z + w ∈ K := by
    intro w hw hw0
    have hd : z + w ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, pi_norm_lt_iff hε]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · show |w 0| < ε
        exact abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w 1)]) hε.le
      · show |w 1| < ε
        exact abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w 0)]) hε.le
    obtain ⟨hO, hnot⟩ := hball hd
    refine ⟨le_of_lt (show (z + w) 0 ^ 2 + (z + w) 1 ^ 2 < 1 from hO), fun hZ => hnot ?_⟩
    simp only [Finset.coe_erase, mem_diff, Finset.mem_coe, mem_singleton_iff]
    exact ⟨hZ, fun h => hw0 (by simpa using h)⟩
  -- the linearization at the puncture
  set u : Plane := ![Real.cos (2 * Real.pi * s₀) - c 0, Real.sin (2 * Real.pi * s₀) - c 1] with hu
  set v : Plane := ![-(a₀ * (2 * Real.pi * Real.sin (2 * Real.pi * s₀))),
    a₀ * (2 * Real.pi * Real.cos (2 * Real.pi * s₀))] with hv
  have hu0 : u 0 = Real.cos (2 * Real.pi * s₀) - c 0 := rfl
  have hu1 : u 1 = Real.sin (2 * Real.pi * s₀) - c 1 := rfl
  have hv0 : v 0 = -(a₀ * (2 * Real.pi * Real.sin (2 * Real.pi * s₀))) := rfl
  have hv1 : v 1 = a₀ * (2 * Real.pi * Real.cos (2 * Real.pi * s₀)) := rfl
  have hDpos : 0 < u 0 * v 1 - u 1 * v 0 := by
    have hc' : c 0 ^ 2 + c 1 ^ 2 < 1 := hc
    have hq := Real.cos_sq_add_sin_sq (2 * Real.pi * s₀)
    have e : u 0 * v 1 - u 1 * v 0 = 2 * Real.pi * a₀ *
        (1 - (c 0 * Real.cos (2 * Real.pi * s₀) + c 1 * Real.sin (2 * Real.pi * s₀))) := by
      rw [hu0, hu1, hv0, hv1]; linear_combination (2 * Real.pi * a₀) * hq
    rw [e]
    have : c 0 * Real.cos (2 * Real.pi * s₀) + c 1 * Real.sin (2 * Real.pi * s₀) < 1 := by
      nlinarith [sq_nonneg (c 0 - Real.cos (2 * Real.pi * s₀)),
        sq_nonneg (c 1 - Real.sin (2 * Real.pi * s₀))]
    have : 0 < 2 * Real.pi * a₀ := by positivity
    nlinarith
  set ar := (u 1 - v 0) / 2 with har
  set ai := (-v 1 - u 0) / 2 with hai
  set br := (-v 0 - u 1) / 2 with hbr
  set bi := (u 0 - v 1) / 2 with hbi
  have hab : br ^ 2 + bi ^ 2 < ar ^ 2 + ai ^ 2 := by
    have : ar ^ 2 + ai ^ 2 - (br ^ 2 + bi ^ 2) = u 0 * v 1 - u 1 * v 0 := by
      rw [har, hai, hbr, hbi]; ring
    linarith
  set α : ℂ := ⟨ar, ai⟩ with hα
  set A := ‖α‖ with hA
  set φ := Complex.arg α with hφ
  have hAc : A * Real.cos φ = ar := Complex.norm_mul_cos_arg α
  have hAs : A * Real.sin φ = ai := Complex.norm_mul_sin_arg α
  have hApos : 0 < A := by
    rw [hA, norm_pos_iff]
    intro h0
    have h1 : ar = 0 := by simpa [hα] using congrArg Complex.re h0
    have h2 : ai = 0 := by simpa [hα] using congrArg Complex.im h0
    rw [h1, h2] at hab
    nlinarith [sq_nonneg br, sq_nonneg bi]
  -- the radius `r`
  set K2 := 2 * Real.pi + 4 * Real.pi ^ 2 with hK2
  set Ws := u 0 ^ 2 + u 1 ^ 2 + v 0 ^ 2 + v 1 ^ 2 with hWs
  set Dd := u 0 * v 1 - u 1 * v 0 with hDd
  set Bd := |u 0| + |u 1| + |v 0| + |v 1| with hBd
  set Bα := |ar| + |ai| + |br| + |bi| with hBα
  have ev := ((((((((jm_ev (f := fun r => r) continuous_id (X := a₀) (by simpa using ha0)).and
    (jm_ev (f := fun r => r) continuous_id (X := 1 - a₀) (by simp; linarith))).and
    (jm_ev (f := fun r => r) continuous_id (X := 3 * δ / 2) (by simp; positivity))).and
    (jm_ev (f := fun r => 2 * Real.pi * r) (by fun_prop) (X := 1) (by simp))).and
    (jm_ev (f := fun r => K2 * r) (by fun_prop) (X := 1) (by simp))).and
    (jm_ev (f := fun r => 2 * K2 ^ 2 * r ^ 2 * Ws) (by fun_prop) (X := Dd ^ 2)
      (by simp; positivity))).and
    (jm_ev (f := fun r => 2 * r ^ 2 * (Bd + 1) ^ 2) (by fun_prop) (X := ε ^ 2)
      (by simp; positivity))).and
    (jm_ev (f := fun r => 2 * r ^ 2 * Bα ^ 2) (by fun_prop) (X := ε ^ 2) (by simp; positivity))).and
    (jm_ev (f := fun r => r * A) (by fun_prop) (X := ε) (by simpa using hε))
  obtain ⟨r, ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, hr⟩ :=
    (ev.and self_mem_nhdsWithin).exists
  have hr : (0 : ℝ) < r := hr
  refine ⟨ε, hε, fun ρ hρ hρε => ?_⟩
  -- the lens identity
  set ℓ₁ : ℝ → Plane := fun x => jb_psi c (g x + b x) x with hℓ₁
  set ℓ₀ : ℝ → Plane := fun x => jb_psi c (g x) x with hℓ₀
  set lens : ℝ → Plane := fun σ => jb_psi c (g (jl_sweep s₀ (3 * δ / 2) σ) + jb_B b s₀ δ σ)
    (jl_sweep s₀ (3 * δ / 2) σ) with hlens
  have hcp := jb_cp_contDiff
  have hℓ₁c : ContDiff ℝ 2 ℓ₁ := by simp only [hℓ₁, jb_psi]; fun_prop
  have hℓ₀c : ContDiff ℝ 2 ℓ₀ := by simp only [hℓ₀, jb_psi]; fun_prop
  have hlensc : ContDiff ℝ 2 lens := by
    have hB := jb_B_contDiff hb s₀ δ
    have hsw := jb_sweep_contDiff s₀ (3 * δ / 2)
    simp only [hlens, jb_psi]; fun_prop
  have hℓ₁K : ∀ x, ℓ₁ x ∈ K := fun x =>
    ⟨jb_mem_disk hc (add_nonneg (hgb x).1 (hgb x).2.1) (hgb x).2.2 x, hgbZ x⟩
  have hℓ₀K : ∀ x, ℓ₀ x ∈ K := fun x =>
    ⟨jb_mem_disk hc (hgb x).1 (by linarith [(hgb x).2.1, (hgb x).2.2]) x, hgZ x⟩
  have hlensK : ∀ σ, lens σ ∈ K := by
    intro σ
    rcases le_total 0 (Real.sin (2 * Real.pi * σ)) with hs | hs
    · have : lens σ = ℓ₁ (jl_sweep s₀ (3 * δ / 2) σ) := by
        simp only [hlens, hℓ₁, jb_B_up hδ hδ' hbsupp hs]
      rw [this]; exact hℓ₁K _
    · have : lens σ = ℓ₀ (jl_sweep s₀ (3 * δ / 2) σ) := by
        simp only [hlens, hℓ₀, jb_B_low hδ hδ' hbsupp hs, add_zero]
      rw [this]; exact hℓ₀K _
  have hchart : ∀ ℓ : ℝ → Plane, ContDiff ℝ 2 ℓ → (∀ x, ℓ x ∈ K) →
      ContDiff ℝ 1 (fun x => stereographicFrom N (E (ℓ x))) := fun ℓ hℓ hℓK =>
    (gl_contDiff_stereo N (hE.comp_contDiff hℓ fun x => hKU (hℓK x)) fun x =>
      tw_one_sub_dot_ne hN (hEunitK _ (hℓK x)) (hNEK _ (hℓK x))).of_le (by norm_num)
  have hsep : ∀ ℓ : ℝ → Plane, (∀ x, ℓ x ∈ K) → ∀ x t,
      stereographicFrom N (E (ℓ x)) - stereographicFrom N (γ t) ≠ 0 := fun ℓ hℓK x t =>
    sub_ne_zero.2 (tw_stereo_ne hN (hEunitK _ (hℓK x)) (hγunit t) (hNEK _ (hℓK x)) (hNγ t)
      (hKγ _ (hℓK x) t))
  have hγc : ContDiff ℝ 1 (fun t => stereographicFrom N (γ t)) :=
    (gl_contDiff_stereo N hγ fun t => tw_one_sub_dot_ne hN (hγunit t) (hNγ t)).of_le (by norm_num)
  have hcp_per : ∀ μ x, jb_psi c μ (x + 1) = jb_psi c μ x := fun μ x => by
    simp only [jb_psi, jb_cp_periodic]
  have hlensG : G lens = G ℓ₁ - G ℓ₀ := by
    have h := jl_lens N (fun x => stereographicFrom N (E (ℓ₁ x)))
      (fun x => stereographicFrom N (E (ℓ₀ x))) (fun t => stereographicFrom N (γ t))
      (fun σ => stereographicFrom N (E (lens σ))) s₀ (3 * δ / 2) (by linarith)
      (hchart ℓ₁ hℓ₁c hℓ₁K) (hchart ℓ₀ hℓ₀c hℓ₀K) hγc (hchart lens hlensc hlensK)
      (fun x => by simp only [hℓ₁, hgper, hbper, hcp_per])
      (fun x => by simp only [hℓ₀, hgper, hcp_per])
      (hsep ℓ₁ hℓ₁K) (hsep ℓ₀ hℓ₀K) (hsep lens hlensK)
      (fun x hx => by
        filter_upwards [jb_b_eventually_zero hδ hδ' hbsupp hx] with y hy
        simp only [hℓ₁, hℓ₀, hy, add_zero])
      (fun σ hσ => by
        filter_upwards [jb_B_eventually_up hδ hδ' hbsupp hσ] with σ' h'
        simp only [hlens, hℓ₁, h'])
      (fun σ hσ => by
        filter_upwards [jb_B_eventually_low hδ hδ' hbsupp hσ] with σ' h'
        simp only [hlens, hℓ₀, h', add_zero])
    simp only [hGdef, tw_gauss_eq_G, h]
    ring
  -- the four stages
  have s1 := jm_stage1 hG hδ hδ' hg hb hgb hbsupp hlow hhigh hr c1.le (by linarith [c2.le])
    c3.le hK1
  have s2 := jm_stage2 hG hz' ha0.le ha1.le hu0 hu1 hv0 hv1 hr c4.le c5.le c6 c7 hnear
  have s3 := jm_stage3 hG (z := z) hr hab c8 hnear
  have s4 := jm_stage4 hG (z := z) (φ := φ / (2 * Real.pi)) (by positivity : 0 < r * A) c9 hρ hρε hnear
  have e23 : (fun σ => z + ((r * Real.sin (2 * Real.pi * σ)) • u - (r * Real.cos (2 * Real.pi * σ)) • v)) =
      fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] + Real.sin (2 * Real.pi * σ) • ![-ai, ar] +
        (Real.cos (2 * Real.pi * σ) • ![br, bi] + Real.sin (2 * Real.pi * σ) • ![bi, -br])) := by
    funext σ
    congr 1
    ext i
    fin_cases i
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Fin.zero_eta]
      rw [har, hai, hbr, hbi]; ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
      rw [har, hai, hbr, hbi]; ring
  have e34 : (fun σ => z + r • (Real.cos (2 * Real.pi * σ) • ![ar, ai] +
      Real.sin (2 * Real.pi * σ) • ![-ai, ar])) =
      fun σ => z + (r * A) • circlePoint (σ + φ / (2 * Real.pi)) := by
    funext σ
    have harg : 2 * Real.pi * (σ + φ / (2 * Real.pi)) = 2 * Real.pi * σ + φ := by
      field_simp
    congr 1
    ext i
    fin_cases i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, circlePoint,
        Fin.zero_eta, harg, Real.cos_add]
      rw [← hAc, ← hAs]; ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, circlePoint, Fin.mk_one, harg, Real.sin_add]
      rw [← hAc, ← hAs]; ring
  rw [e23] at s2
  rw [e34] at s3
  have hfinal : G lens = G (fun σ => z + ρ • circlePoint σ) := by
    rw [s1, s2, s3, s4]
  have : G ℓ₁ = G ℓ₀ + G (fun σ => z + ρ • circlePoint σ) := by linarith
  exact this

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N)
    (c : Plane) (hc : c ∈ openUnitDisk) (z : Plane) (a₀ s₀ δ : ℝ)
    (hz : z = c + a₀ • (circlePoint s₀ - c)) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (g b : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hb : ContDiff ℝ 2 b)
    (hgper : ∀ s, g (s + 1) = g s) (hbper : ∀ s, b (s + 1) = b s)
    (hgb : ∀ s, 0 ≤ g s ∧ 0 ≤ b s ∧ g s + b s ≤ 1)
    (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ)
    (hlow : g s₀ < a₀) (hhigh : a₀ < g s₀ + b s₀)
    (hstrip : ∀ s μ : ℝ, |s - s₀| ≤ 2 * δ → 0 ≤ μ → μ ≤ 1 →
      c + μ • (circlePoint s - c) ∈ Z → c + μ • (circlePoint s - c) = z)
    (hgZ : ∀ s, c + g s • (circlePoint s - c) ∉ Z)
    (hgbZ : ∀ s, c + (g s + b s) • (circlePoint s - c) ∉ Z) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (c + (g s + b s) • (circlePoint s - c))) γ =
        gaussLinkingIntegral N (fun s => E (c + g s • (circlePoint s - c))) γ +
          gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ :=
  gaussLinkingIntegral_strip_bump_jump' E U hU hDU hE hEunit γ hγ hγper hγunit Z hmiss N hN hNγ hNE c hc z a₀ s₀ δ hz hδ hδ' g b hg hb hgper hbper hgb hbsupp hlow hhigh hstrip hgZ hgbZ
