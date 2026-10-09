-- Prove2me | solution 1 for HryniewiczCriterion.gaussLinkingIntegral_small_transverse_loop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T22:53:14.311344+00:00
-- url     : https://prove2.me/submissions/a680160c-da4c-46cf-8867-afa611750413

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
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Deriv.Shift
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_meridian_eq_one

open HryniewiczCriterion
open scoped ContDiff
open MeasureTheory Set
open Set
open Set MeasureTheory
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
# Elementary estimates for the tube lemma

Coordinate bounds for unit vectors, `|⟨x,y⟩| ≤ 4‖x‖‖y‖` and `|det| ≤ 24 ∏ ‖·‖` in the sup norm,
extrema of continuous `1`-periodic functions, the second-order Taylor bound for a `C²` curve,
and a positive lower bound for `‖γ(t+h) - γ(t)‖` away from `h ∈ ℤ` for a loop injective mod `1`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma tw_abs_coord_le (x : R4) (i : Fin 4) : |x i| ≤ ‖x‖ := by
  have h := norm_le_pi_norm x i
  rwa [Real.norm_eq_abs] at h

lemma tw_norm_le_one_of_unit {y : R4} (hy : euclidNorm y = 1) : ‖y‖ ≤ 1 := by
  have h1 := gl_dot4_self_of_unit hy
  simp only [dot4, Fin.sum_univ_four] at h1
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have hsq : y i * y i ≤ 1 := by
    fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1),
      mul_self_nonneg (y 2), mul_self_nonneg (y 3)]
  constructor <;> nlinarith

lemma tw_abs_dot4_le (x y : R4) : |dot4 x y| ≤ 4 * (‖x‖ * ‖y‖) := by
  have key : ∀ i, |x i * y i| ≤ ‖x‖ * ‖y‖ := fun i => by
    rw [abs_mul]
    exact mul_le_mul (tw_abs_coord_le x i) (tw_abs_coord_le y i) (abs_nonneg _) (norm_nonneg _)
  simp only [dot4, Fin.sum_univ_four]
  rw [abs_le]
  constructor <;> linarith [(abs_le.mp (key 0)).1, (abs_le.mp (key 0)).2, (abs_le.mp (key 1)).1,
    (abs_le.mp (key 1)).2, (abs_le.mp (key 2)).1, (abs_le.mp (key 2)).2, (abs_le.mp (key 3)).1,
    (abs_le.mp (key 3)).2]

lemma tw_abs_det4_le (x y z w : R4) : |gl_det4 x y z w| ≤ 24 * (‖x‖ * ‖y‖ * ‖z‖ * ‖w‖) := by
  have key : ∀ i j k l, |x i * y j * z k * w l| ≤ ‖x‖ * ‖y‖ * ‖z‖ * ‖w‖ := fun i j k l => by
    rw [abs_mul, abs_mul, abs_mul]
    gcongr
    · exact tw_abs_coord_le x i
    · exact tw_abs_coord_le y j
    · exact tw_abs_coord_le z k
    · exact tw_abs_coord_le w l
  simp only [gl_det4]
  rw [abs_le]
  constructor <;> linarith [(abs_le.mp (key 0 1 2 3)).1, (abs_le.mp (key 0 1 3 2)).1,
    (abs_le.mp (key 0 2 1 3)).1, (abs_le.mp (key 0 2 3 1)).1, (abs_le.mp (key 0 3 1 2)).1,
    (abs_le.mp (key 0 3 2 1)).1, (abs_le.mp (key 1 0 2 3)).1, (abs_le.mp (key 1 0 3 2)).1,
    (abs_le.mp (key 1 2 0 3)).1, (abs_le.mp (key 1 2 3 0)).1, (abs_le.mp (key 1 3 0 2)).1,
    (abs_le.mp (key 1 3 2 0)).1, (abs_le.mp (key 2 0 1 3)).1, (abs_le.mp (key 2 0 3 1)).1,
    (abs_le.mp (key 2 1 0 3)).1, (abs_le.mp (key 2 1 3 0)).1, (abs_le.mp (key 2 3 0 1)).1,
    (abs_le.mp (key 2 3 1 0)).1, (abs_le.mp (key 3 0 1 2)).1, (abs_le.mp (key 3 0 2 1)).1,
    (abs_le.mp (key 3 1 0 2)).1, (abs_le.mp (key 3 1 2 0)).1, (abs_le.mp (key 3 2 0 1)).1,
    (abs_le.mp (key 3 2 1 0)).1,
    (abs_le.mp (key 0 1 2 3)).2, (abs_le.mp (key 0 1 3 2)).2,
    (abs_le.mp (key 0 2 1 3)).2, (abs_le.mp (key 0 2 3 1)).2, (abs_le.mp (key 0 3 1 2)).2,
    (abs_le.mp (key 0 3 2 1)).2, (abs_le.mp (key 1 0 2 3)).2, (abs_le.mp (key 1 0 3 2)).2,
    (abs_le.mp (key 1 2 0 3)).2, (abs_le.mp (key 1 2 3 0)).2, (abs_le.mp (key 1 3 0 2)).2,
    (abs_le.mp (key 1 3 2 0)).2, (abs_le.mp (key 2 0 1 3)).2, (abs_le.mp (key 2 0 3 1)).2,
    (abs_le.mp (key 2 1 0 3)).2, (abs_le.mp (key 2 1 3 0)).2, (abs_le.mp (key 2 3 0 1)).2,
    (abs_le.mp (key 2 3 1 0)).2, (abs_le.mp (key 3 0 1 2)).2, (abs_le.mp (key 3 0 2 1)).2,
    (abs_le.mp (key 3 1 0 2)).2, (abs_le.mp (key 3 1 2 0)).2, (abs_le.mp (key 3 2 0 1)).2,
    (abs_le.mp (key 3 2 1 0)).2]

/-! ### Extrema of periodic functions -/

lemma tw_periodic_bdd {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ M, ∀ t, f t ≤ M := by
  obtain ⟨M, hM⟩ := (hp.compact_of_continuous one_ne_zero hf).bddAbove
  exact ⟨M, fun t => hM ⟨t, rfl⟩⟩

lemma tw_periodic_min {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ t₀, ∀ t, f t₀ ≤ f t := by
  obtain ⟨y, ⟨t₀, rfl⟩, hy⟩ :=
    (hp.compact_of_continuous one_ne_zero hf).exists_isLeast (range_nonempty f)
  exact ⟨t₀, fun t => hy ⟨t, rfl⟩⟩

lemma tw_periodic_int {γ : ℝ → R4} (hper : ∀ s, γ (s + 1) = γ s) (x : ℝ) (n : ℤ) :
    γ (x + n) = γ x := by
  have hp : Function.Periodic γ 1 := hper
  simpa using (hp.int_mul n) x

/-! ### Taylor bound -/

lemma tw_taylor {γ : ℝ → R4} (hγ : ContDiff ℝ 2 γ) {L : ℝ}
    (hL : ∀ x, ‖deriv (deriv γ) x‖ ≤ L) (t h : ℝ) :
    ‖γ (t + h) - γ t - h • deriv γ t‖ ≤ L * h ^ 2 := by
  have hd1 : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv γ) := by
    have : ContDiff ℝ 1 (deriv γ) := hγ.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  -- Lipschitz bound for `γ'`
  have hlip : ∀ x, ‖deriv γ x - deriv γ t‖ ≤ L * |x - t| := by
    intro x
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hd2 x)
      (fun x _ => hL x) (mem_univ t) (mem_univ x)
    rwa [Real.norm_eq_abs] at h
  set g : ℝ → R4 := fun x => γ x - x • deriv γ t
  have hg : ∀ x, HasDerivAt g (deriv γ x - deriv γ t) x := fun x =>
    (hd1 x).hasDerivAt.sub ((hasDerivAt_id x).smul_const (deriv γ t) |>.congr_deriv (by simp))
  have hb : ∀ x ∈ uIcc t (t + h), ‖deriv g x‖ ≤ L * |h| := by
    intro x hx
    rw [(hg x).deriv]
    refine (hlip x).trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hL 0)))
    rcases le_total t (t + h) with h0 | h0
    · rw [uIcc_of_le h0] at hx
      rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith)]; linarith [hx.2]
    · rw [uIcc_of_ge h0] at hx
      rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith)]; linarith [hx.1]
  have hmv := (convex_uIcc t (t + h)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (hg x).differentiableAt) hb left_mem_uIcc right_mem_uIcc
  have e : g (t + h) - g t = γ (t + h) - γ t - h • deriv γ t := by
    simp only [g, add_smul]; abel
  rw [e, Real.norm_eq_abs, add_sub_cancel_left] at hmv
  calc _ ≤ L * |h| * |h| := hmv
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ### Orthogonality of a curve on the unit sphere and its velocity -/

lemma tw_dot_deriv_eq_zero {γ : ℝ → R4} (hd : Differentiable ℝ γ)
    (hunit : ∀ s, euclidNorm (γ s) = 1) (t : ℝ) : dot4 (γ t) (deriv γ t) = 0 := by
  have h := gl_hasDerivAt_dot4 (hd t).hasDerivAt (hd t).hasDerivAt
  have hc : (fun x => dot4 (γ x) (γ x)) = fun _ => (1 : ℝ) :=
    funext fun x => gl_dot4_self_of_unit (hunit x)
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const t (1 : ℝ))
  rw [gl_dot4_comm (deriv γ t) (γ t)] at h0
  linarith

/-! ### Far-away separation for a loop injective modulo `1` -/

lemma tw_far {γ : ℝ → R4} (hc : Continuous γ) (hper : ∀ s, γ (s + 1) = γ s)
    (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n) {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ c > 0, ∀ t h, η ≤ |h| → |h| ≤ 1 / 2 → c ≤ ‖γ (t + h) - γ t‖ := by
  set K : Set (ℝ × ℝ) := Icc 0 1 ×ˢ (Icc (-(1 / 2)) (1 / 2) ∩ {h | η ≤ |h|})
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs))
  have hKne : K.Nonempty := ⟨(0, 1 / 2), ⟨by simp, ⟨by constructor <;> norm_num, by
    simp only [mem_setOf_eq]; rw [abs_of_pos (by norm_num)]; exact hη2⟩⟩⟩
  have hΦ : Continuous fun p : ℝ × ℝ => ‖γ (p.1 + p.2) - γ p.1‖ := by fun_prop
  obtain ⟨p₀, hp₀K, hp₀⟩ := hK.exists_isMinOn hKne hΦ.continuousOn
  refine ⟨‖γ (p₀.1 + p₀.2) - γ p₀.1‖, ?_, ?_⟩
  · rcases (norm_nonneg (γ (p₀.1 + p₀.2) - γ p₀.1)).lt_or_eq with h | h
    · exact h
    · exfalso
      have he : γ p₀.1 = γ (p₀.1 + p₀.2) := (sub_eq_zero.1 (norm_eq_zero.1 h.symm)).symm
      obtain ⟨n, hn⟩ := hinj _ _ he
      have h2 : p₀.2 = n := by linarith
      have hb : |(n : ℝ)| ≤ 1 / 2 := by rw [← h2, abs_le]; exact hp₀K.2.1
      have hn0 : n = 0 := by
        have : |(n : ℝ)| < 1 := by linarith
        rw [← Int.cast_abs] at this
        have : |n| < 1 := by exact_mod_cast this
        exact Int.abs_lt_one_iff.mp this
      have hl : η ≤ |p₀.2| := hp₀K.2.2
      rw [h2, hn0, Int.cast_zero, abs_zero] at hl
      linarith
  · intro t h hh1 hh2
    set t' := Int.fract t
    have ht : t = t' + (⌊t⌋ : ℤ) := (Int.fract_add_floor t).symm
    have e1 : γ (t + h) = γ (t' + h) := by
      rw [ht, show t' + (⌊t⌋ : ℤ) + h = t' + h + (⌊t⌋ : ℤ) by ring, tw_periodic_int hper]
    have e2 : γ t = γ t' := by rw [ht, tw_periodic_int hper]
    rw [e1, e2]
    have hmem : (t', h) ∈ K := ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩,
      ⟨abs_le.mp hh2, hh1⟩⟩
    exact hp₀ hmem

end HryniewiczCriterion

/-!
# The tube lemma for push-offs of a framed loop in `S³`

Let `γ` be a `C²` unit loop, injective modulo `1`, with a frame `e₁, e₂` such that
`det(γ, γ', e₁, e₂) > 0`. For small `ε > 0`, no push-off `γ(t) + ε ρ (cos φ e₁ + sin φ e₂)`,
`ρ ∈ [a, b]`, `a > 0`, vanishes or is a positive multiple of a point `γ(s)` of the loop.

Writing `s = t + h + n`, `|h| ≤ 1/2`: if `|h|` is not small, injectivity separates `γ(t + h)`
from `γ(t)`; if `|h|` is small, pairing with `γ'(t)` gives `|h| = O(ε)`, and the determinant
`det(γ, γ', ·, -sin φ e₁ + cos φ e₂)` gives `ε ρ det(γ, γ', e₁, e₂) = O(h²) = O(ε²)`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma tw_det_frame (g d e₁ e₂ : R4) (ρ c s ε : ℝ) :
    gl_det4 g d (ε • (ρ • (c • e₁ + s • e₂))) ((-s) • e₁ + c • e₂) =
      ε * ρ * (c ^ 2 + s ^ 2) * gl_det4 g d e₁ e₂ := by
  simp only [gl_det4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_det_decomp (g d T w : R4) (α β μ : ℝ) :
    gl_det4 g d (α • g + β • d + μ • T) w = μ * gl_det4 g d T w := by
  simp only [gl_det4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_dot_decomp (g d T : R4) (α β μ : ℝ) :
    dot4 (α • g + β • d + μ • T) d = α * dot4 g d + β * dot4 d d + μ * dot4 T d := by
  simp only [dot4, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_dot_expand (g v : R4) (ε : ℝ) :
    dot4 (g + ε • v) (g + ε • v) = dot4 g g + 2 * ε * dot4 g v + ε ^ 2 * dot4 v v := by
  simp only [dot4, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_norm_rot_le (e₁ e₂ : R4) (c s : ℝ) (hc : |c| ≤ 1) (hs : |s| ≤ 1) :
    ‖c • e₁ + s • e₂‖ ≤ ‖e₁‖ + ‖e₂‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hs

lemma tw_continuous_det4 {γ e₁ e₂ d : ℝ → R4} (h1 : Continuous γ) (h2 : Continuous d)
    (h3 : Continuous e₁) (h4 : Continuous e₂) :
    Continuous fun t => gl_det4 (γ t) (d t) (e₁ t) (e₂ t) := by
  have a := fun i => (continuous_apply i).comp h1
  have b := fun i => (continuous_apply i).comp h2
  have c := fun i => (continuous_apply i).comp h3
  have e := fun i => (continuous_apply i).comp h4
  simp only [Function.comp_def] at a b c e
  simp only [gl_det4]
  fun_prop

lemma tw_deriv_periodic {γ : ℝ → R4} (hper : ∀ s, γ (s + 1) = γ s) :
    Function.Periodic (deriv γ) 1 := by
  intro x
  have h := deriv_comp_add_const (f := γ) (a := (1 : ℝ)) (x := x)
  have e : (fun x => γ (x + 1)) = γ := funext hper
  rw [e] at h
  exact h.symm

lemma tw_lh {L M1 η m h : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M1) (hnear : |h| < η)
    (hη3 : 8 * (L + 1) * (M1 + 1) * η ≤ m) : 4 * (L * h ^ 2 * M1) ≤ m / 2 * |h| := by
  have h0 := abs_nonneg h
  have h1 : 4 * L * M1 * |h| ≤ m / 2 := by
    have hLM : L * M1 ≤ (L + 1) * (M1 + 1) := by nlinarith
    have : L * M1 * |h| ≤ (L + 1) * (M1 + 1) * η :=
      calc L * M1 * |h| ≤ (L + 1) * (M1 + 1) * |h| := mul_le_mul_of_nonneg_right hLM h0
        _ ≤ (L + 1) * (M1 + 1) * η := mul_le_mul_of_nonneg_left hnear.le (by positivity)
    linarith
  have e : 4 * (L * h ^ 2 * M1) = (4 * L * M1 * |h|) * |h| := by rw [← sq_abs h]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 h0

lemma tw_hbound {μ h q m ε V M1 X Y : ℝ} (hμ : 0 < μ) (hμlo : 1 / 2 ≤ μ) (hε : 0 < ε)
    (hm : 0 < m) (hqm : m ≤ q) (hq0 : 0 ≤ q) (e : μ * h * q = ε * X - μ * Y)
    (hX : |X| ≤ 4 * (V * M1)) (hY : |Y| ≤ m / 2 * |h|) : |h| ≤ 16 * V * M1 / m * ε := by
  have h0 := abs_nonneg h
  have hb1 : μ * |h| * q ≤ ε * (4 * (V * M1)) + μ * (m / 2 * |h|) := by
    have : |μ * h * q| = μ * |h| * q := by rw [abs_mul, abs_mul, abs_of_pos hμ, abs_of_nonneg hq0]
    rw [← this, e]
    calc |ε * X - μ * Y| ≤ |ε * X| + |μ * Y| := abs_sub _ _
      _ = ε * |X| + μ * |Y| := by rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_pos hμ]
      _ ≤ _ := by gcongr
  have hb2 : μ * |h| * m ≤ μ * |h| * q := mul_le_mul_of_nonneg_left hqm (by positivity)
  have hb3 : 1 / 2 * |h| * m ≤ μ * |h| * m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμlo h0) hm.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

lemma tw_final {ε a D0 μ Z M1 L E h H K0 : ℝ} (hε : 0 < ε) (hlhs : ε * a * D0 ≤ μ * Z)
    (hμ : 0 < μ) (hμhi : μ ≤ 3 / 2) (hZ : |Z| ≤ 24 * (M1 * (L * h ^ 2) * E)) (hM1 : 0 ≤ M1)
    (hL : 0 ≤ L) (hE : 0 ≤ E) (hhε : |h| ≤ H * ε) (hH : 0 ≤ H)
    (hK0 : K0 = 72 * (M1 + 1) * (L + 1) * (E + 1) * (H ^ 2 + 1)) (hε3 : ε * K0 < a * D0) :
    False := by
  have hh2 : h ^ 2 ≤ H ^ 2 * ε ^ 2 := by
    rw [← sq_abs h, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg h) hhε 2
  set P := M1 * L * E with hP
  have hP0 : 0 ≤ P := by positivity
  have hZ' : μ * Z ≤ 36 * P * h ^ 2 := by
    have h1 : μ * Z ≤ μ * |Z| := mul_le_mul_of_nonneg_left (le_abs_self Z) hμ.le
    have h2 : μ * |Z| ≤ 3 / 2 * (24 * (M1 * (L * h ^ 2) * E)) :=
      mul_le_mul hμhi hZ (abs_nonneg _) (by norm_num)
    have e : 3 / 2 * (24 * (M1 * (L * h ^ 2) * E)) = 36 * P * h ^ 2 := by rw [hP]; ring
    linarith
  have h3 : 36 * P * h ^ 2 ≤ 36 * P * (H ^ 2 * ε ^ 2) := mul_le_mul_of_nonneg_left hh2 (by positivity)
  have h4 : ε * (a * D0) ≤ ε * (36 * P * H ^ 2 * ε) := by
    have e : ε * (36 * P * H ^ 2 * ε) = 36 * P * (H ^ 2 * ε ^ 2) := by ring
    rw [e]; linarith
  have h5 : a * D0 ≤ 36 * P * H ^ 2 * ε := le_of_mul_le_mul_left h4 hε
  have h6 : 36 * P * H ^ 2 ≤ K0 := by
    rw [hK0, hP]
    have a1 : M1 * L * E ≤ (M1 + 1) * (L + 1) * (E + 1) := by
      exact mul_le_mul (mul_le_mul (by linarith) (by linarith) hL (by linarith)) (by linarith) hE
        (by positivity)
    have a2 : H ^ 2 ≤ H ^ 2 + 1 := by linarith
    have := mul_le_mul a1 a2 (sq_nonneg H) (by positivity)
    nlinarith
  have h7 : 36 * P * H ^ 2 * ε ≤ ε * K0 := by
    rw [mul_comm ε]; exact mul_le_mul_of_nonneg_right h6 hε.le
  linarith

set_option maxHeartbeats 1000000 in
theorem tw_tube (γ e₁ e₂ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (he₁ : Continuous e₁)
    (he₂ : Continuous e₂) (hγper : ∀ s, γ (s + 1) = γ s) (he₁per : ∀ s, e₁ (s + 1) = e₁ s)
    (he₂per : ∀ s, e₂ (s + 1) = e₂ s) (hγunit : ∀ s, euclidNorm (γ s) = 1)
    (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hdet : ∀ s, 0 < Matrix.det (Matrix.of ![γ s, deriv γ s, e₁ s, e₂ s]))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s t ρ φ : ℝ, a ≤ ρ → ρ ≤ b →
      γ t + ε • (ρ • (Real.cos φ • e₁ t + Real.sin φ • e₂ t)) ≠ 0 ∧
      ∀ μ : ℝ, 0 < μ → γ t + ε • (ρ • (Real.cos φ • e₁ t + Real.sin φ • e₂ t)) ≠ μ • γ s := by
  have hb : 0 < b := ha.trans_le hab
  have hd : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have cdγ : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have cddγ : Continuous (deriv (deriv γ)) := by
    have : ContDiff ℝ 1 (deriv γ) := hγ.iterate_deriv' 1 1
    exact this.continuous_deriv le_rfl
  have pdγ : Function.Periodic (deriv γ) 1 := tw_deriv_periodic hγper
  have pddγ : Function.Periodic (deriv (deriv γ)) 1 := tw_deriv_periodic pdγ
  have hdet' : ∀ t, 0 < gl_det4 (γ t) (deriv γ t) (e₁ t) (e₂ t) := fun t => by
    rw [← gl_det_eq_det4]; exact hdet t
  -- constants
  obtain ⟨M1, hM1⟩ := tw_periodic_bdd (f := fun t => ‖deriv γ t‖) (by fun_prop)
    (fun t => by simp only [pdγ t])
  obtain ⟨L, hL⟩ := tw_periodic_bdd (f := fun t => ‖deriv (deriv γ) t‖) (by fun_prop)
    (fun t => by simp only [pddγ t])
  obtain ⟨E, hE⟩ := tw_periodic_bdd (f := fun t => ‖e₁ t‖ + ‖e₂ t‖) (by fun_prop)
    (fun t => by simp only [he₁per, he₂per])
  obtain ⟨t₁, ht₁⟩ := tw_periodic_min (f := fun t => dot4 (deriv γ t) (deriv γ t))
    (gl_continuous_dot4 cdγ cdγ) (fun t => by simp only [pdγ t])
  obtain ⟨t₂, ht₂⟩ := tw_periodic_min (f := fun t => gl_det4 (γ t) (deriv γ t) (e₁ t) (e₂ t))
    (tw_continuous_det4 hγ.continuous cdγ he₁ he₂)
    (fun t => by simp only [hγper, pdγ t, he₁per, he₂per])
  set m := dot4 (deriv γ t₁) (deriv γ t₁) with hm_def
  set D0 := gl_det4 (γ t₂) (deriv γ t₂) (e₁ t₂) (e₂ t₂) with hD0_def
  have hD0 : 0 < D0 := hdet' t₂
  have hm : 0 < m := by
    have hne : deriv γ t₁ ≠ 0 := by
      intro h0
      have := hdet' t₁
      rw [h0] at this
      simp [gl_det4] at this
    exact gl_dot4_self_pos hne
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hLn : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hEn : 0 ≤ E := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hE 0)
  set V := b * E + 1 with hV_def
  have hV : 0 < V := by positivity
  set η := min (1 / 4) (m / (8 * (L + 1) * (M1 + 1))) with hη_def
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη2 : η ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hη3 : 8 * (L + 1) * (M1 + 1) * η ≤ m := by
    have h := min_le_right (1 / 4 : ℝ) (m / (8 * (L + 1) * (M1 + 1)))
    rw [← hη_def] at h
    rwa [le_div_iff₀ (by positivity), mul_comm] at h
  obtain ⟨c, hc, hfar⟩ := tw_far hγ.continuous hγper hinj hη hη2
  set H := 16 * V * M1 / m with hH_def
  have hHn : 0 ≤ H := by positivity
  set K0 := 72 * (M1 + 1) * (L + 1) * (E + 1) * (H ^ 2 + 1) with hK0_def
  have hK0 : 0 < K0 := by positivity
  refine ⟨min (1 / (24 * V)) (min (c / (26 * V)) (a * D0 / K0)), by positivity, ?_⟩
  intro ε hε hε0 s t ρ φ hρa hρb
  have hε1 : ε < 1 / (24 * V) := hε0.trans_le (min_le_left _ _)
  have hε2 : ε < c / (26 * V) := hε0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε < a * D0 / K0 := hε0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hεV : ε * V < 1 / 24 := by
    rw [lt_div_iff₀ (by positivity)] at hε1; nlinarith
  have hρ : 0 < ρ := ha.trans_le hρa
  -- the push-off vector
  set g := γ t with hg_def
  set d := deriv γ t with hd_def
  set u := Real.cos φ • e₁ t + Real.sin φ • e₂ t with hu_def
  set w := (-Real.sin φ) • e₁ t + Real.cos φ • e₂ t with hw_def
  set v := ρ • u with hv_def
  have hEt : ‖e₁ t‖ + ‖e₂ t‖ ≤ E := hE t
  have hu : ‖u‖ ≤ E :=
    (tw_norm_rot_le _ _ _ _ (Real.abs_cos_le_one φ) (Real.abs_sin_le_one φ)).trans hEt
  have hw : ‖w‖ ≤ E := (tw_norm_rot_le _ _ _ _ (by rw [abs_neg]; exact Real.abs_sin_le_one φ)
    (Real.abs_cos_le_one φ)).trans hEt
  have hv : ‖v‖ ≤ V := by
    rw [hv_def, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have : ρ * ‖u‖ ≤ b * E := mul_le_mul hρb hu (norm_nonneg _) hb.le
    linarith
  have hg1 : ‖g‖ ≤ 1 := tw_norm_le_one_of_unit (hγunit t)
  have hgg : dot4 g g = 1 := gl_dot4_self_of_unit (hγunit t)
  have hdM : ‖d‖ ≤ M1 := hM1 t
  -- the squared length of the push-off is close to `1`
  have hq : |dot4 (g + ε • v) (g + ε • v) - 1| ≤ 12 * (ε * V) := by
    rw [tw_dot_expand, hgg]
    have h1 : |dot4 g v| ≤ 4 * V := by
      have := tw_abs_dot4_le g v
      have : ‖g‖ * ‖v‖ ≤ 1 * V := mul_le_mul hg1 hv (norm_nonneg _) zero_le_one
      linarith
    have h2 : |dot4 v v| ≤ 4 * V ^ 2 := by
      have := tw_abs_dot4_le v v
      have : ‖v‖ * ‖v‖ ≤ V * V := mul_le_mul hv hv (norm_nonneg _) hV.le
      nlinarith
    have e : 1 + 2 * ε * dot4 g v + ε ^ 2 * dot4 v v - 1 =
        2 * ε * dot4 g v + ε ^ 2 * dot4 v v := by ring
    rw [e]
    calc |2 * ε * dot4 g v + ε ^ 2 * dot4 v v|
        ≤ |2 * ε * dot4 g v| + |ε ^ 2 * dot4 v v| := abs_add_le _ _
      _ = 2 * ε * |dot4 g v| + ε ^ 2 * |dot4 v v| := by
          rw [abs_mul (2 * ε) (dot4 g v), abs_mul (ε ^ 2) (dot4 v v),
            abs_of_pos (by positivity : (0 : ℝ) < 2 * ε),
            abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]
      _ ≤ 2 * ε * (4 * V) + ε ^ 2 * (4 * V ^ 2) := by gcongr
      _ ≤ 12 * (ε * V) := by
          have h0 : 0 < ε * V := by positivity
          have h1 : (ε * V) * (ε * V) ≤ (ε * V) * 1 := mul_le_mul_of_nonneg_left (by linarith) h0.le
          nlinarith
  refine ⟨fun h0 => ?_, fun μ hμ hx => ?_⟩
  · rw [h0] at hq
    simp only [gl_dot4_zero_right, zero_sub, abs_neg, abs_one] at hq
    linarith
  -- `μ` is close to `1`
  have hμ2 : dot4 (g + ε • v) (g + ε • v) = μ ^ 2 := by
    rw [hx, gl_dot4_smul_left, gl_dot4_smul_right, gl_dot4_self_of_unit (hγunit s)]; ring
  rw [hμ2] at hq
  have hμ1 : |μ - 1| ≤ 12 * (ε * V) := by
    have e : μ ^ 2 - 1 = (μ - 1) * (μ + 1) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < μ + 1)] at hq
    calc |μ - 1| = |μ - 1| * 1 := (mul_one _).symm
      _ ≤ |μ - 1| * (μ + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ _ := hq
  have hμlo : 1 / 2 ≤ μ := by
    have := (abs_le.mp hμ1).1; linarith
  have hμhi : μ ≤ 3 / 2 := by
    have := (abs_le.mp hμ1).2; linarith
  -- reduce `s` to `t + h` with `|h| ≤ 1/2`
  set h := s - t - round (s - t) with hh_def
  have hh : |h| ≤ 1 / 2 := abs_sub_round (s - t)
  have hs : γ s = γ (t + h) := by
    rw [show s = t + h + (round (s - t) : ℤ) by rw [hh_def]; ring, tw_periodic_int hγper]
  rw [hs] at hx
  rcases le_or_gt η |h| with hfar' | hnear
  · -- far case
    have hc' := hfar t h hfar' hh
    have e : γ (t + h) - γ t = (μ⁻¹ - 1) • g + (μ⁻¹ * ε) • v := by
      have hγh : γ (t + h) = μ⁻¹ • (g + ε • v) := by
        rw [hx, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
      rw [hγh, smul_add, smul_smul, ← hg_def]
      module
    rw [e] at hc'
    have hinv : μ⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hμ (by norm_num)]; linarith
    have hinv1 : |μ⁻¹ - 1| ≤ 2 * (12 * (ε * V)) := by
      have e2 : μ⁻¹ - 1 = (1 - μ) * μ⁻¹ := by field_simp
      rw [e2, abs_mul, abs_of_pos (inv_pos.2 hμ), abs_sub_comm]
      calc |μ - 1| * μ⁻¹ ≤ 12 * (ε * V) * 2 :=
            mul_le_mul hμ1 hinv (inv_pos.2 hμ).le (by positivity)
        _ = 2 * (12 * (ε * V)) := by ring
    have hn : ‖(μ⁻¹ - 1) • g + (μ⁻¹ * ε) • v‖ ≤ 26 * (ε * V) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < μ⁻¹ * ε)]
      have t1 : |μ⁻¹ - 1| * ‖g‖ ≤ 2 * (12 * (ε * V)) * 1 :=
        mul_le_mul hinv1 hg1 (norm_nonneg _) (by positivity)
      have t2 : μ⁻¹ * ε * ‖v‖ ≤ 2 * ε * V := by
        have := mul_le_mul (mul_le_mul_of_nonneg_right hinv hε.le) hv (norm_nonneg _)
          (by positivity)
        linarith
      linarith
    have : c ≤ 26 * (ε * V) := hc'.trans hn
    rw [lt_div_iff₀ (by positivity)] at hε2
    linarith
  · -- near case
    set T := γ (t + h) - γ t - h • deriv γ t with hT_def
    have hT : ‖T‖ ≤ L * h ^ 2 := tw_taylor hγ hL t h
    have eqv : ε • v = (μ - 1) • g + (μ * h) • d + μ • T := by
      have e1 : γ (t + h) = g + h • d + T := by rw [hT_def]; abel
      have e2 : ε • v = μ • γ (t + h) - g := by rw [← hx]; abel
      rw [e2, e1]
      module
    -- (i) pairing with `γ'` bounds `h`
    have hgd : dot4 g d = 0 := tw_dot_deriv_eq_zero hd hγunit t
    have hpair := congrArg (fun x => dot4 x d) eqv
    simp only [tw_dot_decomp, hgd, gl_dot4_smul_left] at hpair
    have hvd : |dot4 v d| ≤ 4 * (V * M1) := by
      have := tw_abs_dot4_le v d
      have : ‖v‖ * ‖d‖ ≤ V * M1 := mul_le_mul hv hdM (norm_nonneg _) hV.le
      linarith
    have hTd : |dot4 T d| ≤ 4 * (L * h ^ 2 * M1) := by
      have := tw_abs_dot4_le T d
      have : ‖T‖ * ‖d‖ ≤ L * h ^ 2 * M1 := mul_le_mul hT hdM (norm_nonneg _) (by positivity)
      linarith
    have hLh := tw_lh hLn hM1n hnear hη3
    have hhε : |h| ≤ H * ε := tw_hbound hμ hμlo hε hm (ht₁ t) (gl_dot4_self_nonneg d)
      (by linarith) hvd (hTd.trans hLh)
    -- (ii) the determinant against `w`
    have hdet1 := congrArg (fun x => gl_det4 g d x w) eqv
    simp only [tw_det_decomp] at hdet1
    rw [hv_def, hu_def, hw_def, tw_det_frame, Real.cos_sq_add_sin_sq, mul_one] at hdet1
    have hDt : D0 ≤ gl_det4 g d (e₁ t) (e₂ t) := ht₂ t
    have hTw : |gl_det4 g d T w| ≤ 24 * (M1 * (L * h ^ 2) * E) := by
      have := tw_abs_det4_le g d T w
      have : ‖g‖ * ‖d‖ * ‖T‖ * ‖w‖ ≤ 1 * M1 * (L * h ^ 2) * E := by
        gcongr
      linarith
    have lhs : ε * a * D0 ≤ μ * gl_det4 g d T w := by
      rw [← hdet1]
      have := mul_le_mul hρa hDt hD0.le hρ.le
      have := mul_le_mul_of_nonneg_left this hε.le
      linarith
    rw [lt_div_iff₀ hK0] at hε3
    exact tw_final hε lhs hμ hμhi hTw hM1n hLn hEn hhε hHn hK0_def hε3

end HryniewiczCriterion

/-!
# Meridian, part 1: algebra of stereographic projection

The differential `dσ` of stereographic projection from `N`, its orientation behaviour
`V(dσ x₁, dσ x₂, dσ x₃) = det(y, x₁, x₂, x₃) / (1 - ⟨y,N⟩)³` for `xᵢ ⊥ y`, and the rescaled
meridian `W(l)` with `σ(y) + l W(l) = σ((y + l v)/|y + l v|)` exactly, smooth through `l = 0`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The differential of `σ_N` at `y` applied to `x`. -/
def mer_dS (N y x : R4) : R4 :=
  (1 - dot4 y N)⁻¹ • (x - dot4 x N • N) + (dot4 x N / (1 - dot4 y N) ^ 2) • (y - dot4 y N • N)

lemma mer_hasDerivAt_stereo (N : R4) {y : ℝ → R4} {y' : R4} {s : ℝ} (hy : HasDerivAt y y' s)
    (hk : 1 - dot4 (y s) N ≠ 0) :
    HasDerivAt (fun s => stereographicFrom N (y s)) (mer_dS N (y s) y') s := by
  have hd : HasDerivAt (fun s => dot4 (y s) N) (dot4 y' N) s := by
    have := gl_hasDerivAt_dot4 hy (hasDerivAt_const s N)
    simpa [gl_dot4_zero_right] using this
  have h1 : HasDerivAt (fun s => 1 - dot4 (y s) N) (-dot4 y' N) s := by
    simpa using hd.const_sub 1
  have h2 := h1.inv hk
  have h3 : HasDerivAt (fun s => y s - dot4 (y s) N • N) (y' - dot4 y' N • N) s :=
    hy.sub (hd.smul_const N)
  have h4 := h2.smul h3
  refine h4.congr_deriv ?_
  ext i
  simp only [mer_dS, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.inv_apply]
  field_simp

lemma mer_det_expand (N x1 x2 x3 y : R4) (a1 a2 a3 b1 b2 b3 g1 g2 g3 : ℝ) :
    gl_det4 N (a1 • x1 + b1 • y + g1 • N) (a2 • x2 + b2 • y + g2 • N)
        (a3 • x3 + b3 • y + g3 • N) =
      a1 * a2 * a3 * gl_det4 N x1 x2 x3 + b1 * a2 * a3 * gl_det4 N y x2 x3 +
        a1 * b2 * a3 * gl_det4 N x1 y x3 + a1 * a2 * b3 * gl_det4 N x1 x2 y := by
  simp only [gl_det4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma mer_dS_eq (N y x : R4) :
    mer_dS N y x = (1 - dot4 y N)⁻¹ • x + (dot4 x N / (1 - dot4 y N) ^ 2) • y +
      (-((1 - dot4 y N)⁻¹ * dot4 x N) - dot4 x N / (1 - dot4 y N) ^ 2 * dot4 y N) • N := by
  ext i
  simp only [mer_dS, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Stereographic projection is orientation preserving. -/
lemma mer_orient {N y x1 x2 x3 : R4} (hN : dot4 N N = 1) (hy : dot4 y y = 1)
    (hk : dot4 y N ≠ 1) (h1 : dot4 x1 y = 0) (h2 : dot4 x2 y = 0) (h3 : dot4 x3 y = 0) :
    volumeIn N (mer_dS N y x1) (mer_dS N y x2) (mer_dS N y x3) =
      gl_det4 y x1 x2 x3 / (1 - dot4 y N) ^ 3 := by
  have I1 := gl_cramer4 y N x1 x2 x3
  have I2 := gl_cramer4 N y x1 x2 x3
  have s1 : gl_det4 y N x2 x3 = -gl_det4 N y x2 x3 := by simp only [gl_det4]; ring
  have s2 : gl_det4 y x1 N x3 = -gl_det4 N x1 y x3 := by simp only [gl_det4]; ring
  have s3 : gl_det4 y x1 x2 N = -gl_det4 N x1 x2 y := by simp only [gl_det4]; ring
  rw [h1, h2, h3, hy, gl_dot4_comm N y] at I1
  rw [hN, s1, s2, s3] at I2
  rw [gl_volumeIn_eq, mer_dS_eq, mer_dS_eq, mer_dS_eq, mer_det_expand]
  have hu : 1 - dot4 y N ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have key : -((1 - dot4 y N) * gl_det4 N x1 x2 x3) - (dot4 x1 N * gl_det4 N y x2 x3 +
      dot4 x2 N * gl_det4 N x1 y x3 + dot4 x3 N * gl_det4 N x1 x2 y) =
      (1 - dot4 y N) * gl_det4 y x1 x2 x3 := by linear_combination I1 + I2
  set c := (1 - dot4 y N)⁻¹ with hcdef
  have hc : c * (1 - dot4 y N) = 1 := inv_mul_cancel₀ hu
  have e1 : ∀ x : R4, dot4 x N / (1 - dot4 y N) ^ 2 = dot4 x N * c ^ 2 := fun x => by
    rw [hcdef, inv_pow, div_eq_mul_inv]
  have e2 : gl_det4 y x1 x2 x3 / (1 - dot4 y N) ^ 3 = gl_det4 y x1 x2 x3 * c ^ 3 := by
    rw [hcdef, inv_pow, div_eq_mul_inv]
  rw [e1, e1, e1, e2]
  linear_combination c ^ 4 * key + c ^ 3 * (gl_det4 N x1 x2 x3 + gl_det4 y x1 x2 x3) * hc

/-! ### The rescaled meridian -/

/-- `q = (|y + l v| - 1) / l`, written without division by `l`. -/
def mer_q (y v : R4) (l : ℝ) : ℝ :=
  (2 * dot4 v y + l * dot4 v v) / (euclidNorm (y + l • v) + 1)

/-- `D = |y + l v| - ⟨y + l v, N⟩`. -/
def mer_D (N y v : R4) (l : ℝ) : ℝ :=
  (1 - dot4 y N) + l * (mer_q y v l - dot4 v N)

/-- The rescaled meridian: `σ(y) + l W = σ((y + l v)/|y + l v|)`. -/
def mer_W (N y v : R4) (l : ℝ) : R4 :=
  (mer_D N y v l * (1 - dot4 y N))⁻¹ •
    ((1 - dot4 y N) • (v - dot4 v N • N) + (dot4 v N - mer_q y v l) • (y - dot4 y N • N))

/-- The linear part `W(0) = dσ(v - ⟨v,y⟩ y)`. -/
def mer_L (N y v : R4) : R4 :=
  ((1 - dot4 y N) * (1 - dot4 y N))⁻¹ •
    ((1 - dot4 y N) • (v - dot4 v N • N) + (dot4 v N - dot4 v y) • (y - dot4 y N • N))

lemma mer_euclidNorm_of_dot {y : R4} (hy : dot4 y y = 1) : euclidNorm y = 1 := by
  rw [euclidNorm, hy, Real.sqrt_one]

lemma mer_W_zero {N y : R4} (hy : dot4 y y = 1) (v : R4) : mer_W N y v 0 = mer_L N y v := by
  have hq : mer_q y v 0 = dot4 v y := by
    rw [mer_q, zero_smul, add_zero, mer_euclidNorm_of_dot hy]; ring
  simp only [mer_W, mer_L, mer_D, hq, zero_mul, add_zero]

lemma mer_L_eq_dS {N y : R4} (hy : dot4 y y = 1) (hk : dot4 y N ≠ 1) (v : R4) :
    mer_L N y v = mer_dS N y (v - dot4 v y • y) := by
  have hu : 1 - dot4 y N ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have e : dot4 (v - dot4 v y • y) N = dot4 v N - dot4 v y * dot4 y N := by
    rw [gl_dot4_sub_left, gl_dot4_smul_left]
  rw [mer_dS, e]
  ext i
  simp only [mer_L, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

lemma mer_L_add (N y : R4) (c s : ℝ) (f₁ f₂ : R4) :
    mer_L N y (c • f₁ + s • f₂) = c • mer_L N y f₁ + s • mer_L N y f₂ := by
  have e1 : dot4 (c • f₁ + s • f₂) N = c * dot4 f₁ N + s * dot4 f₂ N := by
    rw [gl_dot4_add_left, gl_dot4_smul_left, gl_dot4_smul_left]
  have e2 : dot4 (c • f₁ + s • f₂) y = c * dot4 f₁ y + s * dot4 f₂ y := by
    rw [gl_dot4_add_left, gl_dot4_smul_left, gl_dot4_smul_left]
  ext i
  simp only [mer_L, e1, e2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

lemma mer_sq_norm (y v : R4) (hy : dot4 y y = 1) (l : ℝ) :
    euclidNorm (y + l • v) ^ 2 = 1 + l * (2 * dot4 v y + l * dot4 v v) := by
  rw [gl_euclidNorm_sq]
  simp only [dot4, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy ⊢
  linear_combination hy

lemma mer_lq (y v : R4) (hy : dot4 y y = 1) (l : ℝ) :
    l * mer_q y v l = euclidNorm (y + l • v) - 1 := by
  have h := mer_sq_norm y v hy l
  have hp : 0 ≤ euclidNorm (y + l • v) := Real.sqrt_nonneg _
  have h1 : euclidNorm (y + l • v) + 1 ≠ 0 := by positivity
  rw [mer_q]
  field_simp
  linear_combination -h

/-- `σ(y) + l W(l) = σ(normalize (y + l v))` when `D ≠ 0`. -/
lemma mer_W_spec {N y : R4} (hy : dot4 y y = 1) (hk : dot4 y N ≠ 1) (v : R4) (l : ℝ)
    (hz : y + l • v ≠ 0) (hD : mer_D N y v l ≠ 0) :
    stereographicFrom N y + l • mer_W N y v l =
      stereographicFrom N (radialNormalize (y + l • v)) := by
  have hu : 1 - dot4 y N ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have hν : 0 < euclidNorm (y + l • v) := gl_euclidNorm_pos hz
  have hlq := mer_lq y v hy l
  set ν := euclidNorm (y + l • v)
  set q := mer_q y v l
  have hzN : dot4 (y + l • v) N = dot4 y N + l * dot4 v N := by
    rw [gl_dot4_add_left, gl_dot4_smul_left]
  have hDe : mer_D N y v l = ν - (dot4 y N + l * dot4 v N) := by
    rw [mer_D]; linear_combination hlq
  have hD' : ν - (dot4 y N + l * dot4 v N) ≠ 0 := hDe ▸ hD
  have hrn : dot4 (radialNormalize (y + l • v)) N = ν⁻¹ * (dot4 y N + l * dot4 v N) := by
    rw [radialNormalize, gl_dot4_smul_left, hzN]
  have hden : 1 - ν⁻¹ * (dot4 y N + l * dot4 v N) ≠ 0 := by
    rw [show 1 - ν⁻¹ * (dot4 y N + l * dot4 v N) = ν⁻¹ * (ν - (dot4 y N + l * dot4 v N)) by
      field_simp]
    exact mul_ne_zero (inv_ne_zero hν.ne') hD'
  have hν0 : ν ≠ 0 := hν.ne'
  have hW : l • mer_W N y v l = ((ν - (dot4 y N + l * dot4 v N)) * (1 - dot4 y N))⁻¹ •
      ((l * (1 - dot4 y N)) • (v - dot4 v N • N) +
        (l * dot4 v N - ν + 1) • (y - dot4 y N • N)) := by
    rw [mer_W, hDe]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (-(((ν - (dot4 y N + l * dot4 v N)) * (1 - dot4 y N))⁻¹ *
      (y i - dot4 y N * N i))) * hlq
  rw [stereographicFrom, stereographicFrom, hrn, hW]
  ext i
  simp only [radialNormalize, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    show euclidNorm (y + l • v) = ν from rfl]
  field_simp
  ring

end HryniewiczCriterion

/-!
# Meridian, part 2: transverse offsets miss the knot; homotopy wrappers

If `V(a, w, z) ≥ v₀ > 0` with `a = A'(0)` and `w, z` bounded, then `A(0) + r w` is not on the
loop `A` for all small `r > 0` (near `s = 0` the loop hugs the line `A(0) + s a`, far from
`s = 0` it stays a fixed distance from `A(0)`).
-/


noncomputable section

namespace HryniewiczCriterion

lemma mer_volumeIn_smul2 (N a w z : R4) (r : ℝ) :
    volumeIn N a (r • w) z = r * volumeIn N a w z := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]; ring

lemma mer_volumeIn_line (N a E z : R4) (s : ℝ) :
    volumeIn N a (s • a + E) z = volumeIn N a E z := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

lemma mer_abs_volumeIn_le (N a w z : R4) (hN : ‖N‖ ≤ 1) :
    |volumeIn N a w z| ≤ 24 * (‖a‖ * ‖w‖ * ‖z‖) := by
  rw [gl_volumeIn_eq, abs_neg]
  refine (tw_abs_det4_le N a w z).trans ?_
  have : ‖N‖ * ‖a‖ * ‖w‖ * ‖z‖ ≤ 1 * ‖a‖ * ‖w‖ * ‖z‖ := by gcongr
  linarith

/-- Second-derivative bound for a periodic `C²` loop. -/
lemma mer_second_bound {A : ℝ → R4} (hA : ContDiff ℝ 2 A) (hper : ∀ s, A (s + 1) = A s) :
    ∃ L, 0 ≤ L ∧ ∀ x, ‖deriv (deriv A) x‖ ≤ L := by
  have cddA : Continuous (deriv (deriv A)) := by
    have : ContDiff ℝ 1 (deriv A) := hA.iterate_deriv' 1 1
    exact this.continuous_deriv le_rfl
  have p2 : Function.Periodic (deriv (deriv A)) 1 := tw_deriv_periodic (tw_deriv_periodic hper)
  obtain ⟨L, hL⟩ := tw_periodic_bdd (f := fun x => ‖deriv (deriv A) x‖) cddA.norm
    (fun x => by simp only [p2 x])
  exact ⟨L, (norm_nonneg _).trans (hL 0), hL⟩

/-- Reduction of a real parameter to `[-1/2, 1/2]` for a `1`-periodic loop. -/
lemma mer_reduce {A : ℝ → R4} (hper : ∀ s, A (s + 1) = A s) (s : ℝ) :
    ∃ s' : ℝ, |s'| ≤ 1 / 2 ∧ A s = A s' := by
  refine ⟨s - round s, abs_sub_round s, ?_⟩
  have := tw_periodic_int hper (s - round s) (round s)
  rw [sub_add_cancel] at this
  exact this

theorem mer_cone (N : R4) (hN : ‖N‖ ≤ 1) (A : ℝ → R4) (hA : ContDiff ℝ 2 A)
    (hper : ∀ s, A (s + 1) = A s) (hinj : ∀ s t, A s = A t → ∃ n : ℤ, t = s + n)
    (ha : deriv A 0 ≠ 0) {M Z v₀ : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hv₀ : 0 < v₀) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ w z : R4, ‖w‖ ≤ M → ‖z‖ ≤ Z →
      v₀ ≤ volumeIn N (deriv A 0) w z → ∀ s, A s ≠ A 0 + r • w := by
  set a := deriv A 0
  have hα : 0 < dot4 a a := gl_dot4_self_pos ha
  set α := dot4 a a
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨L, hL0, hL⟩ := mer_second_bound hA hper
  set η := min (1 / 2) (α / (8 * ‖a‖ * (L + 1))) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hηa : 8 * ‖a‖ * (L + 1) * η ≤ α := by
    have := min_le_right (1 / 2 : ℝ) (α / (8 * ‖a‖ * (L + 1)))
    rw [← hηdef, le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨c, hc, hfar⟩ := tw_far hA.continuous hper hinj hη hη2
  set K := 1536 * ‖a‖ ^ 3 * Z * L * M ^ 2 / α ^ 2
  have hK : 0 ≤ K := by positivity
  refine ⟨min (c / (M + 1)) (v₀ / (K + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro r hr hr0 w z hw hz hv s hs
  have hr1 : r < c / (M + 1) := hr0.trans_le (min_le_left _ _)
  have hr2 : r < v₀ / (K + 1) := hr0.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hr1 hr2
  obtain ⟨s', hs'1, hs'⟩ := mer_reduce hper s
  rw [hs'] at hs
  have hrw : ‖r • w‖ ≤ r * M := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]; exact mul_le_mul_of_nonneg_left hw hr.le
  rcases le_or_gt η |s'| with hfa | hne
  · -- far
    have h1 := hfar 0 s' hfa hs'1
    rw [zero_add, hs, add_sub_cancel_left] at h1
    nlinarith
  · -- near
    set E := A s' - A 0 - s' • a
    have hE : ‖E‖ ≤ L * s' ^ 2 := by
      have := tw_taylor hA hL 0 s'
      rwa [zero_add] at this
    have hrwE : r • w = s' • a + E := by
      simp only [E]; rw [hs]; abel
    -- along `a`
    have hdot : s' * α = dot4 (r • w) a - dot4 E a := by
      rw [hrwE, gl_dot4_add_left, gl_dot4_smul_left]; ring
    have hd1 := tw_abs_dot4_le (r • w) a
    have hd2 := tw_abs_dot4_le E a
    have hs'α : |s'| * α ≤ 4 * ‖a‖ * (r * M + L * s' ^ 2) := by
      have : |s' * α| ≤ |dot4 (r • w) a| + |dot4 E a| := by rw [hdot]; exact abs_sub _ _
      rw [abs_mul, abs_of_pos hα] at this
      have h3 : 4 * (‖r • w‖ * ‖a‖) ≤ 4 * (r * M * ‖a‖) := by gcongr
      have h4 : 4 * (‖E‖ * ‖a‖) ≤ 4 * (L * s' ^ 2 * ‖a‖) := by gcongr
      nlinarith
    have hLs : 4 * ‖a‖ * (L * s' ^ 2) ≤ |s'| * α / 2 := by
      have hs2 : s' ^ 2 = |s'| * |s'| := by rw [← sq_abs]; ring
      rw [hs2]
      have : 8 * ‖a‖ * L * |s'| ≤ α := by
        have : 8 * ‖a‖ * L * |s'| ≤ 8 * ‖a‖ * (L + 1) * η := by
          have : 8 * ‖a‖ * L ≤ 8 * ‖a‖ * (L + 1) := by nlinarith
          exact mul_le_mul this hne.le (abs_nonneg _) (by positivity)
        linarith
      nlinarith [abs_nonneg s']
    have hsb : |s'| * α ≤ 8 * ‖a‖ * r * M := by nlinarith
    -- volume
    have hvol : r * v₀ ≤ 24 * (‖a‖ * (L * s' ^ 2) * Z) := by
      have e1 : volumeIn N a (r • w) z = r * volumeIn N a w z := mer_volumeIn_smul2 N a w z r
      have e2 : volumeIn N a (r • w) z = volumeIn N a E z := by
        rw [hrwE, mer_volumeIn_line]
      have h5 := mer_abs_volumeIn_le N a E z hN
      have h6 : r * v₀ ≤ volumeIn N a E z := by
        rw [← e2, e1]; exact mul_le_mul_of_nonneg_left hv hr.le
      have h7 : ‖a‖ * ‖E‖ * ‖z‖ ≤ ‖a‖ * (L * s' ^ 2) * Z := by gcongr
      linarith [le_abs_self (volumeIn N a E z)]
    have hs2b : s' ^ 2 * α ^ 2 ≤ (8 * ‖a‖ * r * M) ^ 2 := by
      have : (|s'| * α) ^ 2 ≤ (8 * ‖a‖ * r * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsb 2
      rwa [mul_pow, sq_abs] at this
    have hs2c : s' ^ 2 ≤ (8 * ‖a‖ * r * M) ^ 2 / α ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; exact hs2b
    have hfin : r * v₀ ≤ r * (r * K) := by
      have : 24 * (‖a‖ * (L * s' ^ 2) * Z) ≤
          24 * (‖a‖ * (L * ((8 * ‖a‖ * r * M) ^ 2 / α ^ 2)) * Z) := by gcongr
      have e : 24 * (‖a‖ * (L * ((8 * ‖a‖ * r * M) ^ 2 / α ^ 2)) * Z) = r * (r * K) := by
        simp only [K]; field_simp; ring
      linarith
    have : v₀ ≤ r * K := le_of_mul_le_mul_left hfin hr
    nlinarith

/-! ### Homotopy wrappers for `tw_G` -/

theorem mer_homotopy_B (N : R4) (A : ℝ → R4) (B : ℝ → ℝ → R4) (hA : ContDiff ℝ 2 A)
    (hB : ContDiff ℝ 2 (Function.uncurry B)) (hAper : ∀ s, A (s + 1) = A s)
    (hBper : ∀ τ t, B τ (t + 1) = B τ t) (hN : ∀ τ s t, dot4 (A s - B τ t) N = 0)
    (hne : ∀ τ s t, A s ≠ B τ t) :
    tw_G N A (B 0) = tw_G N A (B 1) :=
  gl_gauss_homotopy N (fun _ => A) B (hA.comp contDiff_snd) hB (fun _ s => hAper s) hBper hN hne

theorem mer_homotopy_A (N : R4) (A : ℝ → ℝ → R4) (B : ℝ → R4)
    (hA : ContDiff ℝ 2 (Function.uncurry A)) (hB : ContDiff ℝ 2 B)
    (hAper : ∀ τ s, A τ (s + 1) = A τ s) (hBper : ∀ t, B (t + 1) = B t)
    (hN : ∀ τ s t, dot4 (A τ s - B t) N = 0) (hne : ∀ τ s t, A τ s ≠ B t) :
    tw_G N (A 0) B = tw_G N (A 1) B :=
  gl_gauss_homotopy N A (fun _ => B) hA (hB.comp contDiff_snd) hAper (fun _ t => hBper t) hN hne

end HryniewiczCriterion

/-!
# Meridian, part 3: the exact near contribution

A straight piece `A₀ + ℓ(s) a`, `ℓ(s) = sin(2πs)/(2π)`, against the round circle
`A₀ + ρ (cos 2πt e₁ + sin 2πt e₂)` (`e₁, e₂` orthonormal, `⊥ a`): the Gauss integrand is
`ℓ'(s) 2πρ² V / (αℓ² + ρ²)^{3/2}` with `V = V(a, e₁, e₂)`, `α = |a|²`, and integrates to
`4π V ℓ(δ) / √(αℓ(δ)² + ρ²)` over `s ∈ [-δ, δ]`.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The round circle of radius `ρ` about `A₀` in the plane of `e₁, e₂`. -/
def mer_circ (A₀ e₁ e₂ : R4) (ρ t : ℝ) : R4 :=
  A₀ + ρ • (Real.cos (2 * Real.pi * t) • e₁ + Real.sin (2 * Real.pi * t) • e₂)

/-- The straightening profile `ℓ(s) = sin(2πs)/(2π)`. -/
def mer_ell (s : ℝ) : ℝ := Real.sin (2 * Real.pi * s) / (2 * Real.pi)

lemma mer_le_euclidNorm (u : R4) : ‖u‖ ≤ euclidNorm u := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  show |u i| ≤ Real.sqrt (dot4 u u)
  apply Real.abs_le_sqrt
  simp only [dot4, Fin.sum_univ_four]
  fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1),
    mul_self_nonneg (u 2), mul_self_nonneg (u 3)]

lemma mer_hasDerivAt_cos2pi (t : ℝ) :
    HasDerivAt (fun t => Real.cos (2 * Real.pi * t))
      (-Real.sin (2 * Real.pi * t) * (2 * Real.pi)) t := by
  have h0 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  exact h0.cos

lemma mer_hasDerivAt_sin2pi (t : ℝ) :
    HasDerivAt (fun t => Real.sin (2 * Real.pi * t))
      (Real.cos (2 * Real.pi * t) * (2 * Real.pi)) t := by
  have h0 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  exact h0.sin

lemma mer_hasDerivAt_ell (s : ℝ) : HasDerivAt mer_ell (Real.cos (2 * Real.pi * s)) s := by
  have h := (mer_hasDerivAt_sin2pi s).div_const (2 * Real.pi)
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  refine h.congr_deriv ?_
  field_simp

lemma mer_hasDerivAt_circ (A₀ e₁ e₂ : R4) (ρ t : ℝ) :
    HasDerivAt (mer_circ A₀ e₁ e₂ ρ)
      ((2 * Real.pi * ρ) • (-Real.sin (2 * Real.pi * t) • e₁ +
        Real.cos (2 * Real.pi * t) • e₂)) t := by
  have h := (((mer_hasDerivAt_cos2pi t).smul_const e₁).add
    ((mer_hasDerivAt_sin2pi t).smul_const e₂)).const_smul ρ |>.const_add A₀
  refine h.congr_deriv ?_
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma mer_circ_periodic (A₀ e₁ e₂ : R4) (ρ t : ℝ) :
    mer_circ A₀ e₁ e₂ ρ (t + 1) = mer_circ A₀ e₁ e₂ ρ t := by
  have h1 : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.cos_add_two_pi]
  have h2 : Real.sin (2 * Real.pi * (t + 1)) = Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.sin_add_two_pi]
  simp only [mer_circ, h1, h2]

lemma mer_contDiff_circ (A₀ e₁ e₂ : R4) (ρ : ℝ) : ContDiff ℝ 2 (mer_circ A₀ e₁ e₂ ρ) := by
  unfold mer_circ
  fun_prop

/-- The orthonormal-frame hypotheses. -/
structure MerFrame (a e₁ e₂ : R4) : Prop where
  h11 : dot4 e₁ e₁ = 1
  h22 : dot4 e₂ e₂ = 1
  h12 : dot4 e₁ e₂ = 0
  h1a : dot4 e₁ a = 0
  h2a : dot4 e₂ a = 0

lemma mer_near_integrand (N a e₁ e₂ : R4) (hF : MerFrame a e₁ e₂) (l c ρ C S : ℝ)
    (hCS : S ^ 2 + C ^ 2 = 1) (hρ : 0 < ρ) :
    gl_integrand N (c • a) ((2 * Real.pi * ρ) • (-S • e₁ + C • e₂))
        (l • a - ρ • (C • e₁ + S • e₂)) =
      c * (2 * Real.pi * ρ ^ 2 * volumeIn N a e₁ e₂) /
        Real.sqrt (dot4 a a * l ^ 2 + ρ ^ 2) ^ 3 := by
  have hv : volumeIn N (c • a) ((2 * Real.pi * ρ) • (-S • e₁ + C • e₂))
      (l • a - ρ • (C • e₁ + S • e₂)) =
      c * (2 * Real.pi * ρ ^ 2 * volumeIn N a e₁ e₂) * (S ^ 2 + C ^ 2) := by
    simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      smul_eq_mul]
    ring
  have hn : dot4 (l • a - ρ • (C • e₁ + S • e₂)) (l • a - ρ • (C • e₁ + S • e₂)) =
      dot4 a a * l ^ 2 + ρ ^ 2 := by
    have e1 := hF.h11; have e2 := hF.h22; have e3 := hF.h12; have e4 := hF.h1a
    have e5 := hF.h2a
    simp only [dot4, Fin.sum_univ_four, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      smul_eq_mul] at e1 e2 e3 e4 e5 ⊢
    linear_combination (ρ ^ 2 * C ^ 2) * e1 + (ρ ^ 2 * S ^ 2) * e2 + (2 * ρ ^ 2 * C * S) * e3 -
      (2 * l * ρ * C) * e4 - (2 * l * ρ * S) * e5 + ρ ^ 2 * hCS
  rw [gl_integrand, hv, hCS, mul_one, euclidNorm, hn]

/-- The antiderivative of the near integrand. -/
lemma mer_hasDerivAt_near (α ρ V : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (s : ℝ) :
    HasDerivAt (fun s => 2 * Real.pi * V * (mer_ell s / Real.sqrt (α * mer_ell s ^ 2 + ρ ^ 2)))
      (Real.cos (2 * Real.pi * s) * (2 * Real.pi * ρ ^ 2 * V) /
        Real.sqrt (α * mer_ell s ^ 2 + ρ ^ 2) ^ 3) s := by
  have hl := mer_hasDerivAt_ell s
  have hQpos : 0 < α * mer_ell s ^ 2 + ρ ^ 2 := by positivity
  have hQ : HasDerivAt (fun s => α * mer_ell s ^ 2 + ρ ^ 2)
      (α * (2 * mer_ell s * Real.cos (2 * Real.pi * s))) s := by
    have := ((hl.pow 2).const_mul α).add_const (ρ ^ 2)
    refine this.congr_deriv ?_
    simp
  have hsq := hQ.sqrt hQpos.ne'
  have hdiv := (hl.div hsq (Real.sqrt_pos.2 hQpos).ne').const_mul (2 * Real.pi * V)
  refine hdiv.congr_deriv ?_
  have hs := Real.sq_sqrt hQpos.le
  have hs0 : Real.sqrt (α * mer_ell s ^ 2 + ρ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hQpos).ne'
  set r := Real.sqrt (α * mer_ell s ^ 2 + ρ ^ 2)
  field_simp
  rw [hs]
  ring

end HryniewiczCriterion

/-!
# Meridian, part 6: frames, and the homotopy from an ellipse to a round circle

Gram–Schmidt turns `p, q` (with `V(a, p, q) > 0`) into an orthonormal frame `e₁, e₂ ⊥ a`;
then `V(a, e₁, e₂) = |a|`. The loops `A₀ + r (cos 2πt P + sin 2πt Q)` with
`P, Q` moving from `(p, q)` to `(e₁, e₂)` and `r` from `ε` to `ρ` stay in the transverse cone.
-/


noncomputable section

namespace HryniewiczCriterion

/-- The homotopy parameter `θ(τ) = sin²(πτ/2)`: smooth, `[0,1]`-valued, `θ 0 = 0`, `θ 1 = 1`. -/
def mer_theta (τ : ℝ) : ℝ := Real.sin (Real.pi * τ / 2) ^ 2

lemma mer_theta_zero : mer_theta 0 = 0 := by simp [mer_theta]

lemma mer_theta_one : mer_theta 1 = 1 := by simp [mer_theta, Real.sin_pi_div_two]

lemma mer_theta_mem (τ : ℝ) : 0 ≤ mer_theta τ ∧ mer_theta τ ≤ 1 :=
  ⟨sq_nonneg _, by have := Real.sin_sq_le_one (Real.pi * τ / 2); simpa [mer_theta] using this⟩

lemma mer_theta_contDiff : ContDiff ℝ 2 mer_theta := by unfold mer_theta; fun_prop

/-! ### `V(a, e₁, e₂)² = |a|²` for an orthonormal frame -/

lemma mer_vol_sq (N a e₁ e₂ : R4) (hN : dot4 N N = 1) (haN : dot4 a N = 0)
    (h1N : dot4 e₁ N = 0) (h2N : dot4 e₂ N = 0) (hF : MerFrame a e₁ e₂) :
    volumeIn N a e₁ e₂ ^ 2 = dot4 a a := by
  set M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of ![-N, a, e₁, e₂]
  have hMM : M * M.transpose = Matrix.diagonal ![1, dot4 a a, 1, 1] := by
    have e1 := hF.h11; have e2 := hF.h22; have e3 := hF.h12; have e4 := hF.h1a
    have e5 := hF.h2a
    simp only [dot4, Fin.sum_univ_four] at hN haN h1N h2N e1 e2 e3 e4 e5 ⊢
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> linarith
  have hdet : M.det * M.det = dot4 a a := by
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [this]
    simp [Fin.prod_univ_four]
  rw [sq]
  exact hdet

lemma mer_vol_eq_sqrt (N a e₁ e₂ : R4) (hN : dot4 N N = 1) (haN : dot4 a N = 0)
    (h1N : dot4 e₁ N = 0) (h2N : dot4 e₂ N = 0) (hF : MerFrame a e₁ e₂)
    (hpos : 0 < volumeIn N a e₁ e₂) : volumeIn N a e₁ e₂ = Real.sqrt (dot4 a a) := by
  rw [← mer_vol_sq N a e₁ e₂ hN haN h1N h2N hF, Real.sqrt_sq hpos.le]

/-! ### Gram–Schmidt -/

lemma mer_volumeIn_zero3 (N a b : R4) : volumeIn N a b 0 = 0 := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.zero_apply]; ring

lemma mer_gs (N a p q : R4) (hα : 0 < dot4 a a) (haN : dot4 a N = 0) (hpN : dot4 p N = 0)
    (hqN : dot4 q N = 0) (hv : 0 < volumeIn N a p q) :
    ∃ e₁ e₂ : R4, MerFrame a e₁ e₂ ∧ dot4 e₁ N = 0 ∧ dot4 e₂ N = 0 ∧
      0 < volumeIn N a p e₂ ∧ 0 < volumeIn N a e₁ q ∧ 0 < volumeIn N a e₁ e₂ := by
  set α := dot4 a a with hαdef
  set p₁ := p - (dot4 p a / α) • a with hp₁
  have vp₁ : ∀ z, volumeIn N a p₁ z = volumeIn N a p z := by
    intro z; rw [hp₁]
    simp only [gl_volumeIn_eq, gl_det4, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hp₁a : dot4 p₁ a = 0 := by
    rw [hp₁, gl_dot4_sub_left, gl_dot4_smul_left, ← hαdef]; field_simp; ring
  have hp₁N : dot4 p₁ N = 0 := by
    rw [hp₁, gl_dot4_sub_left, gl_dot4_smul_left, hpN, haN]; ring
  have hp₁0 : p₁ ≠ 0 := by
    intro h; have := vp₁ q; rw [h, gl_volumeIn_zero2] at this; linarith
  have hn₁ : 0 < dot4 p₁ p₁ := gl_dot4_self_pos hp₁0
  set s₁ := (Real.sqrt (dot4 p₁ p₁))⁻¹ with hs₁
  have hs₁sq : s₁ ^ 2 * dot4 p₁ p₁ = 1 := by
    rw [hs₁, inv_pow, Real.sq_sqrt hn₁.le, inv_mul_cancel₀ hn₁.ne']
  have hs₁pos : 0 < s₁ := inv_pos.2 (Real.sqrt_pos.2 hn₁)
  set e₁ := s₁ • p₁ with he₁
  have he₁₁ : dot4 e₁ e₁ = 1 := by
    rw [he₁, gl_dot4_smul_left, gl_dot4_smul_right]; linear_combination hs₁sq
  have he₁a : dot4 e₁ a = 0 := by rw [he₁, gl_dot4_smul_left, hp₁a, mul_zero]
  have he₁N : dot4 e₁ N = 0 := by rw [he₁, gl_dot4_smul_left, hp₁N, mul_zero]
  set q₁ := q - (dot4 q a / α) • a - dot4 q e₁ • e₁ with hq₁
  have hq₁a : dot4 q₁ a = 0 := by
    rw [hq₁, gl_dot4_sub_left, gl_dot4_sub_left, gl_dot4_smul_left, gl_dot4_smul_left, he₁a,
      ← hαdef]
    field_simp; ring
  have hq₁e₁ : dot4 q₁ e₁ = 0 := by
    rw [hq₁, gl_dot4_sub_left, gl_dot4_sub_left, gl_dot4_smul_left, gl_dot4_smul_left, he₁₁,
      gl_dot4_comm a e₁, he₁a]
    ring
  have hq₁N : dot4 q₁ N = 0 := by
    rw [hq₁, gl_dot4_sub_left, gl_dot4_sub_left, gl_dot4_smul_left, gl_dot4_smul_left, hqN, haN,
      he₁N]
    ring
  have ve₁q : volumeIn N a e₁ q = s₁ * volumeIn N a p q := by
    rw [← vp₁ q, he₁]
    simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]; ring
  have vq₁ : ∀ x, volumeIn N a x q₁ = volumeIn N a x q - dot4 q e₁ * volumeIn N a x e₁ := by
    intro x; rw [hq₁]
    simp only [gl_volumeIn_eq, gl_det4, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have ve₁e₁ : volumeIn N a e₁ e₁ = 0 := by
    simp only [gl_volumeIn_eq, gl_det4]; ring
  have vpe₁ : volumeIn N a p e₁ = 0 := by
    rw [← vp₁ e₁, he₁]
    simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]; ring
  have hq₁0 : q₁ ≠ 0 := by
    intro h
    have := vq₁ e₁
    rw [h, mer_volumeIn_zero3, ve₁e₁, mul_zero, sub_zero, ve₁q] at this
    have : 0 < s₁ * volumeIn N a p q := mul_pos hs₁pos hv
    linarith
  have hn₂ : 0 < dot4 q₁ q₁ := gl_dot4_self_pos hq₁0
  set s₂ := (Real.sqrt (dot4 q₁ q₁))⁻¹ with hs₂
  have hs₂sq : s₂ ^ 2 * dot4 q₁ q₁ = 1 := by
    rw [hs₂, inv_pow, Real.sq_sqrt hn₂.le, inv_mul_cancel₀ hn₂.ne']
  have hs₂pos : 0 < s₂ := inv_pos.2 (Real.sqrt_pos.2 hn₂)
  set e₂ := s₂ • q₁ with he₂
  have v₂ : ∀ x, volumeIn N a x e₂ = s₂ * volumeIn N a x q₁ := by
    intro x; rw [he₂]
    simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨e₁, e₂, ⟨he₁₁, ?_, ?_, he₁a, ?_⟩, he₁N, ?_, ?_, ?_, ?_⟩
  · rw [he₂, gl_dot4_smul_left, gl_dot4_smul_right]; linear_combination hs₂sq
  · rw [he₂, gl_dot4_smul_right, gl_dot4_comm, hq₁e₁, mul_zero]
  · rw [he₂, gl_dot4_smul_left, hq₁a, mul_zero]
  · rw [he₂, gl_dot4_smul_left, hq₁N, mul_zero]
  · rw [v₂, vq₁, vpe₁, mul_zero, sub_zero]; exact mul_pos hs₂pos hv
  · rw [ve₁q]; exact mul_pos hs₁pos hv
  · rw [v₂, vq₁, ve₁e₁, mul_zero, sub_zero, ve₁q]; exact mul_pos hs₂pos (mul_pos hs₁pos hv)

/-! ### Volumes along the frame homotopy -/

lemma mer_vol_rot (N a P Q : R4) (c s : ℝ) :
    volumeIn N a (c • P + s • Q) (-s • P + c • Q) = (c ^ 2 + s ^ 2) * volumeIn N a P Q := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

lemma mer_vol_convex (N a p q e₁ e₂ : R4) {θ m : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hm : 0 ≤ m)
    (hX : m ≤ volumeIn N a p q) (hY : m ≤ volumeIn N a p e₂ + volumeIn N a e₁ q)
    (hZ : m ≤ volumeIn N a e₁ e₂) :
    3 / 4 * m ≤ volumeIn N a ((1 - θ) • p + θ • e₁) ((1 - θ) • q + θ • e₂) := by
  have e : volumeIn N a ((1 - θ) • p + θ • e₁) ((1 - θ) • q + θ • e₂) =
      (1 - θ) ^ 2 * volumeIn N a p q +
        θ * (1 - θ) * (volumeIn N a p e₂ + volumeIn N a e₁ q) + θ ^ 2 * volumeIn N a e₁ e₂ := by
    simp only [gl_volumeIn_eq, gl_det4, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  rw [e]
  have h2 : 0 ≤ θ * (1 - θ) := mul_nonneg h0 (by linarith)
  have h3 : (1 - θ) ^ 2 * m ≤ (1 - θ) ^ 2 * volumeIn N a p q :=
    mul_le_mul_of_nonneg_left hX (sq_nonneg _)
  have h4 : θ * (1 - θ) * m ≤ θ * (1 - θ) * (volumeIn N a p e₂ + volumeIn N a e₁ q) :=
    mul_le_mul_of_nonneg_left hY h2
  have h5 : θ ^ 2 * m ≤ θ ^ 2 * volumeIn N a e₁ e₂ := mul_le_mul_of_nonneg_left hZ (sq_nonneg _)
  nlinarith [sq_nonneg (θ - 1 / 2)]

/-! ### Stage: ellipse to round circle -/

theorem mer_stage23 (N : R4) (A : ℝ → R4) (hA : ContDiff ℝ 2 A) (hper : ∀ s, A (s + 1) = A s)
    (hAN : ∀ s, dot4 (A s) N = 0) (p q e₁ e₂ : R4) (hpN : dot4 p N = 0) (hqN : dot4 q N = 0)
    (h1N : dot4 e₁ N = 0) (h2N : dot4 e₂ N = 0) (hF : MerFrame (deriv A 0) e₁ e₂)
    {r₀ M Z v₀ m : ℝ} (hm : 0 ≤ m)
    (hcone : ∀ r : ℝ, 0 < r → r < r₀ → ∀ w z : R4, ‖w‖ ≤ M → ‖z‖ ≤ Z →
      v₀ ≤ volumeIn N (deriv A 0) w z → ∀ s, A s ≠ A 0 + r • w)
    (hM : ‖p‖ + ‖q‖ + 2 ≤ M) (hZ : ‖p‖ + ‖q‖ + 2 ≤ Z) (hv₀ : v₀ ≤ 3 / 4 * m)
    (hX : m ≤ volumeIn N (deriv A 0) p q)
    (hY : m ≤ volumeIn N (deriv A 0) p e₂ + volumeIn N (deriv A 0) e₁ q)
    (hZm : m ≤ volumeIn N (deriv A 0) e₁ e₂)
    {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) (hε : ε < r₀) :
    tw_G N A (fun t => A 0 + ε • (Real.cos (2 * Real.pi * t) • p +
        Real.sin (2 * Real.pi * t) • q)) =
      tw_G N A (mer_circ (A 0) e₁ e₂ ρ) := by
  have he₁ : ‖e₁‖ ≤ 1 := tw_norm_le_one_of_unit (mer_euclidNorm_of_dot hF.h11)
  have he₂ : ‖e₂‖ ≤ 1 := tw_norm_le_one_of_unit (mer_euclidNorm_of_dot hF.h22)
  set P : ℝ → R4 := fun τ => (1 - mer_theta τ) • p + mer_theta τ • e₁
  set Q : ℝ → R4 := fun τ => (1 - mer_theta τ) • q + mer_theta τ • e₂
  set R : ℝ → ℝ := fun τ => (1 - mer_theta τ) * ε + mer_theta τ * ρ
  set B : ℝ → ℝ → R4 := fun τ t =>
    A 0 + R τ • (Real.cos (2 * Real.pi * t) • P τ + Real.sin (2 * Real.pi * t) • Q τ)
  have hB0 : B 0 = fun t => A 0 + ε • (Real.cos (2 * Real.pi * t) • p +
      Real.sin (2 * Real.pi * t) • q) := by
    funext t; simp only [B, R, P, Q, mer_theta_zero, sub_zero, one_mul, zero_mul, add_zero,
      one_smul, zero_smul]
  have hB1 : B 1 = mer_circ (A 0) e₁ e₂ ρ := by
    funext t; simp only [B, R, P, Q, mer_theta_one, sub_self, one_mul, zero_mul, zero_add,
      one_smul, zero_smul, mer_circ]
  rw [← hB0, ← hB1]
  have hθ := mer_theta_contDiff
  have hnP : ∀ τ, ‖P τ‖ ≤ ‖p‖ + 1 := by
    intro τ
    obtain ⟨h0, h1⟩ := mer_theta_mem τ
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    nlinarith [norm_nonneg p]
  have hnQ : ∀ τ, ‖Q τ‖ ≤ ‖q‖ + 1 := by
    intro τ
    obtain ⟨h0, h1⟩ := mer_theta_mem τ
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    nlinarith [norm_nonneg q]
  refine mer_homotopy_B N A B hA ?_ hper ?_ ?_ ?_
  · simp only [B, R, P, Q]
    have hc : ContDiff ℝ 2 fun p : ℝ × ℝ => Real.cos (2 * Real.pi * p.2) := by fun_prop
    have hs : ContDiff ℝ 2 fun p : ℝ × ℝ => Real.sin (2 * Real.pi * p.2) := by fun_prop
    have ht : ContDiff ℝ 2 fun p : ℝ × ℝ => mer_theta p.1 := hθ.comp contDiff_fst
    exact contDiff_const.add (((contDiff_const.sub ht).mul contDiff_const |>.add
      (ht.mul contDiff_const)).smul ((hc.smul ((contDiff_const.sub ht).smul contDiff_const |>.add
        (ht.smul contDiff_const))).add (hs.smul ((contDiff_const.sub ht).smul contDiff_const |>.add
        (ht.smul contDiff_const)))))
  · intro τ t
    have h1 : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.cos_add_two_pi]
    have h2 : Real.sin (2 * Real.pi * (t + 1)) = Real.sin (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.sin_add_two_pi]
    simp only [B, h1, h2]
  · intro τ s t
    simp only [B, P, Q, gl_dot4_sub_left, gl_dot4_add_left, gl_dot4_smul_left, hAN, hpN, hqN,
      h1N, h2N]
    ring
  · intro τ s t
    obtain ⟨h0, h1⟩ := mer_theta_mem τ
    have hR : 0 < R τ := by simp only [R]; nlinarith
    have hR' : R τ < r₀ := by simp only [R]; nlinarith
    have hw := (tw_norm_rot_le (P τ) (Q τ) _ _ (Real.abs_cos_le_one (2 * Real.pi * t))
      (Real.abs_sin_le_one (2 * Real.pi * t)))
    have hz := (tw_norm_rot_le (P τ) (Q τ) _ _
      (by rw [abs_neg]; exact Real.abs_sin_le_one (2 * Real.pi * t))
      (Real.abs_cos_le_one (2 * Real.pi * t)))
    refine hcone (R τ) hR hR' _ (-Real.sin (2 * Real.pi * t) • P τ +
      Real.cos (2 * Real.pi * t) • Q τ) (by linarith [hnP τ, hnQ τ])
      (by linarith [hnP τ, hnQ τ]) ?_ s
    rw [mer_vol_rot, Real.cos_sq_add_sin_sq, one_mul]
    exact hv₀.trans (mer_vol_convex N _ p q e₁ e₂ h0 h1 hm hX hY hZm)

end HryniewiczCriterion

/-!
# Meridian, part 7: from the meridian to its linearization

`σ(normalize(y + ε v(t))) = σ(y) + ε W(ε, t)` and `W(l, t)` is smooth through `l = 0`, where
`W(0, t) = cos 2πt p + sin 2πt q` (`p, q` the linearized frame). For `l` small, `W(l, ·)` is
uniformly close to `W(0, ·)` (compactness of the circle), so the homotopy `l : ε → 0` stays in
the transverse cone.
-/


noncomputable section

namespace HryniewiczCriterion

/-! ### Uniformity near `l = 0` -/

lemma mer_unif {g : ℝ → ℝ → ℝ} {c : ℝ} (hg : ∀ t, ContinuousAt (Function.uncurry g) (0, t))
    (hper : ∀ l t, g l (t + 1) = g l t) (h0 : ∀ t, g 0 t < c) :
    ∃ l₂ : ℝ, 0 < l₂ ∧ ∀ l, |l| < l₂ → ∀ t, g l t < c := by
  have hP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), t), g z.1 z.2 < c := fun t _ =>
    (hg t).eventually (Iio_mem_nhds (h0 t))
  have h := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun l t => g l t < c) hP
  obtain ⟨l₂, hl₂, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨l₂, hl₂, fun l hl t => ?_⟩
  have hmem : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hp : Function.Periodic (g l) 1 := hper l
  have e : g l t = g l (Int.fract t) := by
    have h := (hp.int_mul ⌊t⌋) (Int.fract t)
    rw [mul_one, Int.fract_add_floor] at h
    exact h
  rw [e]
  exact hball (by rw [Real.dist_eq, sub_zero]; exact hl) _ hmem

/-! ### Continuity and smoothness of `W` -/

section Reg

variable {X : Type*} [TopologicalSpace X]

lemma mer_continuous_q (y : R4) {vv : X → R4} {l : X → ℝ} (hv : Continuous vv)
    (hl : Continuous l) : Continuous fun x => mer_q y (vv x) (l x) := by
  unfold mer_q
  refine Continuous.div (by
      exact ((continuous_const.mul (gl_continuous_dot4 hv continuous_const)).add
        (hl.mul (gl_continuous_dot4 hv hv))))
    ((gl_continuous_euclidNorm (continuous_const.add (hl.smul hv))).add continuous_const)
    fun x => ?_
  have := Real.sqrt_nonneg (dot4 (y + l x • vv x) (y + l x • vv x))
  exact (by simp only [euclidNorm]; positivity)

lemma mer_continuous_D (N y : R4) {vv : X → R4} {l : X → ℝ} (hv : Continuous vv)
    (hl : Continuous l) : Continuous fun x => mer_D N y (vv x) (l x) := by
  unfold mer_D
  exact continuous_const.add (hl.mul ((mer_continuous_q y hv hl).sub
    (gl_continuous_dot4 hv continuous_const)))

lemma mer_continuousAt_W (N y : R4) {vv : X → R4} {l : X → ℝ} (hv : Continuous vv)
    (hl : Continuous l) {x₀ : X} (hD : mer_D N y (vv x₀) (l x₀) ≠ 0) (hk : 1 - dot4 y N ≠ 0) :
    ContinuousAt (fun x => mer_W N y (vv x) (l x)) x₀ := by
  unfold mer_W
  have h1 : Continuous fun x => dot4 (vv x) N • N :=
    (gl_continuous_dot4 hv continuous_const).smul continuous_const
  have h1' : Continuous fun x => vv x - dot4 (vv x) N • N := hv.sub h1
  have h2 : Continuous fun x => (1 - dot4 y N) • (vv x - dot4 (vv x) N • N) :=
    h1'.const_smul (1 - dot4 y N)
  have h3 : Continuous fun x => (dot4 (vv x) N - mer_q y (vv x) (l x)) • (y - dot4 y N • N) :=
    ((gl_continuous_dot4 hv continuous_const).sub (mer_continuous_q y hv hl)).smul
      continuous_const
  have h4 : ContinuousAt (fun x => (mer_D N y (vv x) (l x) * (1 - dot4 y N))⁻¹) x₀ :=
    ((mer_continuous_D N y hv hl).mul continuous_const).continuousAt.inv₀ (mul_ne_zero hD hk)
  exact h4.smul (h2.add h3).continuousAt

lemma mer_continuous_L (N y : R4) {vv : X → R4} (hv : Continuous vv) :
    Continuous fun x => mer_L N y (vv x) := by
  unfold mer_L
  have h1 : Continuous fun x => dot4 (vv x) N • N :=
    (gl_continuous_dot4 hv continuous_const).smul continuous_const
  have h1' : Continuous fun x => vv x - dot4 (vv x) N • N := hv.sub h1
  have h2 : Continuous fun x => (1 - dot4 y N) • (vv x - dot4 (vv x) N • N) :=
    h1'.const_smul (1 - dot4 y N)
  have h3 : Continuous fun x => (dot4 (vv x) N - dot4 (vv x) y) • (y - dot4 y N • N) :=
    ((gl_continuous_dot4 hv continuous_const).sub (gl_continuous_dot4 hv continuous_const)).smul
      continuous_const
  exact (h2.add h3).const_smul ((1 - dot4 y N) * (1 - dot4 y N))⁻¹

end Reg

lemma mer_contDiff_W (N y : R4) {vv : ℝ × ℝ → R4} {l : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 vv)
    (hl : ContDiff ℝ 2 l) (hz : ∀ p, y + l p • vv p ≠ 0)
    (hD : ∀ p, mer_D N y (vv p) (l p) ≠ 0) (hk : 1 - dot4 y N ≠ 0) :
    ContDiff ℝ 2 fun p => mer_W N y (vv p) (l p) := by
  have hz' : ContDiff ℝ 2 fun p => y + l p • vv p := contDiff_const.add (hl.smul hv)
  have hn : ContDiff ℝ 2 fun p => euclidNorm (y + l p • vv p) := by
    simp only [euclidNorm]
    exact (gl_contDiff_dot4 hz' hz').sqrt fun p => (gl_dot4_self_pos (hz p)).ne'
  have hq : ContDiff ℝ 2 fun p => mer_q y (vv p) (l p) := by
    unfold mer_q
    refine ContDiff.div ((contDiff_const.mul (gl_contDiff_dot4 hv contDiff_const)).add
      (hl.mul (gl_contDiff_dot4 hv hv))) (hn.add contDiff_const) fun p => ?_
    have := Real.sqrt_nonneg (dot4 (y + l p • vv p) (y + l p • vv p))
    exact (by simp only [euclidNorm]; positivity)
  have hDc : ContDiff ℝ 2 fun p => mer_D N y (vv p) (l p) := by
    unfold mer_D
    exact contDiff_const.add (hl.mul (hq.sub (gl_contDiff_dot4 hv contDiff_const)))
  unfold mer_W
  have h1 : ContDiff ℝ 2 fun p => dot4 (vv p) N • N :=
    (gl_contDiff_dot4 hv contDiff_const).smul_const N
  have h1' : ContDiff ℝ 2 fun p => vv p - dot4 (vv p) N • N := hv.sub h1
  have h2 : ContDiff ℝ 2 fun p => (1 - dot4 y N) • (vv p - dot4 (vv p) N • N) :=
    h1'.const_smul (1 - dot4 y N)
  have h3 : ContDiff ℝ 2 fun p => (dot4 (vv p) N - mer_q y (vv p) (l p)) • (y - dot4 y N • N) :=
    ((gl_contDiff_dot4 hv contDiff_const).sub hq).smul_const _
  have h4 : ContDiff ℝ 2 fun p => (mer_D N y (vv p) (l p) * (1 - dot4 y N))⁻¹ :=
    (hDc.mul contDiff_const).inv fun p => mul_ne_zero (hD p) hk
  exact h4.smul (h2.add h3)

lemma mer_W_perp {N y : R4} (hN : dot4 N N = 1) (v : R4) (l : ℝ) :
    dot4 (mer_W N y v l) N = 0 := by
  simp only [mer_W, gl_dot4_smul_left, gl_dot4_add_left, gl_dot4_sub_left, hN]; ring

lemma mer_L_perp {N y : R4} (hN : dot4 N N = 1) (v : R4) : dot4 (mer_L N y v) N = 0 := by
  simp only [mer_L, gl_dot4_smul_left, gl_dot4_add_left, gl_dot4_sub_left, hN]; ring

/-! ### Stage 1 -/

/-- The meridian direction `v(t) = cos 2πt f₁ + sin 2πt f₂`. -/
def mer_v (f₁ f₂ : R4) (t : ℝ) : R4 :=
  Real.cos (2 * Real.pi * t) • f₁ + Real.sin (2 * Real.pi * t) • f₂

lemma mer_v_periodic (f₁ f₂ : R4) (t : ℝ) : mer_v f₁ f₂ (t + 1) = mer_v f₁ f₂ t := by
  have h1 : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.cos_add_two_pi]
  have h2 : Real.sin (2 * Real.pi * (t + 1)) = Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.sin_add_two_pi]
  simp only [mer_v, h1, h2]

lemma mer_contDiff_v (f₁ f₂ : R4) : ContDiff ℝ 2 (mer_v f₁ f₂) := by unfold mer_v; fun_prop

lemma mer_vol_sub3 (N a w w' z : R4) :
    volumeIn N a w z = volumeIn N a w' z + volumeIn N a (w - w') z := by
  simp only [gl_volumeIn_eq, gl_det4, Pi.sub_apply]; ring

theorem mer_stage1 (N y f₁ f₂ : R4) (hN : dot4 N N = 1) (hk : 1 - dot4 y N ≠ 0)
    (hy : dot4 y y = 1) (A : ℝ → R4) (hA : ContDiff ℝ 2 A) (hper : ∀ s, A (s + 1) = A s)
    (hAN : ∀ s, dot4 (A s) N = 0) (hA0 : A 0 = stereographicFrom N y)
    {r₀ M Z v₀ η l₂ : ℝ} (hη : 0 ≤ η)
    (hcone : ∀ r : ℝ, 0 < r → r < r₀ → ∀ w z : R4, ‖w‖ ≤ M → ‖z‖ ≤ Z →
      v₀ ≤ volumeIn N (deriv A 0) w z → ∀ s, A s ≠ A 0 + r • w)
    (hM : ‖mer_L N y f₁‖ + ‖mer_L N y f₂‖ + η ≤ M) (hZ : ‖mer_L N y f₁‖ + ‖mer_L N y f₂‖ ≤ Z)
    (hv₀ : v₀ ≤ volumeIn N (deriv A 0) (mer_L N y f₁) (mer_L N y f₂) -
      24 * (‖deriv A 0‖ * η * (‖mer_L N y f₁‖ + ‖mer_L N y f₂‖)))
    (hu1 : ∀ l, |l| < l₂ → ∀ t, y + l • mer_v f₁ f₂ t ≠ 0)
    (hu2 : ∀ l, |l| < l₂ → ∀ t, mer_D N y (mer_v f₁ f₂ t) l ≠ 0)
    (hu3 : ∀ l, |l| < l₂ → ∀ t,
      ‖mer_W N y (mer_v f₁ f₂ t) l - mer_L N y (mer_v f₁ f₂ t)‖ ≤ η)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε < r₀) (hεl : ε < l₂) :
    tw_G N A (fun t => stereographicFrom N (radialNormalize (y + ε • mer_v f₁ f₂ t))) =
      tw_G N A (fun t => A 0 + ε • (Real.cos (2 * Real.pi * t) • mer_L N y f₁ +
        Real.sin (2 * Real.pi * t) • mer_L N y f₂)) := by
  set p := mer_L N y f₁
  set q := mer_L N y f₂
  set lam : ℝ → ℝ := fun τ => ε * (1 - mer_theta τ)
  have hlam : ∀ τ, |lam τ| < l₂ := by
    intro τ
    obtain ⟨h0, h1⟩ := mer_theta_mem τ
    rw [abs_of_nonneg (by simp only [lam]; nlinarith)]
    simp only [lam]; nlinarith
  set B : ℝ → ℝ → R4 := fun τ t => A 0 + ε • mer_W N y (mer_v f₁ f₂ t) (lam τ)
  have hB0 : B 0 = fun t => stereographicFrom N (radialNormalize (y + ε • mer_v f₁ f₂ t)) := by
    funext t
    have hl0 : lam 0 = ε := by simp [lam, mer_theta_zero]
    have hε' : |ε| < l₂ := by rw [abs_of_pos hε]; exact hεl
    simp only [B, hl0, hA0]
    exact mer_W_spec hy (fun h => hk (by rw [h]; ring)) _ ε (hu1 ε hε' t) (hu2 ε hε' t)
  have hB1 : B 1 = fun t => A 0 + ε • (Real.cos (2 * Real.pi * t) • p +
      Real.sin (2 * Real.pi * t) • q) := by
    funext t
    have hl1 : lam 1 = 0 := by simp [lam, mer_theta_one]
    simp only [B, hl1, mer_W_zero hy, mer_v, mer_L_add, p, q]
  rw [← hB0, ← hB1]
  refine mer_homotopy_B N A B hA ?_ hper ?_ ?_ ?_
  · have hl : ContDiff ℝ 2 fun p : ℝ × ℝ => lam p.1 := by
      simp only [lam]; exact contDiff_const.mul (contDiff_const.sub
        (mer_theta_contDiff.comp contDiff_fst))
    have hW : ContDiff ℝ 2 fun p : ℝ × ℝ => mer_W N y (mer_v f₁ f₂ p.2) (lam p.1) :=
      mer_contDiff_W N y ((mer_contDiff_v f₁ f₂).comp contDiff_snd) hl
        (fun p => hu1 _ (hlam p.1) _) (fun p => hu2 _ (hlam p.1) _) hk
    exact contDiff_const.add (hW.const_smul ε)
  · intro τ t; simp only [B, mer_v_periodic]
  · intro τ s t
    simp only [B, gl_dot4_sub_left, gl_dot4_add_left, gl_dot4_smul_left, hAN, mer_W_perp hN]
    ring
  · intro τ s t
    set w := mer_W N y (mer_v f₁ f₂ t) (lam τ)
    set c := Real.cos (2 * Real.pi * t)
    set sn := Real.sin (2 * Real.pi * t)
    have hLv : mer_L N y (mer_v f₁ f₂ t) = c • p + sn • q := by
      simp only [mer_v, mer_L_add, p, q, c, sn]
    have hdw := hu3 _ (hlam τ) t
    rw [hLv] at hdw
    have hw0 := tw_norm_rot_le p q c sn (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
    have hz := tw_norm_rot_le p q (-sn) c (by rw [abs_neg]; exact Real.abs_sin_le_one _)
      (Real.abs_cos_le_one _)
    have hwM : ‖w‖ ≤ M := by
      have : w = (c • p + sn • q) + (w - (c • p + sn • q)) := by abel
      rw [this]
      exact (norm_add_le _ _).trans (by linarith)
    refine hcone ε hε hεr w (-sn • p + c • q) hwM (by linarith) ?_ s
    rw [mer_vol_sub3 N _ w (c • p + sn • q), mer_vol_rot, Real.cos_sq_add_sin_sq, one_mul]
    have hb := mer_abs_volumeIn_le N (deriv A 0) (w - (c • p + sn • q)) (-sn • p + c • q)
      (tw_norm_le_one_of_unit (mer_euclidNorm_of_dot hN))
    have h1 : ‖deriv A 0‖ * ‖w - (c • p + sn • q)‖ * ‖-sn • p + c • q‖ ≤
        ‖deriv A 0‖ * η * (‖p‖ + ‖q‖) := by gcongr
    linarith [neg_abs_le (volumeIn N (deriv A 0) (w - (c • p + sn • q)) (-sn • p + c • q))]

end HryniewiczCriterion

/-!
# Gauss integral: symmetry, shift of the second loop, reversal of the first loop
-/


noncomputable section

namespace HryniewiczCriterion

lemma td_integrand_swap (N a b u : R4) :
    gl_integrand N b a (-u) = gl_integrand N a b u := by
  have hn : euclidNorm (-u) = euclidNorm u := by
    simp only [euclidNorm, dot4, Pi.neg_apply, neg_mul_neg]
  rw [gl_integrand, gl_integrand, hn, gl_volumeIn_swap12, gl_volumeIn_neg3, neg_neg]

lemma td_integrand_neg_first (N a b u : R4) :
    gl_integrand N (-a) b u = -gl_integrand N a b u := by
  simp only [gl_integrand, gl_volumeIn_eq, gl_det4, Pi.neg_apply]; ring

/-- The chart Gauss double integral is symmetric in the two loops. -/
theorem td_tw_G_symm (N : R4) (A B : ℝ → R4) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hne : ∀ s t, A s ≠ B t) : tw_G N A B = tw_G N B A := by
  have hcont : Continuous (Function.uncurry fun s t =>
      gl_integrand N (deriv A s) (deriv B t) (A s - B t)) :=
    gl_continuous_integrand N ((hA.continuous_deriv le_rfl).comp continuous_fst)
      ((hB.continuous_deriv le_rfl).comp continuous_snd)
      ((hA.continuous.comp continuous_fst).sub (hB.continuous.comp continuous_snd))
      fun p => sub_ne_zero.2 (hne p.1 p.2)
  unfold tw_G
  rw [gl_integral_integral_swap_unit hcont]
  congr 1; funext t; congr 1; funext s
  rw [show B t - A s = -(A s - B t) by abel, td_integrand_swap]

/-- Shifting the parameter of a periodic second loop does not change the Gauss integral. -/
theorem td_tw_G_shift (N : R4) (A B : ℝ → R4) (hBper : ∀ t, B (t + 1) = B t) (c : ℝ) :
    tw_G N A (fun t => B (t + c)) = tw_G N A B := by
  have hB'per : ∀ t, deriv B (t + 1) = deriv B t := fun t => by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f t) (funext hBper)
  unfold tw_G
  congr 1; funext s
  have hd : ∀ t, deriv (fun t => B (t + c)) t = deriv B (t + c) := fun t => deriv_comp_add_const B c t
  simp_rw [hd]
  set g : ℝ → ℝ := fun t => gl_integrand N (deriv A s) (deriv B t) (A s - B t)
  have hg : Function.Periodic g 1 := fun t => by simp only [g, hBper t, hB'per t]
  have h := intervalIntegral.integral_comp_add_right (a := 0) (b := 1) g c
  simp only [g] at h
  rw [h, zero_add, add_comm 1 c, hg.intervalIntegral_add_eq c 0, zero_add]

/-- Reversing a periodic first loop changes the sign of the Gauss integral. -/
theorem td_tw_G_reverse (N : R4) (A B : ℝ → R4) (hAper : ∀ s, A (s + 1) = A s) (c : ℝ) :
    tw_G N (fun s => A (c - s)) B = -tw_G N A B := by
  have hA'per : ∀ s, deriv A (s + 1) = deriv A s := fun s => by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f s) (funext hAper)
  unfold tw_G
  set I : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..1,
    gl_integrand N (deriv A s) (deriv B t) (A s - B t)
  have hI : Function.Periodic I 1 := fun s => by simp only [I, hAper s, hA'per s]
  have hd : ∀ s, deriv (fun s => A (c - s)) s = -deriv A (c - s) := fun s => deriv_comp_const_sub A c s
  have hpt : ∀ s, (∫ t in (0 : ℝ)..1, gl_integrand N (deriv (fun s => A (c - s)) s)
      (deriv B t) (A (c - s) - B t)) = -I (c - s) := by
    intro s
    simp only [hd, td_integrand_neg_first, intervalIntegral.integral_neg, I]
  simp_rw [hpt]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left, sub_zero]
  have h := hI.intervalIntegral_add_eq (c - 1) 0
  rw [sub_add_cancel, zero_add] at h
  rw [h]

end HryniewiczCriterion

/-!
# Small transverse loop, stage: chart loop `A₀ + ρ V` to the round chart circle

If `V` stays within `η` of `cos 2πt p + sin 2πt q` (`p, q` transverse to `A'(0)`), the straight
homotopy to the round circle stays in the transverse cone, which misses the knot `A`.
-/


noncomputable section

namespace HryniewiczCriterion

theorem td_stage (N : R4) (hN : dot4 N N = 1) (A : ℝ → R4) (hA : ContDiff ℝ 2 A)
    (hper : ∀ s, A (s + 1) = A s) (hAN : ∀ s, dot4 (A s) N = 0) (p q : R4)
    (hpN : dot4 p N = 0) (hqN : dot4 q N = 0)
    {r₀ M Z v₀ η : ℝ} (hη : 0 ≤ η)
    (hcone : ∀ r : ℝ, 0 < r → r < r₀ → ∀ w z : R4, ‖w‖ ≤ M → ‖z‖ ≤ Z →
      v₀ ≤ volumeIn N (deriv A 0) w z → ∀ s, A s ≠ A 0 + r • w)
    (hM : ‖p‖ + ‖q‖ + η ≤ M) (hZ : ‖p‖ + ‖q‖ ≤ Z)
    (hv₀ : v₀ ≤ volumeIn N (deriv A 0) p q - 24 * (‖deriv A 0‖ * η * (‖p‖ + ‖q‖)))
    (V : ℝ → R4) (hV : ContDiff ℝ 2 V) (hVper : ∀ t, V (t + 1) = V t)
    (hVN : ∀ t, dot4 (V t) N = 0) (hVη : ∀ t, ‖V t - mer_v p q t‖ ≤ η)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r₀) :
    tw_G N A (fun t => A 0 + ρ • V t) = tw_G N A (fun t => A 0 + ρ • mer_v p q t) := by
  set B : ℝ → ℝ → R4 := fun τ t =>
    A 0 + ρ • ((1 - mer_theta τ) • V t + mer_theta τ • mer_v p q t)
  have hB0 : B 0 = fun t => A 0 + ρ • V t := by
    funext t; simp [B, mer_theta_zero]
  have hB1 : B 1 = fun t => A 0 + ρ • mer_v p q t := by
    funext t; simp [B, mer_theta_one]
  rw [← hB0, ← hB1]
  refine mer_homotopy_B N A B hA ?_ hper ?_ ?_ ?_
  · have hθ : ContDiff ℝ 2 fun x : ℝ × ℝ => mer_theta x.1 :=
      mer_theta_contDiff.comp contDiff_fst
    have hw : ContDiff ℝ 2 fun x : ℝ × ℝ =>
        (1 - mer_theta x.1) • V x.2 + mer_theta x.1 • mer_v p q x.2 :=
      ((contDiff_const.sub hθ).smul (hV.comp contDiff_snd)).add
        (hθ.smul ((mer_contDiff_v p q).comp contDiff_snd))
    exact contDiff_const.add (hw.const_smul ρ)
  · intro τ t; simp only [B, hVper, mer_v_periodic]
  · intro τ s t
    have hvN : dot4 (mer_v p q t) N = 0 := by
      simp only [mer_v, gl_dot4_add_left, gl_dot4_smul_left, hpN, hqN]; ring
    simp only [B, gl_dot4_sub_left, gl_dot4_add_left, gl_dot4_smul_left, hAN, hVN, hvN]
    ring
  · intro τ s t
    obtain ⟨h0, h1⟩ := mer_theta_mem τ
    set θ := mer_theta τ
    set w := (1 - θ) • V t + θ • mer_v p q t
    set c := Real.cos (2 * Real.pi * t)
    set sn := Real.sin (2 * Real.pi * t)
    have hR : mer_v p q t = c • p + sn • q := rfl
    have hdw : ‖w - (c • p + sn • q)‖ ≤ η := by
      have e : w - (c • p + sn • q) = (1 - θ) • (V t - mer_v p q t) := by
        simp only [w, hR, smul_sub, sub_smul, one_smul]; abel
      rw [e, norm_smul, Real.norm_of_nonneg (by linarith)]
      calc (1 - θ) * ‖V t - mer_v p q t‖ ≤ 1 * η :=
            mul_le_mul (by linarith) (hVη t) (norm_nonneg _) zero_le_one
        _ = η := one_mul η
    have hw0 := tw_norm_rot_le p q c sn (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
    have hz := tw_norm_rot_le p q (-sn) c (by rw [abs_neg]; exact Real.abs_sin_le_one _)
      (Real.abs_cos_le_one _)
    have hwM : ‖w‖ ≤ M := by
      have : w = (c • p + sn • q) + (w - (c • p + sn • q)) := by abel
      rw [this]
      exact (norm_add_le _ _).trans (by linarith)
    refine hcone ρ hρ hρr w (-sn • p + c • q) hwM (by linarith) ?_ s
    rw [mer_vol_sub3 N _ w (c • p + sn • q), mer_vol_rot, Real.cos_sq_add_sin_sq, one_mul]
    have hb := mer_abs_volumeIn_le N (deriv A 0) (w - (c • p + sn • q)) (-sn • p + c • q)
      (tw_norm_le_one_of_unit (mer_euclidNorm_of_dot hN))
    have h1' : ‖deriv A 0‖ * ‖w - (c • p + sn • q)‖ * ‖-sn • p + c • q‖ ≤
        ‖deriv A 0‖ * η * (‖p‖ + ‖q‖) := by gcongr
    linarith [neg_abs_le (volumeIn N (deriv A 0) (w - (c • p + sn • q)) (-sn • p + c • q))]

end HryniewiczCriterion

/-!
# Small transverse loop: the positively oriented case

`E(z + ρ (cos 2πt a + sin 2πt b))` with `det(γ0, γ'0, dE a, dE b) > 0` has Gauss integral `1`
with `γ` for small `ρ`: in the stereographic chart the loop is `A₀ + ρ V` with `V` uniformly
close to the round circle `cos p + sin q` (Fréchet derivative of `σ ∘ E`), so it is homotopic to
the round circle (`td_stage`), as is the meridian (`mer_stage1`), whose Gauss integral is `1`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma td_deriv_perp {A : ℝ → R4} (hd : Differentiable ℝ A) {N : R4}
    (hAN : ∀ s, dot4 (A s) N = 0) (s : ℝ) : dot4 (deriv A s) N = 0 := by
  have h := gl_hasDerivAt_dot4 (hd s).hasDerivAt (hasDerivAt_const s N)
  have hc : (fun x => dot4 (A x) N) = fun _ => (0 : ℝ) := funext hAN
  rw [hc] at h
  have := h.unique (hasDerivAt_const s 0)
  rw [gl_dot4_zero_right, add_zero] at this
  exact this

lemma td_line_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (z w : F) :
    HasDerivAt (fun s : ℝ => z + s • w) w 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z

theorem td_core (E : Plane → R4) (z : Plane) (r : ℝ) (hr : 0 < r)
    (hE : ContDiffOn ℝ 2 E (Metric.ball z r))
    (hEunit : ∀ v ∈ Metric.ball z r, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ s, γ (s + 1) = γ s)
    (hγunit : ∀ s, euclidNorm (γ s) = 1) (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hz : E z = γ 0) (a b : Plane) (ha1 : ‖a‖ ≤ 1) (hb1 : ‖b‖ ≤ 1)
    (hdet : 0 < Matrix.det (Matrix.of ![γ 0, deriv γ 0, fderiv ℝ E z a, fderiv ℝ E z b]))
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ s ≠ N)
    (hNE : ∀ v ∈ Metric.ball z r, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N γ (fun t => E (z + ρ • (Real.cos (2 * Real.pi * t) • a +
        Real.sin (2 * Real.pi * t) • b))) = 1 := by
  have hNN : dot4 N N = 1 := gl_dot4_self_of_unit hN
  have hN1 : ‖N‖ ≤ 1 := tw_norm_le_one_of_unit hN
  set y := γ 0 with hydef
  have hyy : dot4 y y = 1 := gl_dot4_self_of_unit (hγunit 0)
  have hk : dot4 y N ≠ 1 := fun h => hNγ 0 (gl_eq_of_dot4_eq_one hyy hNN h)
  have hk1 : 1 - dot4 y N ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have hkpos : 0 < 1 - dot4 y N := by
    have h := gl_dot4_self_nonneg (y - N)
    rw [gl_dot4_sub_left, gl_dot4_sub_right, gl_dot4_sub_right, hyy, hNN,
      gl_dot4_comm N y] at h
    rcases (sub_nonneg.2 (by linarith : dot4 y N ≤ 1)).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (by linarith : dot4 y N = 1) hk
  -- the projected knot
  set A : ℝ → R4 := fun s => stereographicFrom N (γ s) with hAdef
  have hA : ContDiff ℝ 2 A :=
    gl_contDiff_stereo N hγ fun s => tw_one_sub_dot_ne hN (hγunit s) (hNγ s)
  have hAper : ∀ s, A (s + 1) = A s := fun s => by simp only [A, hγper]
  have hAN : ∀ s, dot4 (A s) N = 0 := fun s => gl_stereo_dot_N hNN _
  have hAinj : ∀ s t, A s = A t → ∃ n : ℤ, t = s + n := by
    intro s t h
    apply hinj
    by_contra hne
    exact tw_stereo_ne hN (hγunit s) (hγunit t) (hNγ s) (hNγ t) hne h
  have hda : deriv A 0 = mer_dS N y (deriv γ 0) :=
    (mer_hasDerivAt_stereo N ((hγ.differentiable (by norm_num)) 0).hasDerivAt hk1).deriv
  -- the surface near `z`
  have hzU : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hEd : DifferentiableAt ℝ E z :=
    (hE.contDiffAt (Metric.isOpen_ball.mem_nhds hzU)).differentiableAt (by norm_num)
  set f₁ := fderiv ℝ E z a with hf₁
  set f₂ := fderiv ℝ E z b with hf₂
  have hperpE : ∀ w : Plane, dot4 (fderiv ℝ E z w) y = 0 := by
    intro w
    have hc : HasDerivAt (fun s : ℝ => E (z + s • w)) (fderiv ℝ E z w) 0 := by
      exact hEd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (td_line_hasDerivAt z w) (by simp)
    have h2 := gl_hasDerivAt_dot4 hc hc
    have hev : (fun s : ℝ => dot4 (E (z + s • w)) (E (z + s • w))) =ᶠ[𝓝 0] fun _ => 1 := by
      have hm : ∀ᶠ s in 𝓝 (0 : ℝ), z + s • w ∈ Metric.ball z r := by
        have hcont : Continuous fun s : ℝ => z + s • w := by fun_prop
        exact hcont.continuousAt.preimage_mem_nhds (by simpa using Metric.isOpen_ball.mem_nhds hzU)
      filter_upwards [hm] with s hs
      exact gl_dot4_self_of_unit (hEunit _ hs)
    have h3 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq hev
    have h4 := h2.unique h3
    simp only [zero_smul, add_zero] at h4
    rw [hz, gl_dot4_comm (γ 0)] at h4
    linarith
  -- the derivative of stereographic projection
  have hdN : Differentiable ℝ (fun x : R4 => dot4 x N) := by unfold dot4; fun_prop
  have hSd : DifferentiableAt ℝ (fun x : R4 => stereographicFrom N x) y := by
    unfold stereographicFrom
    exact (((differentiableAt_const _).sub (hdN y)).inv hk1).smul
      (differentiableAt_id.sub ((hdN y).smul_const N))
  have hSf : ∀ f : R4, fderiv ℝ (fun x => stereographicFrom N x) y f = mer_dS N y f := by
    intro f
    have h1 := hSd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (td_line_hasDerivAt y f) (by simp)
    have h2 := mer_hasDerivAt_stereo N (td_line_hasDerivAt y f) (by simpa using hk1)
    simp only [zero_smul, add_zero] at h2
    exact h1.unique h2
  set p := mer_L N y f₁ with hpdef
  set q := mer_L N y f₂ with hqdef
  have hp' : p = mer_dS N y f₁ := by
    rw [hpdef, mer_L_eq_dS hyy hk, hperpE a, zero_smul, sub_zero]
  have hq' : q = mer_dS N y f₂ := by
    rw [hqdef, mer_L_eq_dS hyy hk, hperpE b, zero_smul, sub_zero]
  set G : Plane → R4 := fun v => stereographicFrom N (E v) with hGdef
  obtain ⟨G', hG, hG'a, hG'b⟩ : ∃ G' : Plane →L[ℝ] R4, HasFDerivAt G G' z ∧ G' a = p ∧
      G' b = q := by
    have hSd' : DifferentiableAt ℝ (fun x : R4 => stereographicFrom N x) (E z) := by
      rw [hz]; exact hSd
    refine ⟨(fderiv ℝ (fun x => stereographicFrom N x) y).comp (fderiv ℝ E z), ?_, ?_, ?_⟩
    · have h := hSd'.hasFDerivAt.comp z hEd.hasFDerivAt
      rw [hz] at h
      exact h
    · rw [hp']; exact hSf f₁
    · rw [hq']; exact hSf f₂
  have hGz : G z = A 0 := by
    show stereographicFrom N (E z) = stereographicFrom N (γ 0); rw [hz]
  -- transversality in the chart
  have hperp : ∀ f : R4, dot4 (f - dot4 f y • y) y = 0 := fun f => by
    rw [gl_dot4_sub_left, gl_dot4_smul_left, hyy]; ring
  have hγ'y : dot4 (deriv γ 0) y = 0 := by
    rw [gl_dot4_comm]
    exact tw_dot_deriv_eq_zero (hγ.differentiable (by norm_num)) hγunit 0
  have hvol : 0 < volumeIn N (deriv A 0) p q := by
    rw [hda, hpdef, hqdef, mer_L_eq_dS hyy hk, mer_L_eq_dS hyy hk,
      mer_orient hNN hyy hk hγ'y (hperp f₁) (hperp f₂)]
    have e : gl_det4 y (deriv γ 0) (f₁ - dot4 f₁ y • y) (f₂ - dot4 f₂ y • y) =
        gl_det4 y (deriv γ 0) f₁ f₂ := by
      simp only [gl_det4, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, ← gl_det_eq_det4]
    exact div_pos hdet (pow_pos hkpos 3)
  have ha : deriv A 0 ≠ 0 := by
    intro h; rw [h, gl_volumeIn_zero1] at hvol; exact lt_irrefl _ hvol
  have hpN : dot4 p N = 0 := mer_L_perp hNN f₁
  have hqN : dot4 q N = 0 := mer_L_perp hNN f₂
  -- constants
  have hna : 0 < ‖deriv A 0‖ := norm_pos_iff.2 ha
  set P₀ := ‖p‖ + ‖q‖ with hP₀
  have hP₀0 : 0 ≤ P₀ := by positivity
  set η := volumeIn N (deriv A 0) p q / (48 * (‖deriv A 0‖ * (P₀ + 1))) with hηdef
  have hη : 0 < η := by positivity
  have hηb : 24 * (‖deriv A 0‖ * η * P₀) ≤ volumeIn N (deriv A 0) p q / 2 := by
    have e : 24 * (‖deriv A 0‖ * η * P₀) = volumeIn N (deriv A 0) p q * P₀ / (2 * (P₀ + 1)) := by
      rw [hηdef]; field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set v₀ := volumeIn N (deriv A 0) p q / 2 with hv₀def
  have hv₀ : 0 < v₀ := by positivity
  obtain ⟨r₀, hr₀, hcone⟩ := mer_cone N hN1 A hA hAper hAinj ha
    (M := P₀ + 2 + η) (Z := P₀ + 2) (by positivity) (by positivity) hv₀
  have hv₀b : v₀ ≤ volumeIn N (deriv A 0) p q - 24 * (‖deriv A 0‖ * η * P₀) := by
    rw [hv₀def]; linarith
  -- uniformity of the rescaled meridian near `l = 0`
  have hD0 : ∀ v : R4, mer_D N y v 0 = 1 - dot4 y N := fun v => by simp [mer_D]
  obtain ⟨l₁, hl₁, hu1⟩ := mer_unif (g := fun l t => -dot4 (y + l • mer_v f₁ f₂ t)
      (y + l • mer_v f₁ f₂ t)) (c := -(1 / 2))
    (fun t => (Continuous.continuousAt (by
      have hv : Continuous fun p : ℝ × ℝ => y + p.1 • mer_v f₁ f₂ p.2 :=
        continuous_const.add (continuous_fst.smul ((mer_contDiff_v f₁ f₂).continuous.comp
          continuous_snd))
      exact (gl_continuous_dot4 hv hv).neg)))
    (fun l t => by simp only [mer_v_periodic])
    (fun t => by simp only [zero_smul, add_zero, hyy]; norm_num)
  obtain ⟨l₂, hl₂, hu2⟩ := mer_unif (g := fun l t => -mer_D N y (mer_v f₁ f₂ t) l)
    (c := -((1 - dot4 y N) / 2))
    (fun t => (Continuous.continuousAt ((mer_continuous_D N y
      ((mer_contDiff_v f₁ f₂).continuous.comp continuous_snd) continuous_fst).neg)))
    (fun l t => by simp only [mer_v_periodic])
    (fun t => by simp only [hD0]; linarith)
  obtain ⟨l₃, hl₃, hu3⟩ := mer_unif (g := fun l t =>
      ‖mer_W N y (mer_v f₁ f₂ t) l - mer_L N y (mer_v f₁ f₂ t)‖) (c := η)
    (fun t => by
      have hvc : Continuous fun p : ℝ × ℝ => mer_v f₁ f₂ p.2 :=
        (mer_contDiff_v f₁ f₂).continuous.comp continuous_snd
      have h1 := mer_continuousAt_W N y hvc continuous_fst (x₀ := ((0 : ℝ), t))
        (by simp only [hD0]; exact hk1) hk1
      exact (h1.sub (mer_continuous_L N y hvc).continuousAt).norm)
    (fun l t => by simp only [mer_v_periodic])
    (fun t => by simp only [mer_W_zero hyy, sub_self, norm_zero]; exact hη)
  set l₀ := min l₁ (min l₂ l₃) with hl₀
  have hl₀pos : 0 < l₀ := lt_min hl₁ (lt_min hl₂ hl₃)
  have hU1 : ∀ l, |l| < l₀ → ∀ t, y + l • mer_v f₁ f₂ t ≠ 0 := by
    intro l hl t h0
    have := hu1 l (hl.trans_le (min_le_left _ _)) t
    rw [h0, gl_dot4_zero_right] at this
    linarith
  have hU2 : ∀ l, |l| < l₀ → ∀ t, mer_D N y (mer_v f₁ f₂ t) l ≠ 0 := by
    intro l hl t
    have := hu2 l (hl.trans_le ((min_le_right _ _).trans (min_le_left _ _))) t
    have : 0 < mer_D N y (mer_v f₁ f₂ t) l := by linarith
    exact this.ne'
  have hU3 : ∀ l, |l| < l₀ → ∀ t,
      ‖mer_W N y (mer_v f₁ f₂ t) l - mer_L N y (mer_v f₁ f₂ t)‖ ≤ η := by
    intro l hl t
    exact (hu3 l (hl.trans_le ((min_le_right _ _).trans (min_le_right _ _))) t).le
  -- the meridian
  obtain ⟨ε₀, hε₀, hmer⟩ := gaussLinkingIntegral_meridian_eq_one γ hγ hγper hγunit hinj f₁ f₂
    hdet N hN hNγ
  -- the Fréchet estimate
  have hκ : (0 : ℝ) < η / 2 := by positivity
  obtain ⟨δ, hδ, hδG⟩ := Metric.eventually_nhds_iff.1 (hG.isLittleO.def hκ)
  refine ⟨min (min r₀ l₀) (min ε₀ (min (δ / 2) (r / 2))),
    lt_min (lt_min hr₀ hl₀pos) (lt_min hε₀ (lt_min (by positivity) (by positivity))), ?_⟩
  intro ρ hρ hρ₀
  have hρr₀ : ρ < r₀ := hρ₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hρl₀ : ρ < l₀ := hρ₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hρε : ρ < ε₀ := hρ₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρδ : ρ < δ / 2 :=
    hρ₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρr : ρ < r / 2 :=
    hρ₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the plane loop
  set c : ℝ → Plane := fun t => Real.cos (2 * Real.pi * t) • a + Real.sin (2 * Real.pi * t) • b
    with hcdef
  have hcn : ∀ t, ‖c t‖ ≤ 2 := by
    intro t
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one (2 * Real.pi * t)
    have h2 := Real.abs_sin_le_one (2 * Real.pi * t)
    calc |Real.cos (2 * Real.pi * t)| * ‖a‖ + |Real.sin (2 * Real.pi * t)| * ‖b‖
        ≤ 1 * 1 + 1 * 1 := add_le_add (mul_le_mul h1 ha1 (norm_nonneg _) zero_le_one)
          (mul_le_mul h2 hb1 (norm_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  have hcper : ∀ t, c (t + 1) = c t := by
    intro t
    have h1 : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.cos_add_two_pi]
    have h2 : Real.sin (2 * Real.pi * (t + 1)) = Real.sin (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Real.sin_add_two_pi]
    simp only [c, h1, h2]
  have hcc : ContDiff ℝ 2 c := by simp only [hcdef]; fun_prop
  have hdist : ∀ t, dist (z + ρ • c t) z ≤ 2 * ρ := by
    intro t
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    have := mul_le_mul_of_nonneg_left (hcn t) hρ.le
    linarith only [this]
  have hmem : ∀ t, z + ρ • c t ∈ Metric.ball z r := fun t =>
    Metric.mem_ball.2 ((hdist t).trans_lt (by linarith only [hρr, hr]))
  -- the chart loop `A₀ + ρ V`
  set V : ℝ → R4 := fun t => ρ⁻¹ • (G (z + ρ • c t) - A 0) with hVdef
  have hEl : ContDiff ℝ 2 fun t => E (z + ρ • c t) :=
    hE.comp_contDiff (contDiff_const.add (hcc.const_smul ρ)) hmem
  have hGl : ContDiff ℝ 2 fun t => G (z + ρ • c t) :=
    gl_contDiff_stereo N hEl fun t => tw_one_sub_dot_ne hN (hEunit _ (hmem t)) (hNE _ (hmem t))
  have hV : ContDiff ℝ 2 V := (hGl.sub contDiff_const).const_smul ρ⁻¹
  have hVper : ∀ t, V (t + 1) = V t := fun t => by simp only [V, hcper t]
  have hVN : ∀ t, dot4 (V t) N = 0 := fun t => by
    simp only [V, G, gl_dot4_smul_left, gl_dot4_sub_left, gl_stereo_dot_N hNN, hAN, sub_zero,
      mul_zero]
  have hVη : ∀ t, ‖V t - mer_v p q t‖ ≤ η := by
    intro t
    have hlin : G' (ρ • c t) = ρ • mer_v p q t := by
      rw [map_smul]
      congr 1
      show G' (Real.cos (2 * Real.pi * t) • a + Real.sin (2 * Real.pi * t) • b) = _
      rw [map_add, map_smul, map_smul, hG'a, hG'b]; rfl
    have hest := hδG ((hdist t).trans_lt (by linarith only [hρδ]))
    rw [add_sub_cancel_left, hlin, hGz] at hest
    have e : V t - mer_v p q t = ρ⁻¹ • (G (z + ρ • c t) - A 0 - ρ • mer_v p q t) := by
      simp only [V, smul_sub, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
    have hn : ‖ρ • c t‖ ≤ 2 * ρ := by
      rw [norm_smul, Real.norm_of_nonneg hρ.le]
      have := mul_le_mul_of_nonneg_left (hcn t) hρ.le
      linarith only [this]
    calc ρ⁻¹ * ‖G (z + ρ • c t) - A 0 - ρ • mer_v p q t‖ ≤ ρ⁻¹ * (η / 2 * (2 * ρ)) := by
          gcongr; exact hest.trans (by gcongr)
      _ = η := by field_simp
  have hS := td_stage N hNN A hA hAper hAN p q hpN hqN hη.le hcone (by linarith only []) (by linarith only [])
    hv₀b V hV hVper hVN hVη hρ hρr₀
  have hS1 := mer_stage1 N y f₁ f₂ hNN hk1 hyy A hA hAper hAN rfl hη.le hcone
    (by rw [← hpdef, ← hqdef]; linarith only []) (by rw [← hpdef, ← hqdef]; linarith only [])
    (by rw [← hpdef, ← hqdef]; exact hv₀b.trans (le_refl _))
    hU1 hU2 hU3 hρ hρr₀ hρl₀
  have hloop : (fun t => stereographicFrom N (E (z + ρ • (Real.cos (2 * Real.pi * t) • a +
      Real.sin (2 * Real.pi * t) • b)))) = fun t => A 0 + ρ • V t := by
    funext t
    simp only [V, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel, G, c]
  have hm := hmer ρ hρ hρε
  rw [tw_gauss_eq_G] at hm ⊢
  rw [hloop, hS]
  have hS1' : tw_G N A (fun t => A 0 + ρ • mer_v p q t) =
      tw_G N A (fun t => stereographicFrom N (radialNormalize (y + ρ • mer_v f₁ f₂ t))) :=
    hS1.symm
  rw [hS1']
  have e : (fun t => stereographicFrom N (radialNormalize (y + ρ • mer_v f₁ f₂ t))) =
      fun t => stereographicFrom N ((fun t => radialNormalize (γ 0 +
        ρ • (Real.cos (2 * Real.pi * t) • f₁ + Real.sin (2 * Real.pi * t) • f₂))) t) := by
    funext t; simp only [mer_v, hydef]
  rw [e]
  exact hm

end HryniewiczCriterion

/-!
# Small transverse loop: both orientations
-/


noncomputable section

namespace HryniewiczCriterion

lemma td_norm_single_le (i : Fin 2) : ‖(Pi.single i 1 : Plane)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

lemma td_circlePoint_eq (s : ℝ) : circlePoint s =
    Real.cos (2 * Real.pi * s) • (Pi.single 0 1 : Plane) +
      Real.sin (2 * Real.pi * s) • (Pi.single 1 1 : Plane) := by
  ext i; fin_cases i <;> simp [circlePoint]

lemma td_circlePoint_rev (s : ℝ) : circlePoint s =
    Real.cos (2 * Real.pi * (1 / 4 - s)) • (Pi.single 1 1 : Plane) +
      Real.sin (2 * Real.pi * (1 / 4 - s)) • (Pi.single 0 1 : Plane) := by
  have h : 2 * Real.pi * (1 / 4 - s) = Real.pi / 2 - 2 * Real.pi * s := by ring
  rw [h]
  ext i; fin_cases i <;> simp [circlePoint, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

/-- Chart-level symmetry for a small loop on the surface against the knot. -/
lemma td_symm_loop (E : Plane → R4) (z : Plane) (r : ℝ)
    (hE : ContDiffOn ℝ 2 E (Metric.ball z r))
    (hEunit : ∀ v ∈ Metric.ball z r, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (hmiss : ∀ v ∈ Metric.ball z r, v ≠ z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ Metric.ball z r, E v ≠ N)
    (c : ℝ → Plane) (hc : ContDiff ℝ 2 c) (hcne : ∀ t, c t ≠ 0) (hcn : ∀ t, ‖c t‖ ≤ 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : 2 * ρ < r) :
    tw_G N (fun s => stereographicFrom N (E (z + ρ • c s))) (fun t => stereographicFrom N (γ t)) =
      tw_G N (fun t => stereographicFrom N (γ t)) (fun s => stereographicFrom N (E (z + ρ • c s))) := by
  have hmem : ∀ t, z + ρ • c t ∈ Metric.ball z r := by
    intro t
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    have := mul_le_mul_of_nonneg_left (hcn t) hρ.le
    linarith only [this, hρr]
  have hne : ∀ t, z + ρ • c t ≠ z := fun t h => by
    have h' : ρ • c t = 0 := by simpa using h
    rcases smul_eq_zero.1 h' with h0 | h0
    · exact hρ.ne' h0
    · exact hcne t h0
  have hEl : ContDiff ℝ 2 fun t => E (z + ρ • c t) :=
    hE.comp_contDiff (contDiff_const.add (hc.const_smul ρ)) hmem
  have hA : ContDiff ℝ 2 fun s => stereographicFrom N (E (z + ρ • c s)) :=
    gl_contDiff_stereo N hEl fun t => tw_one_sub_dot_ne hN (hEunit _ (hmem t)) (hNE _ (hmem t))
  have hB : ContDiff ℝ 2 fun t => stereographicFrom N (γ t) :=
    gl_contDiff_stereo N hγ fun t => tw_one_sub_dot_ne hN (hγunit t) (hNγ t)
  exact td_tw_G_symm N _ _ (hA.of_le (by norm_num)) (hB.of_le (by norm_num)) fun s t =>
    tw_stereo_ne hN (hEunit _ (hmem s)) (hγunit t) (hNE _ (hmem s)) (hNγ t)
      (hmiss _ (hmem s) (hne s) t)

theorem gaussLinkingIntegral_small_transverse_loop' (E : Plane → R4) (z : Plane) (r : ℝ)
    (hr : 0 < r)
    (hE : ContDiffOn ℝ 2 E (Metric.ball z r))
    (hEunit : ∀ v ∈ Metric.ball z r, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (t₀ : ℝ) (hz : E z = γ t₀)
    (hmiss : ∀ v ∈ Metric.ball z r, v ≠ z → ∀ t, E v ≠ γ t)
    (hdet : Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
        fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) ≠ 0)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ Metric.ball z r, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
        if 0 < Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
          fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) then 1 else -1 := by
  -- shift the knot so that the crossing is at `t = 0`
  set g : ℝ → R4 := fun t => γ (t + t₀) with hgdef
  have hg : ContDiff ℝ 2 g := hγ.comp (contDiff_id.add contDiff_const)
  have hgper : ∀ t, g (t + 1) = g t := fun t => by
    simp only [g, show t + 1 + t₀ = t + t₀ + 1 by ring, hγper]
  have hgunit : ∀ t, euclidNorm (g t) = 1 := fun t => hγunit _
  have hginj : ∀ s t, g s = g t → ∃ n : ℤ, t = s + n := by
    intro s t h
    obtain ⟨n, hn⟩ := hγinj _ _ h
    exact ⟨n, by linarith⟩
  have hg0 : g 0 = γ t₀ := by simp [g]
  have hg'0 : deriv g 0 = deriv γ t₀ := by
    rw [hgdef, deriv_comp_add_const, zero_add]
  have hNg : ∀ t, g t ≠ N := fun t => hNγ _
  have hmissg : ∀ v ∈ Metric.ball z r, v ≠ z → ∀ t, E v ≠ g t := fun v hv hvz t =>
    hmiss v hv hvz _
  set e₀ : Plane := Pi.single 0 1
  set e₁ : Plane := Pi.single 1 1
  set d := Matrix.det (Matrix.of ![γ t₀, deriv γ t₀, fderiv ℝ E z e₀, fderiv ℝ E z e₁]) with hd
  -- Gauss integral of the boundary loop against the shifted knot
  have hshift : ∀ ρ : ℝ, gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
      (4 * Real.pi)⁻¹ * tw_G N (fun s => stereographicFrom N (E (z + ρ • circlePoint s)))
        (fun t => stereographicFrom N (g t)) := by
    intro ρ
    rw [tw_gauss_eq_G]
    congr 1
    exact (td_tw_G_shift N _ (fun t => stereographicFrom N (γ t))
      (fun t => by simp only [hγper]) t₀).symm
  have hcp : ContDiff ℝ 2 circlePoint := by
    rw [contDiff_pi]; intro i; fin_cases i <;> simp [circlePoint] <;> fun_prop
  have hcpne : ∀ s, circlePoint s ≠ 0 := fun s h => by
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [circlePoint] at h0 h1
    have := Real.cos_sq_add_sin_sq (2 * Real.pi * s)
    rw [h0, h1] at this; norm_num at this
  have hcpn : ∀ s, ‖circlePoint s‖ ≤ 2 := by
    intro s
    rw [td_circlePoint_eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one (2 * Real.pi * s)
    have h2 := Real.abs_sin_le_one (2 * Real.pi * s)
    calc |Real.cos (2 * Real.pi * s)| * ‖e₀‖ + |Real.sin (2 * Real.pi * s)| * ‖e₁‖
        ≤ 1 * 1 + 1 * 1 := add_le_add (mul_le_mul h1 (td_norm_single_le 0) (norm_nonneg _)
          zero_le_one) (mul_le_mul h2 (td_norm_single_le 1) (norm_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  have hsymm := fun ρ (hρ : 0 < ρ) (hρr : 2 * ρ < r) =>
    td_symm_loop E z r hE hEunit g hg hgunit hmissg N hN hNg hNE circlePoint hcp hcpne hcpn hρ hρr
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- negative orientation: swap the frame, reverse the loop
    have hdet' : 0 < Matrix.det (Matrix.of ![g 0, deriv g 0, fderiv ℝ E z e₁, fderiv ℝ E z e₀]) := by
      rw [hg0, hg'0, gl_det_eq_det4]
      have hneg' : gl_det4 (γ t₀) (deriv γ t₀) (fderiv ℝ E z e₀) (fderiv ℝ E z e₁) < 0 := by
        rw [← gl_det_eq_det4]; exact hneg
      have : gl_det4 (γ t₀) (deriv γ t₀) (fderiv ℝ E z e₁) (fderiv ℝ E z e₀) =
          -gl_det4 (γ t₀) (deriv γ t₀) (fderiv ℝ E z e₀) (fderiv ℝ E z e₁) := by
        simp only [gl_det4]; ring
      linarith
    obtain ⟨ρ₀, hρ₀, hcore⟩ := td_core E z r hr hE hEunit g hg hgper hgunit hginj
      (by rw [hg0, hz]) e₁ e₀ (td_norm_single_le 1) (td_norm_single_le 0) hdet' N hN hNg hNE
    refine ⟨min ρ₀ (r / 4), lt_min hρ₀ (by positivity), fun ρ hρ hρρ => ?_⟩
    have hρ1 : ρ < ρ₀ := hρρ.trans_le (min_le_left _ _)
    have hρ2 : 2 * ρ < r := by linarith [min_le_right ρ₀ (r / 4)]
    have hc := hcore ρ hρ hρ1
    set L' : ℝ → R4 := fun t => E (z + ρ • (Real.cos (2 * Real.pi * t) • e₁ +
      Real.sin (2 * Real.pi * t) • e₀)) with hL'
    have hL'per : ∀ t, stereographicFrom N (L' (t + 1)) = stereographicFrom N (L' t) := by
      intro t
      have h1 : Real.cos (2 * Real.pi * (t + 1)) = Real.cos (2 * Real.pi * t) := by
        rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
          Real.cos_add_two_pi]
      have h2 : Real.sin (2 * Real.pi * (t + 1)) = Real.sin (2 * Real.pi * t) := by
        rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
          Real.sin_add_two_pi]
      simp only [L', h1, h2]
    have hrev : (fun s => stereographicFrom N (E (z + ρ • circlePoint s))) =
        fun s => stereographicFrom N (L' (1 / 4 - s)) := by
      funext s; rw [td_circlePoint_rev s]
    have hsymm' : tw_G N (fun s => stereographicFrom N (L' s)) (fun t => stereographicFrom N (g t)) =
        tw_G N (fun t => stereographicFrom N (g t)) (fun s => stereographicFrom N (L' s)) := by
      have hc' : ContDiff ℝ 2 fun t : ℝ => (Real.cos (2 * Real.pi * t) • e₁ +
          Real.sin (2 * Real.pi * t) • e₀ : Plane) := by fun_prop
      refine td_symm_loop E z r hE hEunit g hg hgunit hmissg N hN hNg hNE _ hc' ?_ ?_ hρ hρ2
      · intro t h
        have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [e₀, e₁] at h0 h1
        have := Real.cos_sq_add_sin_sq (2 * Real.pi * t)
        rw [h0, h1] at this; norm_num at this
      · intro t
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have h1 := Real.abs_cos_le_one (2 * Real.pi * t)
        have h2 := Real.abs_sin_le_one (2 * Real.pi * t)
        calc |Real.cos (2 * Real.pi * t)| * ‖e₁‖ + |Real.sin (2 * Real.pi * t)| * ‖e₀‖
            ≤ 1 * 1 + 1 * 1 := add_le_add (mul_le_mul h1 (td_norm_single_le 1) (norm_nonneg _)
              zero_le_one) (mul_le_mul h2 (td_norm_single_le 0) (norm_nonneg _) zero_le_one)
          _ = 2 := by norm_num
    rw [tw_gauss_eq_G] at hc
    have hr := td_tw_G_reverse N (fun s => stereographicFrom N (L' s))
      (fun t => stereographicFrom N (g t)) hL'per (1 / 4)
    rw [hshift, hrev, hr, hsymm']
    have hnot : ¬ 0 < d := not_lt.2 hneg.le
    rw [if_neg hnot]
    have : (4 * Real.pi)⁻¹ * tw_G N (fun t => stereographicFrom N (g t))
        (fun s => stereographicFrom N (L' s)) = 1 := hc
    linarith
  · -- positive orientation
    have hdet' : 0 < Matrix.det (Matrix.of ![g 0, deriv g 0, fderiv ℝ E z e₀, fderiv ℝ E z e₁]) := by
      rw [hg0, hg'0]; exact hpos
    obtain ⟨ρ₀, hρ₀, hcore⟩ := td_core E z r hr hE hEunit g hg hgper hgunit hginj
      (by rw [hg0, hz]) e₀ e₁ (td_norm_single_le 0) (td_norm_single_le 1) hdet' N hN hNg hNE
    refine ⟨min ρ₀ (r / 4), lt_min hρ₀ (by positivity), fun ρ hρ hρρ => ?_⟩
    have hρ1 : ρ < ρ₀ := hρρ.trans_le (min_le_left _ _)
    have hρ2 : 2 * ρ < r := by linarith [min_le_right ρ₀ (r / 4)]
    have hc := hcore ρ hρ hρ1
    rw [tw_gauss_eq_G] at hc
    rw [hshift, hsymm ρ hρ hρ2, if_pos hpos]
    have e : (fun s => stereographicFrom N (E (z + ρ • circlePoint s))) =
        fun t => stereographicFrom N (E (z + ρ • (Real.cos (2 * Real.pi * t) • e₀ +
          Real.sin (2 * Real.pi * t) • e₁))) := by
      funext s; rw [td_circlePoint_eq s]
    rw [e]
    exact hc

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (E : Plane → R4) (z : Plane) (r : ℝ) (hr : 0 < r)
    (hE : ContDiffOn ℝ 2 E (Metric.ball z r))
    (hEunit : ∀ v ∈ Metric.ball z r, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (t₀ : ℝ) (hz : E z = γ t₀)
    (hmiss : ∀ v ∈ Metric.ball z r, v ≠ z → ∀ t, E v ≠ γ t)
    (hdet : Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
        fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) ≠ 0)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ Metric.ball z r, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
        if 0 < Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
          fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) then 1 else -1 :=
  HryniewiczCriterion.gaussLinkingIntegral_small_transverse_loop' E z r hr hE hEunit γ hγ hγper hγunit hγinj t₀ hz hmiss hdet N hN hNγ hNE
