-- Prove2me | solution 1 for HryniewiczCriterion.disk_conormal_pushOff_linking_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T02:22:07.438472+00:00
-- url     : https://prove2.me/submissions/7bd3f95c-fc41-4e91-b116-25b55defb909

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
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Shift

open HryniewiczCriterion
open scoped ContDiff
open MeasureTheory Set
open scoped ContDiff Topology
open Set Filter Topology
open Complex MeasureTheory Set
open Complex
open Complex Set
open Set

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

/-- A smooth map whose differential at `p` is injective has a smooth local left inverse
near `e p`: there is `g`, smooth at `e p`, with `g (e q) = q` for all `q` near `p`. -/
theorem exists_contDiffAt_leftInverse_of_injective_fderiv_aux
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : E → F} {p : E} (he : ContDiffAt ℝ ∞ e p)
    (hinj : Function.Injective (fderiv ℝ e p)) :
    ∃ g : F → E, ContDiffAt ℝ ∞ g (e p) ∧ ∀ᶠ q in 𝓝 p, g (e q) = q := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL⟩ := ((fderiv ℝ e p : E →L[ℝ] F) : E →ₗ[ℝ] F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  let Lc : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  let f : E → E := fun q => Lc (e q)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcomp : Lc.comp (fderiv ℝ e p) = ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) := by
    ext v
    have := congrArg (fun φ : E →ₗ[ℝ] E => φ v) hL
    simpa [Lc] using this
  have hfd : HasFDerivAt f ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    rw [← hcomp]
    exact Lc.hasFDerivAt.comp p (he.differentiableAt (by simp)).hasFDerivAt
  have hf : ContDiffAt ℝ ∞ f p := Lc.contDiff.contDiffAt.comp p he
  refine ⟨fun y => hf.localInverse hfd hn (Lc y), ?_, ?_⟩
  · exact (hf.to_localInverse hfd hn).comp (e p) Lc.contDiff.contDiffAt
  · exact (hf.hasStrictFDerivAt' hfd hn).eventually_left_inverse

/-!
# Seifert push-off: the outward push-off misses the cone over the disk

For a smooth disk `e` transverse to the radial direction along `D`, and a loop `u` on the
boundary circle with an outward field `a` (`⟨u, a⟩ > 0`), the points
`e(u) + ε de(u) a` miss the cone `{μ e(v) : v ∈ D, μ ≥ 0}` for all small `ε > 0`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma sf_disk_compact : IsCompact closedUnitDisk := by
  have hcl : IsClosed closedUnitDisk :=
    isClosed_le (by fun_prop) continuous_const
  have hsub : closedUnitDisk ⊆ Metric.closedBall (0 : Plane) 1 := by
    intro v hv
    simp only [closedUnitDisk, mem_setOf_eq] at hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    have h0 : |v 0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (v 1)])
    have h1 : |v 1| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (v 0)])
    revert i
    exact Fin.forall_fin_two.2 ⟨h0, h1⟩
  exact Metric.isCompact_of_isClosed_isBounded hcl (Metric.isBounded_closedBall.subset hsub)

/-- Local picture at a boundary point: a function `f`, strictly differentiable at `e u₀`,
with `f (μ e v) = |v|²` near `(u₀, 1)` and `f' (de(u₀) a₀) = 2 ⟨u₀, a₀⟩ > 0`. -/
lemma sf_local (e : Plane → R4) (hE : ContDiff ℝ ∞ e) (u₀ a₀ : Plane)
    (hinj : Function.Injective (fderiv ℝ e u₀)) (htr : e u₀ ∉ range (fderiv ℝ e u₀))
    (hua : 0 < u₀ 0 * a₀ 0 + u₀ 1 * a₀ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (f : R4 → ℝ) (f' : R4 →L[ℝ] ℝ), HasStrictFDerivAt f f' (e u₀) ∧
      0 < f' (fderiv ℝ e u₀ a₀) ∧
      ∀ (v : Plane) (μ : ℝ), ‖v - u₀‖ < δ → |μ - 1| < δ → f (μ • e v) = v 0 ^ 2 + v 1 ^ 2 := by
  set G : Plane × ℝ → R4 := fun p => p.2 • e p.1 with hGdef
  set p₀ : Plane × ℝ := (u₀, 1) with hp₀
  have hG : ContDiff ℝ ∞ G := contDiff_snd.smul (hE.comp contDiff_fst)
  have hde : HasFDerivAt e (fderiv ℝ e u₀) u₀ := ((hE.differentiable (by simp)) u₀).hasFDerivAt
  have hGd : HasFDerivAt G (p₀.2 • (fderiv ℝ e u₀).comp (ContinuousLinearMap.fst ℝ Plane ℝ) +
      (ContinuousLinearMap.snd ℝ Plane ℝ).smulRight (e p₀.1)) p₀ :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀)).smul (hde.comp p₀ (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)))
  have hGq : ∀ q : Plane × ℝ, fderiv ℝ G p₀ q = fderiv ℝ e u₀ q.1 + q.2 • e u₀ := by
    intro q; rw [hGd.fderiv]; simp [p₀]
  have hGinj : Function.Injective (fderiv ℝ G p₀) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    rw [hGq] at hq
    have hde1 : fderiv ℝ e u₀ q.1 = -(q.2 • e u₀) := eq_neg_of_add_eq_zero_left hq
    by_cases hm : q.2 = 0
    · rw [hm, zero_smul, neg_zero] at hde1
      have h1 : q.1 = 0 := hinj (by rw [hde1, map_zero])
      exact Prod.ext h1 hm
    · exfalso
      apply htr
      refine ⟨-(q.2)⁻¹ • q.1, ?_⟩
      rw [map_smul, hde1, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hm, one_smul]
  obtain ⟨L, hL, hLG⟩ := exists_contDiffAt_leftInverse_of_injective_fderiv_aux
    (hG.contDiffAt (x := p₀)) hGinj
  have hGp : G p₀ = e u₀ := by simp [G, p₀]
  rw [hGp] at hL
  set f : R4 → ℝ := fun y => (L y).1 0 ^ 2 + (L y).1 1 ^ 2 with hfdef
  have hfC : ContDiffAt ℝ ∞ f (e u₀) := by
    have h0 : ContDiffAt ℝ ∞ (fun y => (L y).1 0) (e u₀) :=
      ((contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst).contDiffAt.comp _ hL
    have h1 : ContDiffAt ℝ ∞ (fun y => (L y).1 1) (e u₀) :=
      ((contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_fst).contDiffAt.comp _ hL
    exact (h0.pow 2).add (h1.pow 2)
  have hfs : HasStrictFDerivAt f (fderiv ℝ f (e u₀)) (e u₀) := hfC.hasStrictFDerivAt (by simp)
  obtain ⟨δ, hδ, hδL⟩ := Metric.eventually_nhds_iff.1 hLG
  have hfG : ∀ (v : Plane) (μ : ℝ), ‖v - u₀‖ < δ → |μ - 1| < δ →
      f (μ • e v) = v 0 ^ 2 + v 1 ^ 2 := by
    intro v μ hv hμ
    have hd : dist (v, μ) p₀ < δ := by
      rw [Prod.dist_eq]
      exact max_lt (by rwa [dist_eq_norm]) (by rwa [Real.dist_eq])
    have := hδL hd
    simp only [G] at this
    simp only [f, this]
  refine ⟨δ, hδ, f, fderiv ℝ f (e u₀), hfs, ?_, hfG⟩
  -- the derivative along the curve `t ↦ e (u₀ + t a₀)`
  have hl : HasDerivAt (fun t : ℝ => u₀ + t • a₀) a₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a₀).const_add u₀
  have hc : HasDerivAt (fun t : ℝ => e (u₀ + t • a₀)) (fderiv ℝ e u₀ a₀) 0 :=
    hde.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h1 : HasDerivAt (fun t : ℝ => f (e (u₀ + t • a₀))) (fderiv ℝ f (e u₀) (fderiv ℝ e u₀ a₀)) 0 :=
    hfs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hp0 : HasDerivAt (fun t : ℝ => u₀ 0 + t * a₀ 0) (a₀ 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ 0)).const_add (u₀ 0)
  have hp1 : HasDerivAt (fun t : ℝ => u₀ 1 + t * a₀ 1) (a₀ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ 1)).const_add (u₀ 1)
  have h2 := (hp0.pow 2).add (hp1.pow 2)
  have hev : (fun t : ℝ => f (e (u₀ + t • a₀))) =ᶠ[𝓝 0]
      fun t : ℝ => (u₀ 0 + t * a₀ 0) ^ 2 + (u₀ 1 + t * a₀ 1) ^ 2 := by
    have ht : Tendsto (fun t : ℝ => u₀ + t • a₀) (𝓝 0) (𝓝 u₀) := by
      have : Continuous (fun t : ℝ => u₀ + t • a₀) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [ht (Metric.ball_mem_nhds u₀ hδ)] with t htb
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at htb
    have := hfG (u₀ + t • a₀) 1 htb (by simpa using hδ)
    rw [one_smul] at this
    exact this.trans (by simp [smul_eq_mul])
  have := h1.unique (h2.congr_of_eventuallyEq hev)
  rw [this]
  norm_num
  linarith

lemma sf_periodic_fract {α : Type*} {u : ℝ → α} (huper : ∀ s, u (s + 1) = u s) (x : ℝ) :
    u (Int.fract x) = u x := by
  rw [← Int.self_sub_floor, show x - (⌊x⌋ : ℝ) = x - ((⌊x⌋ : ℤ) : ℝ) * 1 by ring]
  exact Function.Periodic.sub_int_mul_eq (f := u) (c := (1 : ℝ)) huper ⌊x⌋

/-- The outward push-off of the boundary misses the cone over the disk. -/
theorem sf_separation (e : Plane → R4) (hE : ContDiff ℝ ∞ e)
    (hinjD : InjOn e closedUnitDisk)
    (hinj : ∀ v ∈ closedUnitDisk, Function.Injective (fderiv ℝ e v))
    (htr : ∀ v ∈ closedUnitDisk, e v ∉ range (fderiv ℝ e v))
    (h0 : ∀ v ∈ closedUnitDisk, e v ≠ 0)
    (hrad : ∀ v ∈ closedUnitDisk, ∀ v' ∈ closedUnitDisk, ∀ μ : ℝ, 0 < μ → μ • e v = e v' → μ = 1)
    (u a : ℝ → Plane) (hu : Continuous u) (ha : Continuous a)
    (huper : ∀ s, u (s + 1) = u s) (haper : ∀ s, a (s + 1) = a s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hua : ∀ s, 0 < u s 0 * a s 0 + u s 1 * a s 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s, ∀ v ∈ closedUnitDisk, ∀ μ : ℝ, 0 ≤ μ →
      e (u s) + ε • fderiv ℝ e (u s) (a s) ≠ μ • e v := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < 1 / ((n : ℝ) + 1) ∧ ∃ s, ∃ v ∈ closedUnitDisk,
      ∃ μ : ℝ, 0 ≤ μ ∧ e (u s) + ε • fderiv ℝ e (u s) (a s) = μ • e v :=
    fun n => hcon _ (by positivity)
  choose ε hε hεlt s v hv μ hμ heq using hseq
  set t : ℕ → ℝ := fun n => Int.fract (s n)
  have heq' : ∀ n, e (u (t n)) + ε n • fderiv ℝ e (u (t n)) (a (t n)) = μ n • e (v n) := by
    intro n; simp only [t, sf_periodic_fract huper, sf_periodic_fract haper]; exact heq n
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedUnitDisk) := isCompact_Icc.prod sf_disk_compact
  have hmem : ∀ n, (t n, v n) ∈ Icc (0 : ℝ) 1 ×ˢ closedUnitDisk :=
    fun n => ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hv n⟩
  obtain ⟨⟨s₀, v₀⟩, ⟨_, hv₀⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have ht : Tendsto (fun n => t (φ n)) atTop (𝓝 s₀) := (continuous_fst.tendsto _).comp hlim
  have hvl : Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := (continuous_snd.tendsto _).comp hlim
  have hεl : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hε _).le) (fun n => ?_)
    refine (hεlt (φ n)).le.trans ?_
    have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set x₀ := e (u s₀)
  set z₀ := fderiv ℝ e (u s₀) (a s₀)
  have hcz : Continuous fun s => fderiv ℝ e (u s) (a s) :=
    ((hE.continuous_fderiv (by simp)).comp hu).clm_apply ha
  have hxl : Tendsto (fun n => e (u (t (φ n)))) atTop (𝓝 x₀) :=
    ((hE.continuous.comp hu).tendsto s₀).comp ht
  have hzl : Tendsto (fun n => fderiv ℝ e (u (t (φ n))) (a (t (φ n)))) atTop (𝓝 z₀) :=
    (hcz.tendsto s₀).comp ht
  have hyl : Tendsto (fun n => e (u (t (φ n))) + ε (φ n) • fderiv ℝ e (u (t (φ n))) (a (t (φ n))))
      atTop (𝓝 x₀) := by simpa using hxl.add (hεl.smul hzl)
  have hμeq : ∀ n, μ n = ‖e (u (t n)) + ε n • fderiv ℝ e (u (t n)) (a (t n))‖ / ‖e (v n)‖ := by
    intro n
    rw [heq' n, norm_smul, Real.norm_of_nonneg (hμ n), mul_div_assoc,
      div_self (norm_ne_zero_iff.2 (h0 _ (hv n))), mul_one]
  have hev : Tendsto (fun n => e (v (φ n))) atTop (𝓝 (e v₀)) := (hE.continuous.tendsto v₀).comp hvl
  have hμl : Tendsto (fun n => μ (φ n)) atTop (𝓝 (‖x₀‖ / ‖e v₀‖)) := by
    simp_rw [hμeq]
    exact hyl.norm.div hev.norm (norm_ne_zero_iff.2 (h0 v₀ hv₀))
  set μ₀ := ‖x₀‖ / ‖e v₀‖
  have hyl' : Tendsto (fun n => e (u (t (φ n))) + ε (φ n) • fderiv ℝ e (u (t (φ n))) (a (t (φ n))))
      atTop (𝓝 (μ₀ • e v₀)) := by
    simp_rw [heq']; exact hμl.smul hev
  have hx₀eq : x₀ = μ₀ • e v₀ := tendsto_nhds_unique hyl hyl'
  have hu₀D : u s₀ ∈ closedUnitDisk := le_of_eq (hucirc s₀)
  have hx₀ne : x₀ ≠ 0 := h0 _ hu₀D
  have hμ₀pos : 0 < μ₀ := div_pos (norm_pos_iff.2 hx₀ne) (norm_pos_iff.2 (h0 v₀ hv₀))
  have hμ₀1 : μ₀ = 1 := hrad v₀ hv₀ (u s₀) hu₀D μ₀ hμ₀pos hx₀eq.symm
  have hvu : v₀ = u s₀ := hinjD hv₀ hu₀D (by rw [show e (u s₀) = x₀ from rfl, hx₀eq, hμ₀1, one_smul])
  rw [hμ₀1] at hμl
  rw [hvu] at hvl
  obtain ⟨δ, hδ, f, f', hf, hf'pos, hfG⟩ :=
    sf_local e hE (u s₀) (a s₀) (hinj _ hu₀D) (htr _ hu₀D) (hua s₀)
  rw [hasStrictFDerivAt_iff_isLittleO] at hf
  set κ := f' z₀
  have hκ : 0 < κ := hf'pos
  set c := κ / (4 * (‖z₀‖ + 1))
  have hc : 0 < c := by positivity
  have E1 := (hyl.prodMk_nhds hxl).eventually (hf.def hc)
  have E2 := hvl.eventually (Metric.ball_mem_nhds (u s₀) hδ)
  have E3 := hμl.eventually (Metric.ball_mem_nhds 1 hδ)
  have E4 := (((hu.tendsto s₀).comp ht)).eventually (Metric.ball_mem_nhds (u s₀) hδ)
  have E5 := ((f'.continuous.tendsto z₀).comp hzl).eventually (lt_mem_nhds (half_lt_self hκ))
  have E6 := hzl.norm.eventually (gt_mem_nhds (lt_add_one ‖z₀‖))
  obtain ⟨n, h1, h2, h3, h4, h5, h6⟩ := (E1.and (E2.and (E3.and (E4.and (E5.and E6))))).exists
  simp only [Function.comp_apply, Metric.mem_ball, dist_eq_norm, Real.dist_eq] at h1 h2 h3 h4 h5 h6
  set m := φ n
  set Z := fderiv ℝ e (u (t m)) (a (t m))
  have hfy : f (e (u (t m)) + ε m • Z) = v m 0 ^ 2 + v m 1 ^ 2 := by
    rw [heq' m]; exact hfG _ _ h2 h3
  have hfx : f (e (u (t m))) = 1 := by
    have := hfG (u (t m)) 1 h4 (by simpa using hδ)
    rw [one_smul] at this
    rw [this]; exact hucirc (t m)
  have hvle : v m 0 ^ 2 + v m 1 ^ 2 ≤ 1 := hv m
  rw [hfy, hfx, add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
    Real.norm_of_nonneg (hε m).le, Real.norm_eq_abs] at h1
  have hlow := neg_abs_le (v m 0 ^ 2 + v m 1 ^ 2 - 1 - ε m * f' Z)
  have hcz' : c * ‖Z‖ ≤ κ / 4 := by
    have : c * ‖Z‖ ≤ c * (‖z₀‖ + 1) := mul_le_mul_of_nonneg_left h6.le hc.le
    calc c * ‖Z‖ ≤ c * (‖z₀‖ + 1) := this
      _ = κ / 4 := by simp only [c]; field_simp
  have hεm := hε m
  nlinarith [mul_le_mul_of_nonneg_left hcz' hεm.le, mul_lt_mul_of_pos_left h5 hεm]

end HryniewiczCriterion

/-!
# Winding numbers of `C¹` loops in `ℂ \ {0}` via the logarithmic derivative
-/


noncomputable section

namespace WindA

/-- The log-derivative primitive recovers the loop: `c t = c 0 · exp (∫₀ᵗ c'/c)`. -/
lemma eq_mul_exp_integral {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (t : ℝ) :
    c t = c 0 * exp (∫ s in (0 : ℝ)..t, c' s / c s) := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, c' s / c s
  have hL : ∀ t, HasDerivAt L (c' t / c t) t := fun t =>
    (hq.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℂ := fun t => c t * exp (-L t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt g (c' t * exp (-L t) + c t * (exp (-L t) * -(c' t / c t))) t :=
      (hc t).mul (HasDerivAt.cexp (f := fun t => -L t) (hL t).neg)
    convert h1 using 1
    field_simp [hne t]
    ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  have hL0 : L 0 = 0 := by simp [L]
  have := hconst t
  simp only [g, hL0, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The log-derivative integral of a closed `C¹` loop lies in `2πi ℤ`. -/
lemma integral_mem_two_pi_I {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0) :
    ∃ k : ℤ, ∫ s in (0 : ℝ)..1, c' s / c s = k * (2 * Real.pi * I) := by
  have h := eq_mul_exp_integral hc hc' hne 1
  rw [hper] at h
  have h1 : exp (∫ s in (0 : ℝ)..1, c' s / c s) = 1 := by
    have h0 := hne 0
    exact mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm)
  exact Complex.exp_eq_one_iff.1 h1

lemma im_integral {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s).im = ∫ s in a..b, (f s).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm

/-- Homotopy invariance of the log-derivative integral. -/
lemma integral_eq_of_homotopy {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s)
    (hcF : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ univ))
    (hcF' : ContinuousOn (Function.uncurry F') (Icc 0 1 ×ˢ univ))
    (hne : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0)
    (hper : ∀ r ∈ Icc (0 : ℝ) 1, F r 1 = F r 0) :
    ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
  set p : ℝ → ℝ := fun r => (projIcc (0 : ℝ) 1 zero_le_one r : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ r, p r ∈ Icc (0 : ℝ) 1 := fun r => (projIcc (0 : ℝ) 1 zero_le_one r).2
  have hpid : ∀ r ∈ Icc (0 : ℝ) 1, p r = r := fun r hr => by simp [p, projIcc_of_mem _ hr]
  set G : ℝ → ℝ → ℂ := fun r s => F' (p r) s / F (p r) s
  have hmap : Continuous fun q : ℝ × ℝ => (p q.1, q.2) := (hp.comp continuous_fst).prodMk continuous_snd
  have hmapI : ∀ q : ℝ × ℝ, (p q.1, q.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
    fun q => ⟨hpI q.1, trivial⟩
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun q : ℝ × ℝ => Function.uncurry F' (p q.1, q.2) :=
      hcF'.comp_continuous hmap hmapI
    have h2 : Continuous fun q : ℝ × ℝ => Function.uncurry F (p q.1, q.2) :=
      hcF.comp_continuous hmap hmapI
    exact h1.div h2 fun q => hne _ (hpI q.1) q.2
  set W : ℝ → ℂ := fun r => ∫ s in (0 : ℝ)..1, G r s
  have hW : Continuous W := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc 0 1
  -- `W r ∈ 2πiℤ`
  have hk : ∀ r, ∃ k : ℤ, W r = k * (2 * Real.pi * I) := by
    intro r
    have hr := hpI r
    have hcont : Continuous (F' (p r)) := by
      have := hGc.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (r, s))
      have h1 : Continuous fun s : ℝ => Function.uncurry F' (p r, s) :=
        hcF'.comp_continuous (continuous_const.prodMk continuous_id) fun s => ⟨hr, trivial⟩
      exact h1
    exact integral_mem_two_pi_I (hF _ hr) hcont (hne _ hr) (hper _ hr)
  set f : ℝ → ℝ := fun r => (W r).im / (2 * Real.pi)
  have hf : Continuous f := (Complex.continuous_im.comp hW).div_const _
  have hfint : ∀ r, ∃ k : ℤ, f r = k := by
    intro r; obtain ⟨k, hk⟩ := hk r
    refine ⟨k, ?_⟩
    simp only [f, hk]
    simp [Complex.mul_im]
  have hWre : ∀ r, W r = (f r : ℂ) * (2 * Real.pi * I) := by
    intro r; obtain ⟨k, hk'⟩ := hk r
    have : f r = k := by
      simp only [f, hk']; simp [Complex.mul_im]
    rw [this, hk']; push_cast; ring
  -- `f` is constant on `[0, 1]`
  obtain ⟨k0, hk0⟩ := hfint 0
  obtain ⟨k1, hk1⟩ := hfint 1
  have hk01 : k0 = k1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have hmem : (k0 : ℝ) + 1 / 2 ∈ Icc (f 0) (f 1) := by
        rw [hk0, hk1]
        have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k0 = 1 / 2 := by linarith
      have h2 : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h3
      omega
    · have hmem : (k1 : ℝ) + 1 / 2 ∈ Icc (f 1) (f 0) := by
        rw [hk0, hk1]
        have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k1 = 1 / 2 := by linarith
      have h2 : ((k - k1 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k1 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k1) : ℤ) = 1 := by exact_mod_cast h3
      omega
  have hW1 : W 1 = W 0 := by rw [hWre 1, hWre 0, hk0, hk1, hk01]
  have e1 : W 1 = ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s := by
    simp only [W, G, hpid 1 ⟨zero_le_one, le_rfl⟩]
  have e0 : W 0 = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
    simp only [W, G, hpid 0 ⟨le_rfl, zero_le_one⟩]
  rw [← e1, ← e0, hW1]

/-- A closed loop whose argument strictly increases and which returns to the ray of
`c 0` only at the ends winds exactly once. -/
lemma integral_eq_two_pi_I_of_im_pos {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * I := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  obtain ⟨k, hk⟩ := integral_mem_two_pi_I hc hc' hne hper
  set θ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, c' s / c s).im
  have hθ : ∀ t, θ t = ∫ s in (0 : ℝ)..t, (c' s / c s).im := fun t => im_integral hq 0 t
  have hθc : Continuous θ := by
    have : θ = fun t => ∫ s in (0 : ℝ)..t, (c' s / c s).im := funext hθ
    rw [this]
    exact continuous_iff_continuousAt.2 fun t =>
      ((Complex.continuous_im.comp hq).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  have hθ1 : θ 1 = 2 * Real.pi * k := by
    simp only [θ, hk]; simp [Complex.mul_im]; ring
  have hθ1pos : 0 < θ 1 := by
    rw [hθ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_im.comp hq).intervalIntegrable 0 1) (fun t _ => hpos t) zero_lt_one
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      rw [hθ1] at hθ1pos
      have := Real.pi_pos
      nlinarith
    exact_mod_cast this
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
    have hθ0 : θ 0 = 0 := by simp [θ]
    have hmem : 2 * Real.pi ∈ Icc (θ 0) (θ 1) := by
      rw [hθ0, hθ1]
      have := Real.pi_pos
      constructor <;> nlinarith
    obtain ⟨t, ht, hθt⟩ := intermediate_value_Icc zero_le_one hθc.continuousOn hmem
    have ht0 : t ≠ 0 := by
      rintro rfl; rw [hθ0] at hθt; have := Real.pi_pos; linarith
    have ht1 : t ≠ 1 := by
      rintro rfl; rw [hθ1] at hθt; have := Real.pi_pos; nlinarith
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    set L := ∫ s in (0 : ℝ)..t, c' s / c s
    have hL : L = (L.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [θ] at hθt ⊢
      first | exact hθt | exact hθt.symm
    have hct := eq_mul_exp_integral hc hc' hne t
    apply hray t htI (Real.exp L.re) (Real.exp_pos _)
    have h2 : exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      push_cast; exact Complex.exp_two_pi_mul_I
    have hE : exp L = (Real.exp L.re : ℂ) := by
      conv_lhs => rw [hL]
      rw [Complex.exp_add, h2, mul_one, Complex.ofReal_exp]
    rw [hct, hE]; ring
  rw [hk, hk1]; simp

end WindA

namespace HryniewiczCriterion

/-- `e i` is the `i`-th standard basis vector of `ℝ⁴`. -/
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith

lemma liouvilleForm_eq (x v : R4) : liouvilleForm x v = omega0 x v / 2 := by
  simp [liouvilleForm, omega0]

lemma omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma omega0_smul_smul (u v : R4) (p q : ℝ) : omega0 (p • u) (q • v) = p * q * omega0 u v := by
  simp [omega0]; ring

/-- A symplectic pair `Z₁, Z₂` together with an `ω₀`-orthogonal symplectic pair `a, b`
spans `ℝ⁴`; every `v` that is `ω₀`-orthogonal to `a, b` lies in `span (Z₁, Z₂)`. -/
lemma eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [omega0_self, h12, h1a, h1b] at e1
    rw [omega0_antisymm Z₂ Z₁, h12, omega0_self, h2a, h2b] at e2
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, h1a, h2a, omega0_self] at e3
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, h1b, h2b,
      omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  -- pair with `a` and `b` to kill the last two coefficients
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, omega0_antisymm a b, omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, omega0_self]; ring
  rw [h1a, h2a, omega0_self, omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, omega0_lin_left, omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, omega0_antisymm, omega0_lin_left, omega0_self, omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

/-- In the situation of `eq_frame_of_omega0`, `ω₀` on two such vectors is the
determinant of their `(Z₁, Z₂)`-coordinates. -/
lemma omega0_eq_det_of_frame (Z₁ Z₂ a b v w : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0)
    (hwa : omega0 w a = 0) (hwb : omega0 w b = 0) :
    omega0 v w = omega0 v Z₂ * omega0 Z₁ w - omega0 w Z₂ * omega0 Z₁ v := by
  have hv := eq_frame_of_omega0 Z₁ Z₂ a b v h12 h1a h1b h2a h2b hab hva hvb
  have hw := eq_frame_of_omega0 Z₁ Z₂ a b w h12 h1a h1b h2a h2b hab hwa hwb
  set p := omega0 v Z₂; set q := omega0 Z₁ v
  set r := omega0 w Z₂; set s := omega0 Z₁ w
  rw [hv, hw]
  simp only [omega0] at h12 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (p * s - r * q) * h12

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

lemma contDiff_fderiv_of_smooth (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (fderiv ℝ H) :=
  hH.fderiv_right le_rfl

lemma contDiff_fderiv2_of_smooth (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ H)) :=
  (contDiff_fderiv_of_smooth hH).fderiv_right le_rfl

lemma hasFDerivAt_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    HasFDerivAt (hamiltonianVectorField H) (jvec.comp (fderiv ℝ (fderiv ℝ H) y)) y := by
  rw [hamiltonianVectorField_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
    (contDiff_fderiv_of_smooth hH).differentiable (by simp) y
  exact jvec.hasFDerivAt.comp y hd.hasFDerivAt

lemma fderiv_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    fderiv ℝ (hamiltonianVectorField H) y = jvec.comp (fderiv ℝ (fderiv ℝ H) y) :=
  (hasFDerivAt_hvf hH y).fderiv

lemma D2_symm (hH : ContDiff ℝ ∞ H) (y v w : R4) :
    fderiv ℝ (fderiv ℝ H) y v w = fderiv ℝ (fderiv ℝ H) y w v :=
  hH.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) v w

lemma contDiff_hvf (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamiltonianVectorField H) := by
  rw [hamiltonianVectorField_eq]
  exact jvec.contDiff.comp (contDiff_fderiv_of_smooth hH)

/-- Bootstrapping: a solution of `f' = g` with `g` as smooth as `f` is `C^∞`. -/
lemma contDiff_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ n : ℕ, ContDiff ℝ n f → ContDiff ℝ n g) : ContDiff ℝ ∞ f := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hf t).continuousAt)
  | succ n ih =>
    have hd : deriv f = g := funext fun t => (hf t).deriv
    have h := contDiff_succ_iff_deriv (𝕜 := ℝ) (f := f) (n := (n : ℕ∞ω))
    push_cast
    refine h.2 ⟨fun t => (hf t).differentiableAt, by simp, ?_⟩
    rw [hd]; exact hg n ih

lemma trajectory_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x) :
    ContDiff ℝ ∞ x :=
  contDiff_of_hasDerivAt hx.1 fun n hn =>
    ((contDiff_hvf hH).of_le (by exact_mod_cast le_top)).comp hn

lemma linearizedFlow_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) : ContDiff ℝ ∞ Y := by
  refine contDiff_of_hasDerivAt hY.2 fun n hn => ?_
  have hA : ContDiff ℝ ∞ fun t => fderiv ℝ (hamiltonianVectorField H) (x t) := by
    simp_rw [fderiv_hvf hH]
    exact contDiff_const.clm_comp
      ((contDiff_fderiv2_of_smooth hH).comp (trajectory_contDiff hH hx))
  exact (hA.of_le (by exact_mod_cast le_top)).clm_comp hn

lemma linearizedFlow_hasDerivAt (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u : R4) (t : ℝ) :
    HasDerivAt (fun t => Y t u) (jvec (fderiv ℝ (fderiv ℝ H) (x t) (Y t u))) t := by
  have h := (hY.2 t).clm_apply (hasDerivAt_const t u)
  simpa [fderiv_hvf hH] using h

/-- The linearized Hamiltonian flow is symplectic. -/
lemma omega0_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u v : R4) (t : ℝ) :
    omega0 (Y t u) (Y t v) = omega0 u v := by
  set g : ℝ → ℝ := fun t => omega0 (Y t u) (Y t v) with hg
  have hder : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY u s) i
    have k := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY v s) i
    have key := ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
      ((h 3).mul (k 2))
    have hval : omega0 (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s u))) (Y s v) +
        omega0 (Y s u) (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s v))) = 0 := by
      rw [omega0_jvec_left, omega0_jvec_right, D2_symm hH]; ring
    have key2 := key.congr_of_eventuallyEq (f₁ := g)
      (Filter.Eventually.of_forall fun r => by simp [hg, omega0])
    exact key2.congr_deriv (by rw [← hval]; simp only [omega0]; ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hg] at hc
  rw [hc, hY.1]; rfl

/-- The linearized flow preserves `dH`: it maps `T_{x(0)} S` to `T_{x(t)} S`. -/
lemma dH_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v := by
  set f : ℝ → ℝ := fun t => fderiv ℝ H (x t) (Y t v) with hf
  have hder : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hd : DifferentiableAt ℝ (fderiv ℝ H) (x s) :=
      (contDiff_fderiv_of_smooth hH).differentiable (by simp) (x s)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt s (hx.1 s)
    have h2 := h1.clm_apply (linearizedFlow_hasDerivAt hH hY v s)
    refine h2.congr_deriv ?_
    rw [hamiltonianVectorField_eq, Function.comp_apply]
    rw [D2_symm hH, add_comm]
    exact apply_jvec_add _ _
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hf] at hc
  rw [hc, hY.1]; rfl

end HryniewiczCriterion

/-!
# Smooth polar lifts of loops, Fubini for continuous integrands, and the action identity
-/


noncomputable section

namespace WindA

/-- Fubini on `[0,1]²` for a continuous integrand. -/
lemma integral_integral_swap_unit {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f x y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- A smooth closed loop in `ℂ \ {0}` with winding number one has a smooth polar form
`c = r e^{iθ}` with `r > 0` periodic and `θ(s + 1) = θ(s) + 2π`. -/
lemma exists_polar_of_winding_one {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hne : ∀ s, c s ≠ 0)
    (hper : ∀ s, c (s + 1) = c s)
    (hW : ∫ s in (0 : ℝ)..1, deriv c s / c s = 2 * Real.pi * I) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧
      (∀ s, r (s + 1) = r s) ∧ (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
  have hd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by simp)) t).hasDerivAt
  have hdc : ContDiff ℝ ∞ (deriv c) := hc.iterate_deriv 1
  have hq : ContDiff ℝ ∞ fun s => deriv c s / c s := by
    simp only [div_eq_mul_inv]; exact hdc.mul (hc.inv hne)
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, deriv c s / c s
  have hL : ∀ t, HasDerivAt L (deriv c t / c t) t := fun t =>
    (hq.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hLs : ContDiff ℝ ∞ L :=
    HryniewiczCriterion.contDiff_of_hasDerivAt hL fun n _ => hq.of_le (by exact_mod_cast le_top)
  have hexp := eq_mul_exp_integral hd hdc.continuous hne
  set r : ℝ → ℝ := fun s => ‖c 0‖ * Real.exp (L s).re
  set θ : ℝ → ℝ := fun s => arg (c 0) + (L s).im
  have hexp' : ∀ t, c t = c 0 * exp (L t) := hexp
  have hpolar : ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
    intro s
    have e1 : exp (L s) = (Real.exp (L s).re : ℂ) * exp (((L s).im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im (L s)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    have e2 := norm_mul_exp_arg_mul_I (c 0)
    rw [← Complex.exp_ofReal_mul_I, hexp' s, e1]
    conv_lhs => rw [← e2]
    simp only [r, θ]
    push_cast
    rw [show ((arg (c 0) : ℂ) + ((L s).im : ℂ)) * I = (arg (c 0) : ℂ) * I + ((L s).im : ℂ) * I by ring,
      Complex.exp_add]
    ring
  have hrpos : ∀ s, 0 < r s := fun s => mul_pos (norm_pos_iff.2 (hne 0)) (Real.exp_pos _)
  have hnorm : ∀ s, ‖c s‖ = r s := by
    intro s
    rw [hpolar s, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hrpos s).le,
      ← Complex.exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hqper : Function.Periodic (fun s => deriv c s / c s) 1 := by
    intro s
    have : deriv c (s + 1) = deriv c s := by
      have h1 : (fun t => c (t + 1)) = c := funext hper
      have := deriv_comp_add_const (f := c) (a := 1) (x := s)
      rw [h1] at this; exact this.symm
    simp only [this, hper]
  have hLper : ∀ s, L (s + 1) = L s + 2 * Real.pi * I := by
    intro s
    have := hqper.intervalIntegral_add_eq_add 0 s (fun a b => hq.continuous.intervalIntegrable a b)
    simp only [zero_add] at this
    simp only [L]; rw [this, hW]
  refine ⟨r, θ, ?_, ?_, hrpos, ?_, ?_, hpolar⟩
  · exact contDiff_const.mul (Real.contDiff_exp.comp (Complex.reCLM.contDiff.comp hLs))
  · exact contDiff_const.add (Complex.imCLM.contDiff.comp hLs)
  · intro s; rw [← hnorm, ← hnorm, hper]
  · intro s; simp only [θ, hLper]; simp; ring

end WindA

/-!
# The action identity `∫_{∂D} ω₀(c, ∂ₛc) = 2 ∬ ω₀(∂ᵣc, ∂ₛc)` for a family of loops
-/


noncomputable section

namespace HryniewiczCriterion

lemma hasDerivAt_omega0 {f g : ℝ → R4} {f' g' : R4} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun t => omega0 (f t) (g t)) (omega0 f' (g t) + omega0 (f t) g') t := by
  have hfi := fun i => (hasDerivAt_pi.1 hf) i
  have hgi := fun i => (hasDerivAt_pi.1 hg) i
  have h := ((((hfi 0).mul (hgi 1)).sub ((hfi 1).mul (hgi 0))).add ((hfi 2).mul (hgi 3))).sub
    ((hfi 3).mul (hgi 2))
  convert h using 1 <;> first | rfl | (simp only [omega0]; ring) | (funext t; simp only [omega0]) | skip

lemma continuous_omega0 {X : Type*} [TopologicalSpace X] {f g : X → R4} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => omega0 (f x) (g x) := by
  have hfi := fun i => (continuous_apply i).comp hf
  have hgi := fun i => (continuous_apply i).comp hg
  simp only [omega0]
  exact ((((hfi 0).mul (hgi 1)).sub ((hfi 1).mul (hgi 0))).add ((hfi 2).mul (hgi 3))).sub
    ((hfi 3).mul (hgi 2))

/-- The action identity for a smooth family of loops `c r` (`r ∈ [0,1]`), closed in `s`,
starting from a constant loop. -/
theorem action_identity {c : ℝ → ℝ → R4} (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hper : ∀ r, c r 1 = c r 0) (h0 : ∀ s, c 0 s = c 0 0) :
    ∫ s in (0 : ℝ)..1, omega0 (c 1 s) (fderiv ℝ (Function.uncurry c) (1, s) (0, 1)) =
      2 * ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        omega0 (fderiv ℝ (Function.uncurry c) (r, s) (1, 0))
          (fderiv ℝ (Function.uncurry c) (r, s) (0, 1)) := by
  set Φ := Function.uncurry c with hΦ
  set D := fderiv ℝ Φ
  set D2 := fderiv ℝ D
  have hD : ContDiff ℝ ∞ D := hc.fderiv_right le_rfl
  have hD2 : ContDiff ℝ ∞ D2 := hD.fderiv_right le_rfl
  have hΦd : ∀ p, HasFDerivAt Φ (D p) p := fun p => ((hc.differentiable (by simp)) p).hasFDerivAt
  have hDd : ∀ p, HasFDerivAt D (D2 p) p := fun p => ((hD.differentiable (by simp)) p).hasFDerivAt
  have hsymm : ∀ p v w, D2 p v w = D2 p w v := fun p v w =>
    hc.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) v w
  set e1 : ℝ × ℝ := (1, 0)
  set e2 : ℝ × ℝ := (0, 1)
  have lr : ∀ r s : ℝ, HasDerivAt (fun r => ((r, s) : ℝ × ℝ)) e1 r := fun r s =>
    (hasDerivAt_id r).prodMk (hasDerivAt_const r s)
  have ls : ∀ r s : ℝ, HasDerivAt (fun s => ((r, s) : ℝ × ℝ)) e2 s := fun r s =>
    (hasDerivAt_const s r).prodMk (hasDerivAt_id s)
  have cr : ∀ r s, HasDerivAt (fun r => c r s) (D (r, s) e1) r := fun r s =>
    HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun r => ((r, s) : ℝ × ℝ)) r (hΦd (r, s)) (lr r s)
  have cs : ∀ r s, HasDerivAt (fun s => c r s) (D (r, s) e2) s := fun r s =>
    HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun s => ((r, s) : ℝ × ℝ)) s (hΦd (r, s)) (ls r s)
  have Dr : ∀ r s v, HasDerivAt (fun r => D (r, s) v) (D2 (r, s) e1 v) r := fun r s v =>
    (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt r
      (HasFDerivAt.comp_hasDerivAt (l := D) (f := fun r => ((r, s) : ℝ × ℝ)) r (hDd (r, s)) (lr r s))
  have Ds : ∀ r s v, HasDerivAt (fun s => D (r, s) v) (D2 (r, s) e2 v) s := fun r s v =>
    (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt s
      (HasFDerivAt.comp_hasDerivAt (l := D) (f := fun s => ((r, s) : ℝ × ℝ)) s (hDd (r, s)) (ls r s))
  -- continuity
  have hcc : Continuous Φ := hc.continuous
  have hDv : ∀ v, Continuous fun p => D p v := fun v => hD.continuous.clm_apply continuous_const
  have hD2v : ∀ v w, Continuous fun p => D2 p v w := fun v w =>
    (hD2.continuous.clm_apply continuous_const).clm_apply continuous_const
  set A : ℝ → ℝ → ℝ := fun r s => omega0 (D (r, s) e1) (D (r, s) e2)
  set B : ℝ → ℝ → ℝ := fun r s => omega0 (c r s) (D2 (r, s) e1 e2)
  have hA : Continuous (Function.uncurry A) := continuous_omega0 (hDv e1) (hDv e2)
  have hB : Continuous (Function.uncurry B) := continuous_omega0 hcc (hD2v e1 e2)
  have hAr : ∀ s, Continuous fun r => A r s := fun s =>
    hA.comp (continuous_id.prodMk continuous_const)
  have hBr : ∀ s, Continuous fun r => B r s := fun s =>
    hB.comp (continuous_id.prodMk continuous_const)
  have hAs : ∀ r, Continuous fun s => A r s := fun r =>
    hA.comp (continuous_const.prodMk continuous_id)
  have hBs : ∀ r, Continuous fun s => B r s := fun r =>
    hB.comp (continuous_const.prodMk continuous_id)
  -- slices in `r`
  have hDe2zero : ∀ s, D (0, s) e2 = 0 := by
    intro s
    have h := cs 0 s
    have hconst : (fun s => c 0 s) = fun _ => c 0 0 := funext h0
    rw [hconst] at h
    exact h.unique (hasDerivAt_const s _)
  have I1 : ∀ s, ∫ r in (0 : ℝ)..1, (A r s + B r s) = omega0 (c 1 s) (D (1, s) e2) := by
    intro s
    have hder : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => omega0 (c r s) (D (r, s) e2))
        (A r s + B r s) r := fun r _ => hasDerivAt_omega0 (cr r s) (Dr r s e2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((hAr s).add (hBr s)).intervalIntegrable 0 1), hDe2zero]
    simp [omega0]
  have hDe1per : ∀ r, D (r, 1) e1 = D (r, 0) e1 := by
    intro r
    have h1 := cr r 1
    have hfun : (fun r => c r 1) = fun r => c r 0 := funext hper
    rw [hfun] at h1
    exact h1.unique (cr r 0)
  have I2 : ∀ r, ∫ s in (0 : ℝ)..1, (-A r s + B r s) = 0 := by
    intro r
    have hder : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => omega0 (c r s) (D (r, s) e1))
        (-A r s + B r s) s := by
      intro s _
      have h := hasDerivAt_omega0 (cs r s) (Ds r s e1)
      convert h using 1
      simp only [A, B, hsymm (r, s) e2 e1, omega0_antisymm (D (r, s) e2)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((hAs r).neg.add (hBs r)).intervalIntegrable 0 1), hper, hDe1per, sub_self]
  -- Fubini
  have hswap := WindA.integral_integral_swap_unit (f := fun r s => -A r s + B r s)
    ((hA.neg).add hB)
  simp only [I2, intervalIntegral.integral_zero] at hswap
  have hpar : ∀ {F : ℝ → ℝ → ℝ}, Continuous (Function.uncurry F) →
      Continuous fun s => ∫ r in (0 : ℝ)..1, F r s := by
    intro F hF
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s r => F r s) (hF.comp continuous_swap) 0 1
  have key : ∀ s, (∫ r in (0 : ℝ)..1, (A r s + B r s)) - ∫ r in (0 : ℝ)..1, (-A r s + B r s) =
      2 * ∫ r in (0 : ℝ)..1, A r s := by
    intro s
    have h := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := 1)
      (f := fun r => A r s + B r s) (g := fun r => -A r s + B r s)
      (((hAr s).add (hBr s)).intervalIntegrable 0 1) (((hAr s).neg.add (hBr s)).intervalIntegrable 0 1)
    refine h.symm.trans ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r; ring
  calc ∫ s in (0 : ℝ)..1, omega0 (c 1 s) (D (1, s) e2)
      = ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (A r s + B r s) := by simp only [I1]
    _ = (∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (A r s + B r s)) -
          ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (-A r s + B r s) := by rw [← hswap, sub_zero]
    _ = ∫ s in (0 : ℝ)..1, ((∫ r in (0 : ℝ)..1, (A r s + B r s)) -
          ∫ r in (0 : ℝ)..1, (-A r s + B r s)) := by
        exact (intervalIntegral.integral_sub
          ((hpar (F := fun r s => A r s + B r s) (hA.add hB)).intervalIntegrable 0 1)
          ((hpar (F := fun r s => -A r s + B r s) (hA.neg.add hB)).intervalIntegrable 0 1)).symm
    _ = ∫ s in (0 : ℝ)..1, 2 * ∫ r in (0 : ℝ)..1, A r s := by simp only [key]
    _ = _ := by rw [intervalIntegral.integral_const_mul]

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Pointwise frame identities -/

lemma ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push Not at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := dot4_pos (ne_zero_of_dH_pos hy)
  have hn := euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, omega0_smul_smul, omega0_raw21, ← hn]
  field_simp

lemma omega0_xiFrame_y {y : R4} (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) y = 0 := by
  rw [omega0_antisymm]
  simp only [omega0] at *
  have := omega0_xiFrameRaw_self (H := H) Q hQ y
  simp only [omega0] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(euclidNorm y)⁻¹) * this

lemma omega0_xiFrame_X {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, hamiltonianVectorField_eq]
  simp only
  rw [omega0_jvec_left, map_smul, dH_xiFrameRaw hy]; simp

lemma omega0_y_X (y : R4) : omega0 y (hamiltonianVectorField H y) = fderiv ℝ H y y := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_right _ _

lemma liouville_X (y : R4) :
    liouvilleForm y (hamiltonianVectorField H y) = fderiv ℝ H y y / 2 := by
  rw [liouvilleForm_eq, omega0_y_X]

/-! ### The Reeb projection -/

lemma omega0_reeb_y {y : R4} (hy : 0 < fderiv ℝ H y y) (w : R4) :
    omega0 (reebProjection H y w) y = 0 := by
  have hl : liouvilleForm y (hamiltonianVectorField H y) ≠ 0 := by
    rw [liouville_X]; positivity
  have hlin : ∀ (u X : R4) (c : ℝ), liouvilleForm y (u - c • X) =
      liouvilleForm y u - c * liouvilleForm y X := by
    intro u X c; simp [liouvilleForm]; ring
  have : liouvilleForm y (reebProjection H y w) = 0 := by
    rw [reebProjection, hlin, div_mul_cancel₀ _ hl, sub_self]
  rw [omega0_antisymm, liouvilleForm_eq] at *
  linarith

lemma dH_reeb (y w : R4) :
    fderiv ℝ H y (reebProjection H y w) = fderiv ℝ H y w := by
  rw [reebProjection, map_sub, map_smul, hamiltonianVectorField_eq]
  simp [apply_jvec_self]

lemma omega0_X_left (y w : R4) :
    omega0 (hamiltonianVectorField H y) w = -fderiv ℝ H y w := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_left _ _

lemma omega0_reeb_X (y w : R4) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y w) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, omega0_X_left, dH_reeb, hw]; simp

lemma omega0_reeb_reeb (y v w : R4) (hv : fderiv ℝ H y v = 0) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y v) (reebProjection H y w) = omega0 v w := by
  have h1 := omega0_X_left (H := H) y v
  have h2 := omega0_X_left (H := H) y w
  rw [hv] at h1; rw [hw] at h2
  set X := hamiltonianVectorField H y
  set a := liouvilleForm y v / liouvilleForm y X
  set b := liouvilleForm y w / liouvilleForm y X
  have hXX := omega0_self X
  have e : omega0 (v - a • X) (w - b • X) =
      omega0 v w - b * omega0 v X - a * omega0 X w + a * b * omega0 X X := by
    simp [omega0]; ring
  rw [reebProjection, reebProjection, e, h2, hXX, omega0_antisymm v X, h1]; ring

/-! ### Smoothness -/

lemma cd_omega0 {p q : ℝ → R4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun τ => omega0 (p τ) (q τ)) := by
  have h := fun i => contDiff_pi.1 hp i
  have k := fun i => contDiff_pi.1 hq i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))

lemma cd_dH (hH : ContDiff ℝ ∞ H) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((contDiff_fderiv_of_smooth hH).comp hc).clm_apply hv

lemma cd_quatQ1 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ1 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma cd_quatQ2 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ2 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

lemma cd_xiFrame (hH : ContDiff ℝ ∞ H) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((cd_dH hH hc hQ).div (cd_dH hH hc hc) fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (dot4_pos (ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

lemma cd_reeb (hH : ContDiff ℝ ∞ H) {c w : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun τ => reebProjection H (c τ) (w τ)) := by
  have hX : ContDiff ℝ ∞ (fun τ => hamiltonianVectorField H (c τ)) :=
    (contDiff_hvf hH).comp hc
  have hl1 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (w τ)) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hw).div_const 2
  have hl2 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (hamiltonianVectorField H (c τ))) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hX).div_const 2
  have hne : ∀ τ, liouvilleForm (c τ) (hamiltonianVectorField H (c τ)) ≠ 0 := fun τ => by
    rw [liouville_X]; exact (half_pos (hpos τ)).ne'
  exact hw.sub ((hl1.div hl2 hne).smul hX)

/-! ### Assembly -/

theorem linearizedXiPath_isSymplecticPath' (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath H P Y t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath H P Y t).det = 1) ∧
      linearizedXiPath H P Y 0 = 1 := by
  have hH := hS.1
  have hpos : ∀ t, 0 < fderiv ℝ H (P.x t) (P.x t) := fun t =>
    hS.2.2 _ (P.trajectory.2 t)
  have hx := trajectory_contDiff hH P.trajectory
  have hYc := linearizedFlow_contDiff hH P.trajectory hY
  have hx0 : 0 < fderiv ℝ H (P.x 0) (P.x 0) := hpos 0
  set E : Fin 2 → R4 := ![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] with hE
  -- frame facts at (P.x 0)
  have hE0 : ∀ j, fderiv ℝ H (P.x 0) (E j) = 0 := by
    intro j; fin_cases j <;> simp [hE, xiFrame1, xiFrame2, map_smul, dH_xiFrameRaw hx0]
  have hEl : ∀ j, liouvilleForm (P.x 0) (E j) = 0 := by
    intro j
    rw [liouvilleForm_eq, omega0_antisymm]
    fin_cases j
    · simp [hE, xiFrame1, omega0_xiFrame_y quatQ2 omega0_quatQ2]
    · simp [hE, xiFrame2, omega0_xiFrame_y quatQ1 omega0_quatQ1]
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    have hc : ContDiff ℝ ∞ (fun τ => P.x (P.T * τ)) := hx.comp (contDiff_const.mul contDiff_id)
    have hcpos : ∀ τ, 0 < fderiv ℝ H (P.x (P.T * τ)) (P.x (P.T * τ)) := fun τ => hpos _
    refine ContDiff.contDiffOn (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
    have hw : ContDiff ℝ ∞ (fun τ => Y (P.T * τ) (E j)) :=
      (hYc.comp (contDiff_const.mul contDiff_id)).clm_apply contDiff_const
    have hr := cd_reeb hH hc hcpos hw
    have hZ1 := cd_xiFrame hH hc hcpos quatQ2 (cd_quatQ2 hc)
    have hZ2 := cd_xiFrame hH hc hcpos quatQ1 (cd_quatQ1 hc)
    fin_cases i
    · simpa [linearizedXiPath, xiCoords, xiFrame2, hE] using cd_omega0 hr hZ2
    · simpa [linearizedXiPath, xiCoords, xiFrame1, hE] using cd_omega0 hZ1 hr
  · -- determinant
    intro τ _
    set y := P.x (P.T * τ)
    have hy := hpos (P.T * τ)
    set w : Fin 2 → R4 := fun j => Y (P.T * τ) (E j)
    have hw : ∀ j, fderiv ℝ H y (w j) = 0 := fun j => by
      simp only [w, y]; rw [dH_linearizedFlow hH P.trajectory hY, hE0]
    set r : Fin 2 → R4 := fun j => reebProjection H y (w j)
    have hdet := omega0_eq_det_of_frame (xiFrame1 H y) (xiFrame2 H y) y
      (hamiltonianVectorField H y) (r 0) (r 1) (omega0_xiFrame12 hy)
      (omega0_xiFrame_y quatQ2 omega0_quatQ2) (omega0_xiFrame_X hy quatQ2)
      (omega0_xiFrame_y quatQ1 omega0_quatQ1) (omega0_xiFrame_X hy quatQ1)
      (by rw [omega0_y_X]; exact hy.ne')
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 0))
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 1))
    have hrr : omega0 (r 0) (r 1) = 1 := by
      simp only [r]
      rw [omega0_reeb_reeb y _ _ (hw 0) (hw 1)]
      simp only [w]
      rw [omega0_linearizedFlow hH hY]
      simp [hE, omega0_xiFrame12 hx0]
    have hm : linearizedXiPath H P Y τ = Matrix.of
        ![![omega0 (r 0) (xiFrame2 H y), omega0 (r 1) (xiFrame2 H y)],
          ![omega0 (xiFrame1 H y) (r 0), omega0 (xiFrame1 H y) (r 1)]] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm, Matrix.det_fin_two_of]
    linarith [hdet, hrr]
  · -- initial value
    have hr : ∀ j, reebProjection H (P.x 0) (Y 0 (E j)) = E j := by
      intro j
      rw [hY.1]
      simp [reebProjection, hEl j]
    ext i j
    simp only [linearizedXiPath, Matrix.of_apply, mul_zero]
    rw [hr j]
    fin_cases i <;> fin_cases j <;>
      simp [xiCoords, hE, omega0_xiFrame12 hx0, omega0_self, Matrix.one_apply,
        omega0_antisymm (xiFrame2 H (P.x 0)) (xiFrame1 H (P.x 0))]

end HryniewiczCriterion

/-!
# Complex `ξ`-coordinates of the Reeb projection
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-- The `(Z₁, Z₂)`-coordinates of the Reeb projection of `w` at `x`, as a complex number. -/
def xiPsi (H : R4 → ℝ) (x w : R4) : ℂ :=
  ⟨omega0 (reebProjection H x w) (xiFrame2 H x), omega0 (xiFrame1 H x) (reebProjection H x w)⟩

lemma reebProjection_eq_xiPsi {x w : R4} (hx : 0 < fderiv ℝ H x x) (hw : fderiv ℝ H x w = 0) :
    reebProjection H x w = (xiPsi H x w).re • xiFrame1 H x + (xiPsi H x w).im • xiFrame2 H x := by
  have h12 := omega0_xiFrame12 hx
  have h1a : omega0 (xiFrame1 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ2 omega0_quatQ2
  have h2a : omega0 (xiFrame2 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ1 omega0_quatQ1
  have h1b : omega0 (xiFrame1 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ2
  have h2b : omega0 (xiFrame2 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ1
  have hab : omega0 x (hamiltonianVectorField H x) ≠ 0 := by rw [omega0_y_X]; exact hx.ne'
  exact eq_frame_of_omega0 _ _ _ _ _ h12 h1a h1b h2a h2b hab (omega0_reeb_y hx w)
    (omega0_reeb_X x w hw)

lemma xiPsi_im_conj_mul {x v w : R4} (hx : 0 < fderiv ℝ H x x) (hv : fderiv ℝ H x v = 0)
    (hw : fderiv ℝ H x w = 0) :
    ((starRingEnd ℂ) (xiPsi H x v) * xiPsi H x w).im = omega0 v w := by
  have h12 := omega0_xiFrame12 hx
  have h1a : omega0 (xiFrame1 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ2 omega0_quatQ2
  have h2a : omega0 (xiFrame2 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ1 omega0_quatQ1
  have h1b : omega0 (xiFrame1 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ2
  have h2b : omega0 (xiFrame2 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ1
  have hab : omega0 x (hamiltonianVectorField H x) ≠ 0 := by rw [omega0_y_X]; exact hx.ne'
  have := omega0_eq_det_of_frame _ _ _ _ _ _ h12 h1a h1b h2a h2b hab (omega0_reeb_y hx v)
    (omega0_reeb_X x v hv) (omega0_reeb_y hx w) (omega0_reeb_X x w hw)
  rw [omega0_reeb_reeb x v w hv hw] at this
  rw [this]
  simp [xiPsi, Complex.mul_im]
  ring

lemma xiPsi_add_smul (x p q : R4) (a b : ℝ) :
    xiPsi H x (a • p + b • q) = (a : ℂ) * xiPsi H x p + (b : ℂ) * xiPsi H x q := by
  apply Complex.ext <;>
  · simp [xiPsi, reebProjection, liouvilleForm, omega0]
    ring

lemma xiPsi_zero (x : R4) : xiPsi H x 0 = 0 := by
  apply Complex.ext <;> simp [xiPsi, reebProjection, liouvilleForm, omega0]

/-! ### Smoothness -/

lemma contDiffAt_omega0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → R4}
    {p : E} (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ContDiffAt ℝ ∞ (fun q => omega0 (f q) (g q)) p := by
  have h := fun i => contDiffAt_pi.1 hf i
  have k := fun i => contDiffAt_pi.1 hg i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub ((h 3).mul (k 2))

lemma contDiff_dot4 : ContDiff ℝ ∞ (fun x : R4 => dot4 x x) := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  simp only [dot4, Fin.sum_univ_four]
  exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add ((h 3).mul (h 3))

lemma contDiffAt_xiFrame (hH : ContDiff ℝ ∞ H) {x : R4} (hx : 0 < fderiv ℝ H x x) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ Q) :
    ContDiffAt ℝ ∞ (fun y => (euclidNorm y)⁻¹ • xiFrameRaw H Q y) x := by
  have hdH := contDiff_fderiv_of_smooth hH
  have hraw : ContDiffAt ℝ ∞ (fun y => xiFrameRaw H Q y) x := by
    have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ H y (Q y)) := hdH.clm_apply hQ
    have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ H y y) := hdH.clm_apply contDiff_id
    exact hQ.contDiffAt.sub ((h1.contDiffAt.div h2.contDiffAt hx.ne').smul contDiffAt_id)
  have hdne : dot4 x x ≠ 0 := (dot4_pos (ne_zero_of_dH_pos hx)).ne'
  have hnorm : ContDiffAt ℝ ∞ (fun y => euclidNorm y) x := contDiff_dot4.contDiffAt.sqrt hdne
  have hnne : euclidNorm x ≠ 0 := fun h => by
    have := euclidNorm_sq x; rw [h] at this; exact hdne (by linarith)
  exact (hnorm.inv hnne).smul hraw

lemma contDiff_quatQ1 : ContDiff ℝ ∞ quatQ1 := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma contDiff_quatQ2 : ContDiff ℝ ∞ quatQ2 := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

/-- `xiPsi` is smooth in `(x, w)` wherever `dH(x) x > 0`. -/
lemma contDiffAt_xiPsi (hH : ContDiff ℝ ∞ H) {x w : R4} (hx : 0 < fderiv ℝ H x x) :
    ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiPsi H p.1 p.2) (x, w) := by
  have hfst : ContDiffAt ℝ ∞ (fun p : R4 × R4 => p.1) (x, w) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ ∞ (fun p : R4 × R4 => p.2) (x, w) := contDiffAt_snd
  have hZ1 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiFrame1 H p.1) (x, w) :=
    ContDiffAt.comp (g := fun y => (euclidNorm y)⁻¹ • xiFrameRaw H quatQ2 y) (x, w)
      (contDiffAt_xiFrame hH hx quatQ2 contDiff_quatQ2) hfst
  have hZ2 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiFrame2 H p.1) (x, w) :=
    ContDiffAt.comp (g := fun y => (euclidNorm y)⁻¹ • xiFrameRaw H quatQ1 y) (x, w)
      (contDiffAt_xiFrame hH hx quatQ1 contDiff_quatQ1) hfst
  have hX : ContDiffAt ℝ ∞ (fun p : R4 × R4 => hamiltonianVectorField H p.1) (x, w) :=
    (contDiff_hvf hH).contDiffAt.comp (x, w) hfst
  have hl1 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => liouvilleForm p.1 p.2) (x, w) := by
    simp only [liouvilleForm_eq]; exact (contDiffAt_omega0 hfst hsnd).div_const 2
  have hl2 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => liouvilleForm p.1 (hamiltonianVectorField H p.1))
      (x, w) := by
    simp only [liouvilleForm_eq]; exact (contDiffAt_omega0 hfst hX).div_const 2
  have hne : liouvilleForm x (hamiltonianVectorField H x) ≠ 0 := by
    rw [liouville_X]; exact (half_pos hx).ne'
  have hR : ContDiffAt ℝ ∞ (fun p : R4 × R4 => reebProjection H p.1 p.2) (x, w) :=
    hsnd.sub ((hl1.div hl2 hne).smul hX)
  have ha := contDiffAt_omega0 hR hZ2
  have hb := contDiffAt_omega0 hZ1 hR
  have hc : ContDiffAt ℝ ∞ (fun p : R4 × R4 =>
      (omega0 (reebProjection H p.1 p.2) (xiFrame2 H p.1) : ℂ) +
        (omega0 (xiFrame1 H p.1) (reebProjection H p.1 p.2) : ℂ) * I) (x, w) :=
    (ofRealCLM.contDiff.contDiffAt.comp (x, w) ha).add
      ((ofRealCLM.contDiff.contDiffAt.comp (x, w) hb).mul contDiffAt_const)
  convert hc using 1
  funext p
  apply Complex.ext <;> simp [xiPsi]

end HryniewiczCriterion

/-!
# The disk: tangency, interior non-vanishing of `ξ`-coordinates, sign of `ω₀|D`
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ} {e : Plane → R4}

lemma smul_mem_openUnitDisk {v : Plane} (hv : v ∈ closedUnitDisk) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    t • v ∈ openUnitDisk := by
  simp only [closedUnitDisk, openUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  have h0 := ht.1; have h1 := ht.2
  have : t ^ 2 < 1 := by nlinarith
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma smul_mem_openUnitDisk' {v : Plane} (hv : v ∈ openUnitDisk) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • v ∈ openUnitDisk := by
  simp only [openUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  have h0 := ht.1; have h1 := ht.2
  have : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := by
  intro v hv; simp only [openUnitDisk, closedUnitDisk, mem_setOf_eq] at *; exact hv.le

lemma isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)) continuous_const

lemma zero_mem_openUnitDisk : (0 : Plane) ∈ openUnitDisk := by
  simp [openUnitDisk]

lemma eq_zero_at_one {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ t ∈ Ico (0 : ℝ) 1, g t = 0) :
    g 1 = 0 := by
  have hc : IsClosed {t | g t = 0} := isClosed_eq hg continuous_const
  have hsub : closure (Ico (0 : ℝ) 1) ⊆ {t | g t = 0} := hc.closure_subset_iff.2 h
  rw [closure_Ico zero_ne_one] at hsub
  exact hsub ⟨zero_le_one, le_rfl⟩

lemma nonneg_at_one {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ g t) :
    0 ≤ g 1 := by
  have hc : IsClosed {t | 0 ≤ g t} := isClosed_le continuous_const hg
  have hsub : closure (Ico (0 : ℝ) 1) ⊆ {t | 0 ≤ g t} := hc.closure_subset_iff.2 h
  rw [closure_Ico zero_ne_one] at hsub
  exact hsub ⟨zero_le_one, le_rfl⟩

variable (hH : ContDiff ℝ ∞ H) (he : ContDiff ℝ ∞ e)
  (hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1)
include hH he hDS

lemma dH_fderiv_open {v : Plane} (hv : v ∈ openUnitDisk) (w : Plane) :
    fderiv ℝ H (e v) (fderiv ℝ e v w) = 0 := by
  have hev : (H ∘ e) =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_openUnitDisk.mem_nhds hv] with q hq
    exact hDS q (openUnitDisk_subset hq)
  have h0 : fderiv ℝ (H ∘ e) v = 0 := by rw [hev.fderiv_eq]; simp
  have hc : fderiv ℝ (H ∘ e) v = (fderiv ℝ H (e v)).comp (fderiv ℝ e v) :=
    fderiv_comp v ((hH.differentiable (by simp)) _) ((he.differentiable (by simp)) _)
  have := congrArg (fun L : Plane →L[ℝ] ℝ => L w) (hc.symm.trans h0)
  simpa using this

lemma contDiff_fderiv_e : ContDiff ℝ ∞ (fderiv ℝ e) := he.fderiv_right le_rfl

lemma dH_fderiv_closed {v : Plane} (hv : v ∈ closedUnitDisk) (w : Plane) :
    fderiv ℝ H (e v) (fderiv ℝ e v w) = 0 := by
  have hsm : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
  have hg : Continuous fun t : ℝ => fderiv ℝ H (e (t • v)) (fderiv ℝ e (t • v) w) :=
    ((contDiff_fderiv_of_smooth hH).continuous.comp (he.continuous.comp hsm)).clm_apply
      (((contDiff_fderiv_e hH he hDS).continuous.comp hsm).clm_apply continuous_const)
  have := eq_zero_at_one hg fun t ht =>
    dH_fderiv_open hH he hDS (smul_mem_openUnitDisk hv ht) w
  simpa using this

lemma dH_pos_closed (hS : IsStrictlyStarShapedLevel H) {v : Plane} (hv : v ∈ closedUnitDisk) :
    0 < fderiv ℝ H (e v) (e v) := hS.2.2 _ (hDS v hv)

omit hH he hDS in
lemma eq_smul_X_of_xiPsi_eq_zero {x w : R4} (hx : 0 < fderiv ℝ H x x) (hw : fderiv ℝ H x w = 0)
    (h0 : xiPsi H x w = 0) :
    w = (liouvilleForm x w / liouvilleForm x (hamiltonianVectorField H x)) •
      hamiltonianVectorField H x := by
  have h := reebProjection_eq_xiPsi hx hw
  rw [h0] at h
  simp only [Complex.zero_re, Complex.zero_im, zero_smul, add_zero] at h
  exact sub_eq_zero.1 h

lemma xiPsi_ne_zero_open (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) {w : Plane} (hw : w ≠ 0) :
    xiPsi H (e v) (fderiv ℝ e v w) ≠ 0 := by
  intro h0
  have hx := dH_pos_closed hH he hDS hS (openUnitDisk_subset hv)
  have h := eq_smul_X_of_xiPsi_eq_zero hx (dH_fderiv_open hH he hDS hv w) h0
  set c := liouvilleForm (e v) (fderiv ℝ e v w) /
    liouvilleForm (e v) (hamiltonianVectorField H (e v))
  by_cases hc : c = 0
  · rw [hc, zero_smul] at h
    exact hw (hinj v (openUnitDisk_subset hv) (by rw [h, map_zero]))
  · apply htr v hv
    refine ⟨c⁻¹ • w, ?_⟩
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `ω₀` on the image of the standard basis. -/
def diskOmega (e : Plane → R4) (v : Plane) : ℝ :=
  omega0 (fderiv ℝ e v (Pi.single 0 1)) (fderiv ℝ e v (Pi.single 1 1))

omit hH he hDS in
lemma fderiv_plane_eq (v a : Plane) :
    fderiv ℝ e v a = a 0 • fderiv ℝ e v (Pi.single 0 1) + a 1 • fderiv ℝ e v (Pi.single 1 1) := by
  have ha : a = a 0 • (Pi.single 0 1 : Plane) + a 1 • (Pi.single 1 1 : Plane) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [ha]
  simp only [map_add, map_smul]

omit hH he hDS in
lemma omega0_fderiv_plane (v a b : Plane) :
    omega0 (fderiv ℝ e v a) (fderiv ℝ e v b) = (a 0 * b 1 - a 1 * b 0) * diskOmega e v := by
  rw [fderiv_plane_eq v a, fderiv_plane_eq v b, diskOmega]
  simp only [omega0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma continuous_diskOmega : Continuous (diskOmega e) :=
  continuous_omega0 ((contDiff_fderiv_e hH he hDS).continuous.clm_apply continuous_const)
    ((contDiff_fderiv_e hH he hDS).continuous.clm_apply continuous_const)

lemma diskOmega_ne_zero (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : diskOmega e v ≠ 0 := by
  intro hD
  have hx := dH_pos_closed hH he hDS hS (openUnitDisk_subset hv)
  set e0 : Plane := Pi.single 0 1
  set e1 : Plane := Pi.single 1 1
  set ζ := xiPsi H (e v) (fderiv ℝ e v e0)
  set η := xiPsi H (e v) (fderiv ℝ e v e1)
  have he0 : e0 ≠ 0 := fun h => by simpa [e0] using congrFun h 0
  have hζ : ζ ≠ 0 := xiPsi_ne_zero_open hH he hDS hS hinj htr hv he0
  have him : ((starRingEnd ℂ) ζ * η).im = 0 := by
    rw [xiPsi_im_conj_mul hx (dH_fderiv_open hH he hDS hv e0) (dH_fderiv_open hH he hDS hv e1)]
    exact hD
  set t : ℝ := (η / ζ).re
  have hηt : η = (t : ℂ) * ζ := by
    have him' : η.im * ζ.re - η.re * ζ.im = 0 := by
      simp [Complex.mul_im] at him; linarith
    have hreal : η / ζ = (t : ℂ) := by
      apply Complex.ext
      · simp [t]
      · rw [Complex.div_im, ← sub_div, him', zero_div]; simp
    rw [← hreal, div_mul_cancel₀ _ hζ]
  have hw : (1 : ℝ) • e1 + (-t) • e0 ≠ 0 := fun h => by
    have := congrFun h 1
    simp [e0, e1] at this
  apply xiPsi_ne_zero_open hH he hDS hS hinj htr hv hw
  rw [map_add, map_smul, map_smul, xiPsi_add_smul]
  change ((1 : ℝ) : ℂ) * η + ((-t : ℝ) : ℂ) * ζ = 0
  rw [hηt]; push_cast; ring

lemma diskOmega_mul_pos (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : 0 < diskOmega e v * diskOmega e 0 := by
  have hD0 := diskOmega_ne_zero hH he hDS hS hinj htr zero_mem_openUnitDisk
  by_contra hle
  push_neg at hle
  set h : ℝ → ℝ := fun t => diskOmega e (t • v) * diskOmega e 0
  have hc : Continuous h :=
    ((continuous_diskOmega hH he hDS).comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h 0 = diskOmega e 0 * diskOmega e 0 := by simp [h]
  have h1 : h 1 = diskOmega e v * diskOmega e 0 := by simp [h]
  have hmem : (0 : ℝ) ∈ Icc (h 1) (h 0) := ⟨by rw [h1]; exact hle, by rw [h0]; exact mul_self_nonneg _⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn hmem
  have := diskOmega_ne_zero hH he hDS hS hinj htr (smul_mem_openUnitDisk' hv ht)
  exact this (by simpa [h, hD0] using hzero)

lemma diskOmega_mul_nonneg (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ closedUnitDisk) : 0 ≤ diskOmega e v * diskOmega e 0 := by
  have hc : Continuous fun t : ℝ => diskOmega e (t • v) * diskOmega e 0 :=
    ((continuous_diskOmega hH he hDS).comp (continuous_id.smul continuous_const)).mul continuous_const
  have := nonneg_at_one hc fun t ht =>
    (diskOmega_mul_pos hH he hDS hS hinj htr (smul_mem_openUnitDisk hv ht)).le
  simpa using this

end HryniewiczCriterion

/-!
# `disk_conormal_pushOff_linking_zero`

The push-off of `∂D` along the `ξ`-projected outward conormal misses the radial cone over `D`
for small `ε` (`sf_separation`). Choosing a pole off that cone, the orbit loop contracts
through the (radially projected) disk in the complement of the push-off, so the Gauss
integral equals that of a constant loop, `0`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma sf_contDiff_liouville {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {x v : E → R4} (hx : ContDiff ℝ n x) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n fun p => liouvilleForm (x p) (v p) := by
  have hx' : ∀ i, ContDiff ℝ n fun p => x p i := fun i => contDiff_pi.1 hx i
  have hv' : ∀ i, ContDiff ℝ n fun p => v p i := fun i => contDiff_pi.1 hv i
  simp only [liouvilleForm]
  exact (((((hx' 0).mul (hv' 1)).sub ((hx' 1).mul (hv' 0))).add ((hx' 2).mul (hv' 3))).sub
    ((hx' 3).mul (hv' 2))).div_const 2

theorem disk_conormal_pushOff_linking_zero' (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsLinkingNumber (orbitLoop P)
        (fun s => radialNormalize (P.x (P.T * s) + ε • (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))))) 0 := by
  have hH : ContDiff ℝ ∞ H := hS.1
  have hE : ContDiff ℝ ∞ e := he.1
  have h2inf : (2 : WithTop ℕ∞) ≤ ∞ := by first | decide | simp | norm_num | exact_mod_cast le_top
  have hD : ∀ v ∈ closedUnitDisk, H (e v) = 1 := fun v hv => hDS ⟨v, hv, rfl⟩
  have hcl : ∀ s, u s ∈ closedUnitDisk := fun s => le_of_eq (hucirc s)
  have hpos : ∀ v ∈ closedUnitDisk, 0 < fderiv ℝ H (e v) (e v) := fun v hv =>
    dH_pos_closed hH hE hD hS hv
  have h0 : ∀ v ∈ closedUnitDisk, e v ≠ 0 := by
    intro v hv h
    have := hpos v hv
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  have htr : ∀ v ∈ closedUnitDisk, e v ∉ range (fderiv ℝ e v) := by
    rintro v hv ⟨w, hw⟩
    have := dH_fderiv_closed hH hE hD hv w
    rw [hw] at this
    linarith [hpos v hv]
  have hrad : ∀ v ∈ closedUnitDisk, ∀ v' ∈ closedUnitDisk, ∀ μ : ℝ, 0 < μ →
      μ • e v = e v' → μ = 1 := by
    intro v hv v' hv' μ hμ he'
    obtain ⟨r, _, hr⟩ := hS.2.1 (e v) (h0 v hv)
    have h1 := hr 1 ⟨one_pos, by rw [one_smul]; exact hD v hv⟩
    have h2 := hr μ ⟨hμ, by rw [he']; exact hD v' hv'⟩
    rw [h1, h2]
  set T := P.T
  have hT : 0 < T := P.T_pos
  have hd : ∀ t, HasDerivAt u (deriv u t) t := fun t => ((hu.differentiable (by simp)) t).hasDerivAt
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  set X := hamiltonianVectorField H
  -- `de(u) u' = T X`
  have hdu : ∀ s, fderiv ℝ e (u s) (deriv u s) = T • X (e (u s)) := by
    intro s
    have h1 : HasDerivAt (fun s => e (u s)) (fderiv ℝ e (u s) (deriv u s)) s :=
      ((hE.differentiable (by simp)) (u s)).hasFDerivAt.comp_hasDerivAt s (hd s)
    have h2 : HasDerivAt (fun s => P.x (T * s)) ((T : ℝ) • X (P.x (T * s))) s := by
      have := (P.trajectory.1 (T * s)).scomp s ((hasDerivAt_id s).const_mul T)
      convert this using 1 <;> first | rfl | simp [X]
    have hfun : (fun s => e (u s)) = fun s => P.x (T * s) := funext heu
    rw [hfun] at h1
    rw [h1.unique h2, heu s]
  -- `⟨u, u'⟩ = 0`
  have hudot : ∀ s, u s 0 * deriv u s 0 + u s 1 * deriv u s 1 = 0 := by
    intro s
    have hdi : ∀ t i, HasDerivAt (fun t => u t i) (deriv u t i) t :=
      fun t i => hasDerivAt_pi.1 (hd t) i
    have hsq : HasDerivAt (fun t => u t 0 * u t 0 + u t 1 * u t 1)
        (deriv u s 0 * u s 0 + u s 0 * deriv u s 0 + (deriv u s 1 * u s 1 + u s 1 * deriv u s 1)) s :=
      ((hdi s 0).mul (hdi s 0)).add ((hdi s 1).mul (hdi s 1))
    have hconst : (fun t => u t 0 * u t 0 + u t 1 * u t 1) = fun _ => (1 : ℝ) := funext fun t => by
      have := hucirc t; simp only [unitCircle, mem_setOf_eq] at this; linarith
    rw [hconst] at hsq
    have := hsq.unique (hasDerivAt_const s 1); linarith
  -- the outward field `a` with `de(u) a = W`
  set c : ℝ → ℝ := fun s => liouvilleForm (e (u s)) (fderiv ℝ e (u s) (u s)) /
    liouvilleForm (e (u s)) (X (e (u s))) with hc
  set a : ℝ → Plane := fun s => u s - (c s / T) • deriv u s with ha
  have hW : ∀ s, fderiv ℝ e (u s) (u s) - c s • X (e (u s)) = fderiv ℝ e (u s) (a s) := by
    intro s
    simp only [a, map_sub, map_smul, hdu s, smul_smul, div_mul_cancel₀ _ hT.ne']
  have hlpos : ∀ s, 0 < liouvilleForm (e (u s)) (X (e (u s))) := by
    intro s; rw [liouville_X]; linarith [hpos _ (hcl s)]
  have hXC : ContDiff ℝ ∞ fun s => X (e (u s)) := (contDiff_hvf hH).comp (hE.comp hu)
  have hdeC : ContDiff ℝ ∞ fun s => fderiv ℝ e (u s) (u s) :=
    ((hE.fderiv_right le_rfl).comp hu).clm_apply hu
  have hcC : ContDiff ℝ ∞ c :=
    (sf_contDiff_liouville (hE.comp hu) hdeC).div (sf_contDiff_liouville (hE.comp hu) hXC)
      fun s => (hlpos s).ne'
  have hac : Continuous a := hu.continuous.sub ((hcC.continuous.div_const T).smul hdc)
  have hduper : ∀ s, deriv u (s + 1) = deriv u s := by
    intro s
    rw [← deriv_comp_add_const]
    exact congrArg (fun g => deriv g s) (funext huper)
  have haper : ∀ s, a (s + 1) = a s := by intro s; simp only [a, c, huper, hduper]
  have hua : ∀ s, 0 < u s 0 * a s 0 + u s 1 * a s 1 := by
    intro s
    have h1 : u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc s
    have e1 : u s 0 * a s 0 + u s 1 * a s 1 =
        (u s 0 ^ 2 + u s 1 ^ 2) - c s / T * (u s 0 * deriv u s 0 + u s 1 * deriv u s 1) := by
      simp only [a, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, h1, hudot s]; norm_num
  obtain ⟨ε₀, hε₀, hsep⟩ := sf_separation e hE he.2.1 he.2.2 htr h0 hrad u a hu.continuous hac
    huper haper hucirc hua
  refine ⟨ε₀, hε₀, fun ε hε hεlt => ?_⟩
  set γ₁ : ℝ → R4 := fun s => radialNormalize (e (u s)) with hγ₁
  set γ₂ : ℝ → R4 := fun s => radialNormalize (e (u s) + ε • fderiv ℝ e (u s) (a s)) with hγ₂
  have hL : orbitLoop P = γ₁ := by
    funext s; simp only [orbitLoop, γ₁, heu]; rfl
  have hR : (fun s => radialNormalize (P.x (T * s) + ε • (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (T * s)) (X (P.x (T * s)))) • X (P.x (T * s))))) = γ₂ := by
    funext s
    rw [← heu s]
    show radialNormalize (e (u s) + ε • (fderiv ℝ e (u s) (u s) - c s • X (e (u s)))) = _
    rw [hW s]
  rw [hL, hR]
  have hy0 : ∀ s, e (u s) + ε • fderiv ℝ e (u s) (a s) ≠ 0 := fun s h =>
    hsep ε hε hεlt s (u s) (hcl s) 0 le_rfl (by rw [h, zero_smul])
  have hsepN : ∀ v ∈ closedUnitDisk, ∀ t, radialNormalize (e v) ≠ γ₂ t := by
    intro v hv t
    apply sf_ne_normalize (hy0 t)
    intro μ hμ heq
    exact hsep ε hε hεlt t v hv (μ * (euclidNorm (e v))⁻¹)
      (mul_nonneg hμ.le (inv_nonneg.2 (gl_euclidNorm_pos (h0 v hv)).le))
      (by rw [heq, radialNormalize, smul_smul])
  have hyC : ContDiff ℝ ∞ fun s => e (u s) + ε • fderiv ℝ e (u s) (a s) := by
    have : (fun s => e (u s) + ε • fderiv ℝ e (u s) (a s)) =
        fun s => e (u s) + ε • (fderiv ℝ e (u s) (u s) - c s • X (e (u s))) := by
      funext s; rw [hW s]
    rw [this]
    have h3 : ContDiff ℝ ∞ fun s => c s • X (e (u s)) := hcC.smul hXC
    have h4 : ContDiff ℝ ∞ fun s => ε • (fderiv ℝ e (u s) (u s) - c s • X (e (u s))) :=
      (hdeC.sub h3).const_smul ε
    exact (hE.comp hu).add h4
  have hγ₁C : ContDiff ℝ 2 γ₁ := sf_contDiff_normalize ((hE.comp hu).of_le h2inf)
    fun s => h0 _ (hcl s)
  have hγ₂C : ContDiff ℝ 2 γ₂ := sf_contDiff_normalize (hyC.of_le h2inf) hy0
  have hγ₁per : ∀ s, γ₁ (s + 1) = γ₁ s := fun s => by simp only [γ₁, huper]
  have hγ₂per : ∀ s, γ₂ (s + 1) = γ₂ s := fun s => by simp only [γ₂, huper, haper]
  have hu₁ : ∀ s, euclidNorm (γ₁ s) = 1 := fun s => gl_euclidNorm_normalize (h0 _ (hcl s))
  have hu₂ : ∀ s, euclidNorm (γ₂ s) = 1 := fun s => gl_euclidNorm_normalize (hy0 s)
  obtain ⟨N, hN, hNe, hNγ⟩ := sf_exists_pole e (hE.differentiable (by simp)) γ₂
    (hγ₂C.differentiable (by simp)) hu₂
  have hNγ₁ : ∀ s, γ₁ s ≠ N := fun s => hNe _ (h0 _ (hcl s))
  refine isLinkingNumber_of_gaussLinkingIntegral_eq' γ₁ γ₂ hγ₁C hγ₂C hγ₁per hγ₂per hu₁ hu₂
    (fun s t => hsepN (u s) (hcl s) t) N hN (fun s => ⟨hNγ₁ s, hNγ s⟩) 0 ?_
  -- contract the orbit loop through the disk
  set φ : ℝ → ℝ := fun τ => Real.sin (Real.pi / 2 * τ) ^ 2 with hφ
  have hφC : ContDiff ℝ ∞ φ :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2
  have hmemD : ∀ τ s, φ τ • u s ∈ closedUnitDisk := by
    intro τ s
    have h1 : u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc s
    have hφ1 : φ τ ^ 2 ≤ 1 := by
      have := Real.sin_sq_le_one (Real.pi / 2 * τ)
      have h0' : 0 ≤ φ τ := sq_nonneg _
      nlinarith
    simp only [closedUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    nlinarith
  set R : ℝ → ℝ → R4 := fun τ s => radialNormalize (e (φ τ • u s)) with hRdef
  have hRC : ContDiff ℝ 2 (Function.uncurry R) :=
    sf_contDiff_normalize (y := fun p : ℝ × ℝ => e (φ p.1 • u p.2))
      ((hE.comp ((hφC.comp contDiff_fst).smul (hu.comp contDiff_snd))).of_le h2inf)
      (fun p => h0 _ (hmemD _ _))
  have hRper : ∀ τ s, R τ (s + 1) = R τ s := fun τ s => by simp only [R, huper]
  have hRunit : ∀ τ s, euclidNorm (R τ s) = 1 := fun τ s => gl_euclidNorm_normalize (h0 _ (hmemD _ _))
  have hRN : ∀ τ s, R τ s ≠ N := fun τ s => hNe _ (h0 _ (hmemD _ _))
  have hne : ∀ τ s t, R τ s ≠ γ₂ t := fun τ s t => hsepN _ (hmemD τ s) t
  have hhom := sf_gauss_homotopy_left N hN R γ₂ hRC hγ₂C hRper hγ₂per hRunit hu₂ hRN hNγ hne
  have hR0 : R 0 = fun _ => radialNormalize (e 0) := by
    funext s; simp [R, φ]
  have hR1 : R 1 = γ₁ := by
    funext s; simp [R, φ, γ₁]
  rw [hR0, hR1, sf_gauss_const] at hhom
  rw [← hhom]; simp

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsLinkingNumber (orbitLoop P)
        (fun s => radialNormalize (P.x (P.T * s) + ε • (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))))) 0 :=
  disk_conormal_pushOff_linking_zero' H hS P hP e he hDS hbd u hu huper hucirc heu
