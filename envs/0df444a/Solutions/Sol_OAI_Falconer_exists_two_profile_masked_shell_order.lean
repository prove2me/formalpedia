-- Prove2me | solution 1 for OAI.Falconer.exists_two_profile_masked_shell_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:23:37.807986+00:00
-- url     : https://prove2.me/submissions/2e3c60fd-2cd2-4611-a060-f561f89fbdfb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_scalar_shell_of_two_profile_inverse
import Theorems.Thm_OAI_Falconer_sphere_stationary_expansion

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The failed perpendicular test in an actual spherical chart

The normalized affine chart stays within twice its tangent displacement
of the cap center. Its coordinate derivative therefore inherits the
uniform lower bound proved for the tangential sphere field.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_chart_nonzero {w h : E} (hw : ‖w‖ = 1) (hh : inner ℝ w h = 0) :
    w+h ≠ 0 := by
  intro he
  have hi := congrArg (inner ℝ w) he
  simp only [inner_add_right,real_inner_self_eq_norm_sq,hw,one_pow,hh,add_zero,
    inner_zero_right] at hi
  norm_num at hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartDerivatives
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of the normalized line chart

The scalar denominator is a smooth function of two real variables on a
fixed compact square. Its bounds are independent of the chart center,
tangent direction, and displacement. No analytic input is assumed here.
-/

namespace Falconer
open Set
open scoped ContDiff

private theorem partialSecond_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (partialSecond F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

private theorem partialSecond_eq {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (s u : ℝ) :
    partialSecond F n (s,u) = iteratedDeriv n (fun x => F (s,x)) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have hp : HasDerivAt (fun x : ℝ => (s,x)) (0,1) u :=
      (hasDerivAt_const u s).prodMk (hasDerivAt_id u)
    have hh := ((partialSecond_smooth hF n).differentiable (by simp) (s,u)).hasFDerivAt.comp_hasDerivAt u hp
    rw [iteratedDeriv_succ]
    change fderiv ℝ (partialSecond F n) (s,u) (0,1) = _
    rw [← hh.deriv]
    congr 1
    funext x
    exact ih x

private theorem uniform_section_derivatives {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => F (s,x)) u| ≤ C := by
  have hc := (partialSecond_smooth hF n).continuous.abs
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs u hu
  rw [← partialSecond_eq hF]
  exact (hC ⟨(s,u),⟨hs,hu⟩,rfl⟩).trans (le_max_left _ _)

theorem chartLineKernel_smooth : ContDiff ℝ ∞ chartLineKernel := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact (h.sqrt (fun p => by positivity)).inv (fun p => by positivity)

theorem chartLineKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives chartLineKernel_smooth n

theorem chartLineLinearKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => x * chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives (contDiff_snd.mul chartLineKernel_smooth) n

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_norm_sq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    ‖(w+y)+u•t‖^2 = 1+‖y‖^2+u^2 := by
  rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,real_inner_smul_right,
    real_inner_smul_right,hwy,hwt,hyt,hw,norm_smul,ht,Real.norm_eq_abs]
  simp only [one_pow,mul_zero,zero_add,mul_one,sq_abs]
  ring

end InnerProduct

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

theorem northLift_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    northLift (coordinateJoin x u) =
      (chartPole n + transverseLift x) + u • chartAxis n := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]

theorem gnomonicChart_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    (gnomonicChart (coordinateJoin x u) : Space (n+2)) =
      normalizedLine (chartPole n + transverseLift x) (chartAxis n) u := by
  simp only [gnomonicChart,normalizedLine,northLift_coordinateJoin]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AmbientSymbols
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ambient smooth symbols in the adapted spherical chart

The smooth cap partition is constructed in Euclidean space. Its restriction
to every rotated one-coordinate spherical chart is smooth, including at
points where the amplitude vanishes.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalizedLine_contDiff (a t : E) (hne : ∀ u : ℝ, a+u•t ≠ 0) :
    ContDiff ℝ ∞ (normalizedLine a t) := by
  have hz : ContDiff ℝ ∞ (fun u : ℝ => a+u•t) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact ((hz.norm ℝ hne).inv (fun u => norm_ne_zero_iff.mpr (hne u))).smul hz

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BumpDerivatives
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of scaled cap bumps

A single compactly supported bump controls every center and radius. The
scale enters through the curve supplied to that fixed bump, so the k-th
bound loses only the k-th power of the inverse cap radius.
-/

namespace Falconer
open Set
open scoped ContDiff

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    normalizedLine (w+y) t u =
      chartLineKernel (‖y‖,u) • (w+y) + (u*chartLineKernel (‖y‖,u)) • t := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,hn,chartLineKernel,smul_add,smul_smul]
  rw [mul_comm]

theorem tangent_line_derivatives (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (normalizedLine (w+y) t) u‖ ≤ B := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives m
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives m
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x*chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have hwyb : ‖w+y‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hw]; linarith)
  have he : normalizedLine (w+y) t = (fun x =>
      chartLineKernel (‖y‖,x) • (w+y) + (x*chartLineKernel (‖y‖,x)) • t) :=
    funext (tangent_line_eq hw ht hwy hwt hyt)
  have hk' : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x) • (w+y)) :=
    hk.smul contDiff_const
  have hl' : ContDiff ℝ ∞ (fun x => (x*chartLineKernel (‖y‖,x)) • t) :=
    hl.smul contDiff_const
  rw [he,iteratedDeriv_fun_add
    ((hk'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) ((hl'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hk.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hl.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ‖iteratedDeriv m (fun x => chartLineKernel (‖y‖,x)) u • (w+y)‖ +
        ‖iteratedDeriv m (fun x => x*chartLineKernel (‖y‖,x)) u • t‖ := norm_add_le _ _
    _ ≤ C*2+D*1 := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul (hCb _ hys _ hu) hwyb (norm_nonneg _) hC)
        (mul_le_mul (hDb _ hys _ hu) ht.le (norm_nonneg _) hD)
    _ = _ := by ring

/-- One fixed scale controls all positive orders up to a chosen finite order. -/
theorem tangent_line_derivative_scale (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (normalizedLine (w+y) t) u‖ ≤ D^k := by
  choose B hB hBb using (fun k => tangent_line_derivatives (E := E) k)
  let D := 1+∑ k ∈ Finset.range (m+1), B k
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (m+1)) => hB k)]
  refine ⟨D,hD,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu k hk hkm
  apply (hBb k w y t hw ht hwy hwt hyt hy u hu).trans
  have hb : B k ≤ D := by
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m+1)) => hB j)
      (Finset.mem_range.mpr (by omega : k < m+1))
    dsimp [D]
    linarith
  exact hb.trans (le_self_pow₀ hD (by omega))

end InnerProduct
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartBumps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap bump derivatives in every rotated spherical chart

The constants depend only on the ambient dimension and derivative order.
The cap center, rotation, radius and transverse chart coordinate remain free.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem rotatedChartCurve_contDiff {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartCurve e y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun u => e (gnomonicChart (coordinateJoin y u)))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using he.comp hp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryInverse
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite inverse for the higher-dimensional stationary expansion

The polynomials are those of `osc:L-operators` and `osc:B-operators` in
Section 6 of the manuscript. Their variable represents the sphere Laplacian.
The finite inverse identity is algebraic and independent of a sphere
stationary-phase expansion.
-/

namespace Falconer
open Polynomial
open scoped BigOperators

theorem sphereStationaryConstant_ne_zero (n : ℕ) :
    sphereStationaryConstant n ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi)
      ((n : ℝ) / 2)).ne'
  · exact Complex.exp_ne_zero _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ParametricJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth dependence of the actual quadratic stationary jets

The derivatives are taken only in the tangent variable. Joint smoothness
of an amplitude therefore gives smooth dependence of every fixed quadratic
jet on its external parameters, including the evaluation direction.
-/

namespace Falconer
open InnerProductSpace
open scoped ContDiff

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem partialFDeriv_contDiffAt {n : ℕ} {F : P × Space n → G} {p : P} {x : Space n}
    (hF : ContDiffAt ℝ ∞ F (p,x)) :
    ContDiffAt ℝ ∞ (fun z : P × Space n => fderiv ℝ (fun y => F (z.1,y)) z.2) (p,x) := by
  have hf : ContDiffAt ℝ ∞
      (fun z : (P × Space n) × Space n => F (z.1.1,z.2)) ((p,x),x) :=
    hF.comp ((p,x),x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hf.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem partialLaplacian_contDiffAt {n : ℕ} {F : P × Space n → ℂ} {p : P} {x : Space n}
    (hF : ContDiffAt ℝ ∞ F (p,x)) :
    ContDiffAt ℝ ∞
      (fun z : P × Space n => Laplacian.laplacian (fun y => F (z.1,y)) z.2) (p,x) := by
  have h₂ := partialFDeriv_contDiffAt (partialFDeriv_contDiffAt hF)
  have heq : (fun z : P × Space n => Laplacian.laplacian (fun y => F (z.1,y)) z.2) =
      (fun z => ∑ i : Fin n,
        (fderiv ℝ (fun y => fderiv ℝ (fun v => F (z.1,v)) y) z.2)
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
    funext z
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin n) ℝ)]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [heq]
  exact ContDiffAt.sum (fun i _ => (h₂.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

theorem partialIteratedLaplacian_contDiffAt {n : ℕ} {F : P × Space n → ℂ}
    {p : P} {x : Space n} (hF : ContDiffAt ℝ ∞ F (p,x)) (j : ℕ) :
    ContDiffAt ℝ ∞
      (fun z : P × Space n =>
        ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
          (fun y => F (z.1,y))) z.2) (p,x) := by
  induction j with
  | zero => simpa using hF
  | succ j hj =>
      simpa only [Function.iterate_succ_apply'] using partialLaplacian_contDiffAt hj

theorem quadraticJetCoefficient_contDiffAt {n : ℕ} {F : P × Space n → ℂ} {p : P}
    (hF : ContDiffAt ℝ ∞ F (p,0)) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun q : P => quadraticJetCoefficient j (fun u => F (q,u))) p := by
  have h := (partialIteratedLaplacian_contDiffAt hF j).comp p
    (contDiffAt_id.prodMk contDiffAt_const)
  exact contDiffAt_const.mul h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite-derivative bounds for stationary jets

The Laplacian is a fixed finite sum of second directional derivatives.
Expressing that contraction as a continuous linear map gives bounds for
all mixed Fréchet derivatives, without replacing them by separate bounds
on a single chart coordinate. Vertical unit vectors in a parameter/tangent
product give the partial Laplacian used by the actual stationary operators.
-/

namespace Falconer
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.Falconer.instNormedSpaceRealContinuousLinearMapIdComplex_solutions
attribute [local instance] OAI.Falconer.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions
theorem directionalLaplacianTrace_norm_le {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖directionalLaplacianTrace v‖ ≤ n := by
  apply (directionalLaplacianTrace v).opNorm_le_bound (Nat.cast_nonneg n)
  intro T
  rw [directionalLaplacianTrace_apply]
  calc
    ‖∑ i : Fin n, T (v i) (v i)‖ ≤ ∑ i : Fin n, ‖T (v i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖T (v i) (v i)‖ ≤ ‖T (v i)‖ * ‖v i‖ := (T (v i)).le_opNorm _
        _ ≤ (‖T‖ * ‖v i‖) * ‖v i‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖T‖ := by
          simpa only [mul_one] using mul_le_mul
            (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg T))
            (hv i) (norm_nonneg (v i)) (mul_nonneg (norm_nonneg T) zero_le_one)
    _ = (n : ℝ) * ‖T‖ := by simp

theorem directionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directionalLaplacian v f) := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    h₁.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (directionalLaplacianTrace v).contDiff.comp hd

theorem iteratedDirectionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ ((directionalLaplacian v)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      exact directionalLaplacian_contDiff v hj

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem verticalDirections_norm {n : ℕ} (i : Fin n) :
    ‖(verticalDirections n i : P × Space n)‖ ≤ 1 := by
  simp [verticalDirections, Prod.norm_def]

theorem directionalLaplacian_vertical {n : ℕ} {F : P × Space n → ℂ}
    (hF : ContDiff ℝ ∞ F) (p : P) (x : Space n) :
    directionalLaplacian (verticalDirections n) F (p,x) =
      Laplacian.laplacian (fun y => F (p,y)) x := by
  let g : P × Space n → ℂ := fun z => F ((p,0)+z)
  have hg : ContDiff ℝ ∞ g := hF.comp (contDiff_const.add contDiff_id)
  have hd := (ContinuousLinearMap.inr ℝ P (Space n)).iteratedFDeriv_comp_right
    hg x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (2 : ℕ∞ω) ≤ ∞)
  have heq : g ∘ ContinuousLinearMap.inr ℝ P (Space n) = fun y => F (p,y) := by
    funext y
    simp [g]
  rw [heq] at hd
  have hshift : iteratedFDeriv ℝ 2 g (0,x) = iteratedFDeriv ℝ 2 F (p,x) := by
    simpa only [g, Prod.mk_add_mk, add_zero, zero_add] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) 2 (p,0) (0,x))
  change iteratedFDeriv ℝ 2 (fun y => F (p,y)) x =
    (iteratedFDeriv ℝ 2 g (0,x)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ P (Space n)) at hd
  rw [hshift] at hd
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_two_apply]
  rfl

theorem iteratedDirectionalLaplacian_vertical {n : ℕ} {F : P × Space n → ℂ}
    (hF : ContDiff ℝ ∞ F) (j : ℕ) (p : P) (x : Space n) :
    ((directionalLaplacian (verticalDirections n))^[j] F) (p,x) =
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (p,y))) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [directionalLaplacian_vertical
        (iteratedDirectionalLaplacian_contDiff _ hF j)]
      exact congrArg (fun g : Space n → ℂ => Laplacian.laplacian g x) (funext hj)

end Parameters

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorAmbientMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientMask Q ρ m N σ J i b S)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _).continuous.measurable.comp
    measurable_snd).ite ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

 theorem descriptorAmbientProduct_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) :
    ContDiff ℝ ∞ (descriptorAmbientProduct Q ρ m N σ J i B S x) :=
  contDiff_prod (fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x)

 theorem descriptorAmbientProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorAmbientMask_measurable Q ρ m N σ J i b (S b))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianIsometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance and locality of the actual quadratic jets

These are identities for the Euclidean derivatives in the published input.
They allow the choice of tangent orthonormal coordinates and fixed cutoffs
to be removed from the resulting stationary coefficients.
-/

namespace Falconer
open InnerProductSpace
open scoped Topology

theorem euclidean_iterated_laplacian_congr {n : ℕ} {f g : Space n → ℂ}
    {x : Space n} (h : f =ᶠ[𝓝 x] g) (j : ℕ) :
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) =ᶠ[𝓝 x]
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] g) := by
  induction j with
  | zero => exact h
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact laplacian_congr_nhds hj

theorem quadraticJetCoefficient_congr {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᶠ[𝓝 (0 : Space n)] g) (j : ℕ) :
    quadraticJetCoefficient j f = quadraticJetCoefficient j g := by
  unfold quadraticJetCoefficient
  rw [(euclidean_iterated_laplacian_congr h j).self_of_nhds]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuadraticChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed quadratic chart at a sphere pole

This is the actual chart in `osc:stationary`. Its phase is exactly quadratic,
in every dimension. Surface measure transport and its Jacobian are separate
from the geometric statements here.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem quadraticSpherePoint_norm {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u‖ = 1 := by
  have hu2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have harg : 0 ≤ 1-‖u‖^2/4 := by nlinarith
  have hs := Real.sq_sqrt harg
  have he := coordinateJoin_norm_sq (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs] at he
  change ‖quadraticSpherePoint u‖^2 = _ at he
  nlinarith [norm_nonneg (quadraticSpherePoint u)]

theorem gnomonicChart_quadraticToGnomonic {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (gnomonicChart (quadraticToGnomonic u) : Space (n+1)) = quadraticSpherePoint u := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; nlinarith
  have he : northLift (quadraticToGnomonic u) = a⁻¹ • quadraticSpherePoint u := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [northLift_zero, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_zero_coord]
      change 1 = a⁻¹ * a
      exact (inv_mul_cancel₀ ha.ne').symm
    · simp only [northLift_succ, quadraticToGnomonic, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_succ_coord]
      dsimp only [a]
      ring
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    rw [he, norm_smul, quadraticSpherePoint_norm (hu.le.trans (by norm_num)),
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_one]
  change ‖northLift (quadraticToGnomonic u)‖⁻¹ • northLift (quadraticToGnomonic u) = _
  rw [hn, he, smul_smul, inv_inv, mul_inv_cancel₀ ha.ne', one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

theorem stationaryPoleRotation_pole {n : ℕ} (e : Sphere (n+1)) :
    stationaryPoleRotation e (gnomonicChart (0 : Space n)) = (e : Space (n+1)) := by
  have h := Submodule.reflection_sub
    (v := (gnomonicChart (0 : Space n) : Space (n+1))) (w := -(e : Space (n+1)))
    (by rw [norm_neg, sphere_norm, sphere_norm])
  rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
  exact neg_injective h

theorem stationaryPoleRotation_apply {n : ℕ} (e : Sphere (n+1)) (x : Space (n+1)) :
    stationaryPoleRotation e x =
      poleRotationFormula (gnomonicChart (0 : Space n)) e x := by
  rw [stationaryPoleRotation, Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartJetOperators
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual stationary operators on a smooth pole patch

The operators are the quadratic Laplacian jets of the explicit chart
amplitude. They depend smoothly on the evaluation direction away from the
opposite pole. Their equality with the coefficients in the local
sphere expansion follows by locality, including the fixed chart cutoff.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem unmaskedStationaryAmplitude_contDiffAt (m : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) {e : Space (m+3)} {u : Space (m+2)}
    (he : (gnomonicChart (0 : Space (m+2)) : Space (m+3)) + e ≠ 0)
    (hu : ‖u‖ < 1) : ContDiffAt ℝ ∞ (unmaskedStationaryAmplitude m B) (e,u) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hd : ContDiffAt ℝ ∞
      (fun v : Space (m+2) => ((Real.sqrt (1-‖v‖^2/4))^m : ℂ)) u := by
    apply ContDiffAt.pow
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
        (by linarith : 1-‖u‖^2/4 ≠ 0))
  have hq := (quadraticSpherePoint_contDiffAt (hu.trans (by norm_num))).comp (e,u)
    contDiffAt_snd
  have hr := (poleRotationFormula_contDiffAt
    (gnomonicChart (0 : Space (m+2))) e (quadraticSpherePoint u) he).comp (e,u)
      (contDiffAt_fst.prodMk hq)
  exact (hd.comp (e,u) contDiffAt_snd).mul (hB.contDiffAt.comp (e,u) hr)

theorem actualStationaryCoefficient_contDiffAt (m j : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) {e : Space (m+3)}
    (he : (gnomonicChart (0 : Space (m+2)) : Space (m+3)) + e ≠ 0) :
    ContDiffAt ℝ ∞ (actualStationaryCoefficient m j B) e := by
  exact quadraticJetCoefficient_contDiffAt
    (unmaskedStationaryAmplitude_contDiffAt m hB he (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) j

theorem actualStationaryCoefficient_eq (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m j B e =
      quadraticJetCoefficient j (quadraticAmplitude m
        (fun w => B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticJetCoefficient_congr
  filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : Space (m+2)) ∈ ball 0 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hu
  simp only [unmaskedStationaryAmplitude, quadraticAmplitude, indicator_of_mem hu]
  congr 1
  congr 1
  rw [← stationaryPoleRotation_apply, ← gnomonicChart_quadraticToGnomonic hu']
  rfl

@[simp] theorem actualStationaryCoefficient_zero (m : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m 0 B e = sphereStationaryConstant (m+2) * B e := by
  rw [actualStationaryCoefficient_eq, quadraticJetCoefficient_amplitude_zero]
  change _ * B (stationaryPoleRotation e (gnomonicChart (0 : Space (m+2)))) = _
  rw [stationaryPoleRotation_pole]

/-- The actual coefficient depends only on the original amplitude near its
evaluation direction; every cutoff that is constant there is invisible. -/
theorem actualStationaryCoefficient_local (m j : ℕ) {B G : Space (m+3) → ℂ}
    (e : Sphere (m+3)) (hBG : B =ᶠ[𝓝 (e : Space (m+3))] G) :
    actualStationaryCoefficient m j B e = actualStationaryCoefficient m j G e := by
  apply quadraticJetCoefficient_congr
  let γ : Space (m+2) → Space (m+3) :=
    fun u => stationaryPoleRotation e (quadraticSpherePoint u)
  have hq0 : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  have hγ0 : γ 0 = (e : Space (m+3)) := by
    change stationaryPoleRotation e (quadraticSpherePoint 0) = _
    rw [hq0, stationaryPoleRotation_pole]
  have hγ : Filter.Tendsto γ (𝓝 (0 : Space (m+2))) (𝓝 (e : Space (m+3))) := by
    rw [← hγ0]
    exact (stationaryPoleRotation e).continuous.continuousAt.comp
      (quadraticSpherePoint_contDiffAt (u := (0 : Space (m+2))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  filter_upwards [hBG.comp_tendsto hγ] with u hu
  simp only [unmaskedStationaryAmplitude, ← stationaryPoleRotation_apply]
  rw [show B (stationaryPoleRotation e (quadraticSpherePoint u)) =
    G (stationaryPoleRotation e (quadraticSpherePoint u)) from hu]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleCutoffs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem poleCutoff_one {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : ‖x-(e : Space d)‖ ≤ 1/8) : poleCutoff e x = 1 := by
  apply (capBump (1/4) (by norm_num) e).one_of_mem_closedBall
  change dist x (e : Space d) ≤ (1/4 : ℝ)/2
  rw [dist_eq_norm]
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem poleCutoff_zero {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : 1/4 ≤ ‖x-(e : Space d)‖) : poleCutoff e x = 0 := by
  apply (capBump (1/4) (by norm_num) e).zero_of_le_dist
  simpa only [dist_eq_norm,capBump] using hx

theorem poleCutoff_support {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : poleCutoff e x ≠ 0) : ‖x-(e : Space d)‖ < 1/4 := by
  by_contra h
  exact hx (poleCutoff_zero e x (le_of_not_gt h))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleStationarySupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual support conditions for the pole expansion

Geometric support in a radius-1/4 cap implies all support conditions in
the quadratic stationary theorem. The ambient pole bump is invisible to
the actual coefficient jets at its center.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem poleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (poleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).mul hB

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FixedChartBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite derivative bounds for fixed quadratic geometry

Only compact sets inside the smooth chart are used. The chart need not
extend smoothly through its outer singularity.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_iteratedFDeriv_bound_at {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i f) K := by
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  choose A hA using fun i => hK.exists_bound_of_continuousOn (hc i)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  refine ⟨C,Finset.sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem norm_iteratedFDeriv_mul_le_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (k-i) g x‖ := by
  obtain ⟨U,hU,hxU,hfU⟩ := hf.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨V,hV,hxV,hgV⟩ := hg.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hxW : x ∈ W := ⟨hxU,hxV⟩
  have hfU' : ContDiffOn ℝ k f U := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hfU
  have hgV' : ContDiffOn ℝ k g V := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hgV
  have hfW : ContDiffOn ℝ k f W := hfU'.mono inter_subset_left
  have hgW : ContDiffOn ℝ k g W := hgV'.mono inter_subset_right
  have hh := norm_iteratedFDerivWithin_mul_le hfW hgW hW.uniqueDiffOn hxW (le_refl (k : ℕ∞ω))
  have hre (j : ℕ) (a : E → ℂ) : iteratedFDerivWithin ℝ j a W x = iteratedFDeriv ℝ j a x :=
    iteratedFDerivWithin_of_isOpen j hW hxW
  simpa only [hre] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative budget of the actual quadratic amplitude

The fixed pole cutoff and fixed quadratic geometry cost constants depending
only on the dimension and derivative order. The original symbol supplies
the entire scale power.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem mixed_product_uniform_bound_at {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (k : ℕ)
    (hfb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 2^k*A*B := by
  apply (norm_iteratedFDeriv_mul_le_at hf hg k).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb j hjk) (Nat.cast_nonneg _))
        (hgb (k-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      have hs : (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
        simpa only [one_pow,mul_one,one_mul,one_add_one_eq_two] using
          (add_pow (1 : ℝ) 1 k).symm
      rw [← Finset.sum_mul,← Finset.sum_mul,hs]

theorem poleLocalizedAmbient_uniform_budget (d K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ j (poleLocalizedAmbient e B) w‖ ≤ A*C*D^K := by
  choose P hP hPb using fun j => capBump_ambient_derivatives d j
  let Q := ∑ j ∈ Finset.range (K+1), P j*4^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  have hPQ (j : ℕ) (hj : j ≤ K) : P j*4^j ≤ Q := by
    change P j*(4 : ℝ)^j ≤ ∑ i ∈ Finset.range (K+1), P i*4^i
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hP i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*Q,by positivity,?_⟩
  intro e B hB C D hC hD hb j hj w
  have hCD : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  have hcut (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun x => (poleCutoff e x : ℂ)) w‖ ≤ Q := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((poleCutoff_contDiff e).contDiffAt (x := (w : Space d)))
      (show (i : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ poleCutoff e) w‖ ≤ Q
    rw [hn]
    apply (hPb i (1/4) (by norm_num) e w).trans
    simpa only [one_div,inv_inv] using hPQ i (hi.trans hj)
  have hBb (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i B w‖ ≤ C*D^K :=
    (hb i (hi.trans hj) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (hi.trans hj)) hC)
  have hh := mixed_product_uniform_bound_at
    ((Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).contDiffAt)
    hB.contDiffAt hQ hCD j hcut hBb
  apply hh.trans
  calc
    _ ≤ 2^K*Q*(C*D^K) := by gcongr; norm_num
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_LocalStationaryJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local mixed derivative bounds on the actual stationary chart

The chart is smooth on an open pole patch. These lemmas localize the
vertical Laplacian estimate to that patch, without extending the chart
across its singularities.
-/

namespace Falconer
open Set
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_comp_clm_at (L : E →L[ℝ] F) {f : F → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (L x)) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ L) x =
      (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hx,hfU⟩ := hf.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfu : ContDiffOn ℝ k f U := by simpa using hfU
  have hp : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfu hU.uniqueDiffOn hp.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hU hx] at he
  exact he

attribute [local instance] OAI.Falconer.instNormedSpaceRealContinuousLinearMapIdComplex_solutions_1
attribute [local instance] OAI.Falconer.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_1
theorem directionalLaplacian_contDiffAt {n : ℕ} (v : Fin n → E) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (directionalLaplacian v f) x := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := h₁.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (directionalLaplacianTrace v).contDiff.contDiffAt.comp x hd

theorem directionalLaplacian_derivative_bound_at {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (directionalLaplacian v f) x‖ ≤
      (n : ℝ) * ‖iteratedFDeriv ℝ (k+2) f x‖ := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := h₁.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ k
    ((directionalLaplacianTrace v) ∘ (fderiv ℝ (fderiv ℝ f))) x‖ ≤ _
  rw [(directionalLaplacianTrace v).iteratedFDeriv_comp_left hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  have h := (directionalLaplacianTrace v).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ f)) x)
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right (directionalLaplacianTrace_norm_le v hv)
    (norm_nonneg _))

theorem iteratedDirectionalLaplacian_contDiffAt {n : ℕ} (v : Fin n → E)
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ContDiffAt ℝ ∞ ((directionalLaplacian v)^[j] f) x := by
  induction j with
  | zero => exact hf
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      exact directionalLaplacian_contDiffAt v hj

theorem iteratedDirectionalLaplacian_derivative_bound_at {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (j k : ℕ) :
    ‖iteratedFDeriv ℝ k ((directionalLaplacian v)^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  induction j generalizing k with
  | zero => simp
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      have h₁ := directionalLaplacian_derivative_bound_at v hv
        (iteratedDirectionalLaplacian_contDiffAt v hf j) k
      have h₂ := mul_le_mul_of_nonneg_left (hj (k+2)) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      apply (h₁.trans h₂).trans_eq
      rw [show k+2+2*j = k+2*(j+1) by omega, pow_succ]
      ring

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem directionalLaplacian_vertical_at {n : ℕ} {F : P × Space n → ℂ}
    {p : P} {x : Space n} (hF : ContDiffAt ℝ ∞ F (p,x)) :
    directionalLaplacian (verticalDirections n) F (p,x) =
      Laplacian.laplacian (fun y => F (p,y)) x := by
  let g : P × Space n → ℂ := fun z => F ((p,0)+z)
  have hg : ContDiffAt ℝ ∞ g ((0 : P),x) := by
    have hc : ContDiffAt ℝ ∞ (fun z : P × Space n => (p,0)+z) ((0 : P),x) :=
      contDiffAt_const.add contDiffAt_id
    have hFx : ContDiffAt ℝ ∞ F ((p,0)+((0 : P),x)) := by simpa using hF
    have h := hFx.comp ((0 : P),x) hc
    simpa only [Function.comp_def, g] using h
  have hd := iteratedFDeriv_comp_clm_at (ContinuousLinearMap.inr ℝ P (Space n)) hg 2
  have heq : g ∘ ContinuousLinearMap.inr ℝ P (Space n) = fun y => F (p,y) := by
    funext y
    simp [g]
  rw [heq] at hd
  have hshift : iteratedFDeriv ℝ 2 g (0,x) = iteratedFDeriv ℝ 2 F (p,x) := by
    simpa only [g, Prod.mk_add_mk, add_zero, zero_add] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) 2 (p,0) (0,x))
  change iteratedFDeriv ℝ 2 (fun y => F (p,y)) x =
    (iteratedFDeriv ℝ 2 g (0,x)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ P (Space n)) at hd
  rw [hshift] at hd
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  rfl

theorem iteratedDirectionalLaplacian_vertical_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j : ℕ) {p : P} {x : Space n} (hx : (p,x) ∈ U) :
    ((directionalLaplacian (verticalDirections n))^[j] F) (p,x) =
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (p,y))) x := by
  induction j generalizing p x with
  | zero => rfl
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [directionalLaplacian_vertical_at
        (iteratedDirectionalLaplacian_contDiffAt _ ((hF _ hx).contDiffAt (hU.mem_nhds hx)) j)]
      have ht : Filter.Tendsto (fun y : Space n => (p,y)) (𝓝 x) (𝓝 (p,x)) :=
        continuous_const.continuousAt.prodMk continuous_id.continuousAt
      have he : (fun y => ((directionalLaplacian (verticalDirections n))^[j] F) (p,y))
          =ᶠ[𝓝 x] ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
            (fun y => F (p,y))) := by
        filter_upwards [ht (hU.mem_nhds hx)] with y hy
        exact hj hy
      exact (InnerProductSpace.laplacian_congr_nhds he).self_of_nhds

theorem partialIteratedLaplacian_derivative_bound_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j k : ℕ) {z : P × Space n} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ k (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) z‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F z‖ := by
  have he : (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) =ᶠ[𝓝 z]
      (directionalLaplacian (verticalDirections n))^[j] F := by
    filter_upwards [hU.mem_nhds hz] with q hq
    exact (iteratedDirectionalLaplacian_vertical_on hU hF j hq).symm
  rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
  exact iteratedDirectionalLaplacian_derivative_bound_at _ verticalDirections_norm
    ((hF z hz).contDiffAt (hU.mem_nhds hz)) j k

/-- The actual quadratic coefficient costs exactly `2j` additional
derivatives, also when differentiated in its external parameters. -/
theorem quadraticJetCoefficient_derivative_bound_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j k : ℕ) {p : P} (hp : (p,0) ∈ U) :
    ‖iteratedFDeriv ℝ k (fun q : P => quadraticJetCoefficient j (fun y => F (q,y))) p‖ ≤
      ‖sphereStationaryConstant n / ((2*Complex.I)^j * (j.factorial : ℂ))‖ *
        (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F (p,0)‖ := by
  let g : P × Space n → ℂ := fun z =>
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
      (fun y => F (z.1,y))) z.2
  let c : ℂ := sphereStationaryConstant n / ((2*Complex.I)^j * (j.factorial : ℂ))
  let L : P →L[ℝ] P × Space n := ContinuousLinearMap.inl ℝ P (Space n)
  have hg : ContDiffAt ℝ ∞ g (p,0) :=
    partialIteratedLaplacian_contDiffAt ((hF _ hp).contDiffAt (hU.mem_nhds hp)) j
  have hgc : ContDiffAt ℝ ∞ (g ∘ L) p := hg.comp p L.contDiff.contDiffAt
  have he : (fun q : P => quadraticJetCoefficient j (fun y => F (q,y))) =
      c • (g ∘ L) := by
    funext q
    rfl
  rw [he, iteratedFDeriv_const_smul_apply (hgc.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)), norm_smul]
  have hsmall : ‖iteratedFDeriv ℝ k (g ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ k g (p,0)‖ := by
    rw [iteratedFDeriv_comp_clm_at L hg k]
    have h := (iteratedFDeriv ℝ k g (p,0)).norm_compContinuousLinearMap_le
      (fun _ : Fin k => L)
    have hnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ P (Space n)
    have hp : (∏ _i : Fin k, ‖L‖) ≤ (1 : ℝ) := by
      simpa using pow_le_pow_left₀ (norm_nonneg L) hnorm k
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  calc
    _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ k g (p,0)‖ :=
      mul_le_mul_of_nonneg_left hsmall (norm_nonneg c)
    _ ≤ ‖c‖ * ((n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F (p,0)‖) :=
      mul_le_mul_of_nonneg_left (partialIteratedLaplacian_derivative_bound_on hU hF j k hp)
        (norm_nonneg c)
    _ = _ := by dsimp [c]; ring

end Parameters
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskedStationaryJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth fixed-patch extensions of actual stationary jets

The mask is one on the prepared inner cap and vanishes near the antipodal
singularity of the chosen frame. No global spherical differential operator
is assumed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem stationaryPatchMask_one (m : ℕ) (x : Space (m+3))
    (hx : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    stationaryPatchMask m x = 1 := poleCutoff_one _ x hx

theorem stationary_patch_ne_antipode (m : ℕ) {x : Space (m+3)}
    (hx : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4) :
    (gnomonicChart (0 : Space (m+2)) : Space (m+3))+x ≠ 0 := by
  intro he
  have hx' : x = -(gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he
  rw [hx',norm_sub_rev,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm] at hx
  norm_num at hx

theorem stationaryPatchMask_support (m : ℕ) :
    tsupport (stationaryPatchMask m) =
      closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4) :=
  (capBump (1/4) (by norm_num) (gnomonicChart (0 : Space (m+2)))).tsupport_eq

theorem maskedStationaryCoefficient_contDiff (m j : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (maskedStationaryCoefficient m j B) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (stationaryPatchMask m)
  · have hnear : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
      simpa only [stationaryPatchMask_support,mem_closedBall,dist_eq_norm] using hx
    exact ((Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).contDiffAt).mul
      (actualStationaryCoefficient_contDiffAt m j hB (stationary_patch_ne_antipode m hnear))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change stationaryPatchMask m y = (0 : ℝ) at hy
    simp only [maskedStationaryCoefficient,hy,Complex.ofReal_zero,zero_mul]

theorem quadraticJetCoefficient_zero_amplitude (n j : ℕ) :
    quadraticJetCoefficient j (fun _ : Space n => (0 : ℂ)) = 0 := by
  have hz : (Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ)) (fun _ => 0) =
      (fun _ => 0) := InnerProductSpace.laplacian_const
  simp only [quadraticJetCoefficient,Function.iterate_fixed hz,mul_zero]

theorem actualStationaryCoefficient_zero_amplitude (m j : ℕ) (x : Space (m+3)) :
    actualStationaryCoefficient m j (fun _ => 0) x = 0 := by
  have he : (fun u => unmaskedStationaryAmplitude m (fun _ => 0) (x,u)) =
      (fun _ : Space (m+2) => (0 : ℂ)) := by
    funext u
    simp only [unmaskedStationaryAmplitude,mul_zero]
  change quadraticJetCoefficient j _ = 0
  rw [he]
  exact quadraticJetCoefficient_zero_amplitude _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite inverse amplitudes built from the actual local jets

Each recursive amplitude is globally smooth and supported in the same fixed
pole patch. The diagonal cancellation is pointwise on the prepared inner
patch and does not assume a spherical differential-operator identity.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem localInverseAmplitude_contDiff (m : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) (j : ℕ) : ContDiff ℝ ∞ (localInverseAmplitude m B j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      simp only [localInverseAmplitude]
      exact (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m))).mul hB
    | succ j =>
      rw [localInverseAmplitude]
      apply contDiff_const.mul
      exact ContDiff.sum (fun h _ => maskedStationaryCoefficient_contDiff m (h+1)
        (ih (j-h) (by omega)))

theorem localInverseAmplitude_zero_of_mask_zero (m j : ℕ) (B : Space (m+3) → ℂ)
    (x : Space (m+3)) (hx : stationaryPatchMask m x = 0) :
    localInverseAmplitude m B j x = 0 := by
  cases j with
  | zero => simp only [localInverseAmplitude,hx,Complex.ofReal_zero,mul_zero,zero_mul]
  | succ j =>
    simp only [localInverseAmplitude,maskedStationaryCoefficient,hx,Complex.ofReal_zero,
      zero_mul,Finset.sum_const_zero,mul_zero]

theorem localInverseAmplitude_tsupport (m j : ℕ) (B : Space (m+3) → ℂ) :
    tsupport (localInverseAmplitude m B j) ⊆ tsupport (stationaryPatchMask m) := by
  apply closure_mono
  intro x hx hzero
  exact hx (localInverseAmplitude_zero_of_mask_zero m j B x hzero)

theorem localInverseAmplitude_cancellation (m k : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) :
    (∑ h ∈ Finset.range (k+1), actualStationaryCoefficient m h
      (localInverseAmplitude m B (k-h)) e) = if k = 0 then B e else 0 := by
  have hc := sphereStationaryConstant_ne_zero (m+2)
  cases k with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one,Nat.sub_self,
      actualStationaryCoefficient_zero,localInverseAmplitude,he,
      Complex.ofReal_one,mul_one,↓reduceIte]
    rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,actualStationaryCoefficient_zero,
      localInverseAmplitude,maskedStationaryCoefficient,he,Complex.ofReal_one,
      one_mul,Nat.succ_ne_zero,↓reduceIte]
    rw [← mul_assoc,mul_neg,mul_inv_cancel₀ hc,neg_one_mul]
    exact add_neg_cancel _

theorem localInverseAmplitude_cancellation_reverse (m k : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) :
    (∑ h ∈ Finset.range (k+1), actualStationaryCoefficient m (k-h)
      (localInverseAmplitude m B h) e) = if k = 0 then B e else 0 := by
  rw [← localInverseAmplitude_cancellation m k B e he,
    ← Finset.sum_range_reflect (fun h => actualStationaryCoefficient m h
      (localInverseAmplitude m B (k-h)) e) (k+1)]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  simp [Nat.sub_sub_self hh']

theorem localInverseAmplitude_triangle (m J : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) (t : ℂ) :
    (∑ j ∈ Finset.range (J+1), t^j *
      ∑ h ∈ Finset.range (J+1-j), t^h * actualStationaryCoefficient m h
        (localInverseAmplitude m B j) e) = B e := by
  have hid : (∑ j ∈ Finset.range (J+1), ∑ h ∈ Finset.range (J+1-j),
      t^(j+h)*actualStationaryCoefficient m h (localInverseAmplitude m B j) e) = B e := by
    rw [← Finset.sum_range_diag_flip]
    have hh : ∀ k ∈ Finset.range (J+1),
        (∑ j ∈ Finset.range (k+1), t^(j+(k-j))*
          actualStationaryCoefficient m (k-j) (localInverseAmplitude m B j) e) =
            t^k*(if k = 0 then B e else 0) := by
      intro k _
      rw [← localInverseAmplitude_cancellation_reverse m k B e he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Nat.add_sub_of_le hj']
    rw [Finset.sum_congr rfl hh]
    simp
  rw [← hid]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [pow_add,mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JointStationaryGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mixed bounds for the actual stationary chart

The reflection formula preserves norm even when its direction parameter is
off the sphere. This permits ambient derivatives in that parameter while
the original symbol is evaluated only on sphere points.
-/

namespace Falconer
open Set Metric
open scoped ContDiff RealInnerProductSpace

theorem poleRotationFormula_eq_reflection {n : ℕ} (p e x : Space n) :
    poleRotationFormula p e x = (ℝ ∙ (p+e)).reflection x := by
  rw [Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

theorem poleRotationFormula_norm {n : ℕ} (p e x : Space n) :
    ‖poleRotationFormula p e x‖ = ‖x‖ := by
  rw [poleRotationFormula_eq_reflection]
  exact (ℝ ∙ (p+e)).reflection.norm_map x

theorem jointStationaryRegion_isOpen (m : ℕ) : IsOpen (jointStationaryRegion m) := by
  exact (isOpen_ne_fun (continuous_const.add continuous_fst) continuous_const).inter
    (isOpen_lt continuous_snd.norm continuous_const)

theorem jointStationaryCompact_isCompact (m : ℕ) : IsCompact (jointStationaryCompact m) :=
  (isCompact_closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4)).prod
    (isCompact_closedBall (0 : Space (m+2)) 1)

theorem jointStationaryCompact_subset (m : ℕ) :
    jointStationaryCompact m ⊆ jointStationaryRegion m := by
  intro z hz
  have he : ‖z.1-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hz.1
  have hu : ‖z.2‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hz.2
  exact ⟨stationary_patch_ne_antipode m he,by linarith⟩

theorem jointStationaryChart_norm (m : ℕ)
    (z : Space (m+3) × Space (m+2)) (hz : ‖z.2‖ ≤ 2) :
    ‖jointStationaryChart m z‖ = 1 := by
  rw [jointStationaryChart,poleRotationFormula_norm]
  exact quadraticSpherePoint_norm hz

theorem unmaskedStationaryAmplitude_contDiffAt_region (m : ℕ)
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B)
    {z : Space (m+3) × Space (m+2)} (hz : z ∈ jointStationaryRegion m) :
    ContDiffAt ℝ ∞ (unmaskedStationaryAmplitude m B) z := by
  exact ((quadraticChartDensity_contDiffAt m hz.2).comp z contDiffAt_snd).mul
    (hB.contDiffAt.comp z (jointStationaryChart_contDiffAt m hz))

theorem joint_stationary_geometry_bounds (m K : ℕ) :
    ∃ Q R : ℝ, 0 ≤ Q ∧ 0 ≤ R ∧ ∀ j ≤ K, ∀ z ∈ jointStationaryCompact m,
      ‖iteratedFDeriv ℝ j (jointStationaryChart m) z‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ j (fun z : Space (m+3) × Space (m+2) =>
        quadraticChartDensity m z.2) z‖ ≤ R := by
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound_at (jointStationaryCompact_isCompact m)
    (fun z hz => jointStationaryChart_contDiffAt m (jointStationaryCompact_subset m hz)) K
  obtain ⟨R,hR,hRb⟩ := compact_iteratedFDeriv_bound_at (jointStationaryCompact_isCompact m)
    (fun z hz => (quadraticChartDensity_contDiffAt m
      (jointStationaryCompact_subset m hz).2).comp z contDiffAt_snd) K
  exact ⟨Q,R,hQ,hR,fun j hj z hz => ⟨hQb j hj z hz,hRb j hj z hz⟩⟩

/-- All mixed chart derivatives cost only their total order in the original
symbol scale. The direction parameter is differentiated in ambient space. -/
theorem joint_stationary_amplitude_budget (m K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ z ∈ jointStationaryCompact m,
        ‖iteratedFDeriv ℝ j (unmaskedStationaryAmplitude m B) z‖ ≤ A*C*D^K := by
  obtain ⟨Q,R,hQ,hR,hgeometry⟩ := joint_stationary_geometry_bounds m K
  let a : ℕ → ℝ := fun j => mixedCompositionBudget (fun _ => Q) j
  have ha (j : ℕ) : 0 ≤ a j := mixedCompositionBudget_nonneg (fun _ => hQ) j
  let H := ∑ j ∈ Finset.range (K+1), a j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => ha j)
  have haH (j : ℕ) (hj : j ≤ K) : a j ≤ H :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*R*H,by positivity,?_⟩
  intro B hB C D hC hD hb j hj z hz
  have hzU := jointStationaryCompact_subset m hz
  have hCE : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  let w : Sphere (m+3) := ⟨jointStationaryChart m z,by
    rw [mem_sphere,dist_zero_right]
    exact jointStationaryChart_norm m z hzU.2.le⟩
  have hcomp (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (B ∘ jointStationaryChart m) z‖ ≤ H*(C*D^K) := by
    have hh := mixed_composition_derivative_bound (B := fun _ => Q) (D := 1)
      (jointStationaryChart_contDiffAt m hzU)
      hB.contDiffAt hCE i
      (fun l hl => (hb l ((hl.trans hi).trans hj) w).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ((hl.trans hi).trans hj)) hC))
      (fun l _ hl => by simpa only [one_pow,mul_one] using
        (hgeometry l ((hl.trans hi).trans hj) z hz).1)
    exact hh.trans (by
      simp only [one_pow,mul_one]
      exact mul_le_mul_of_nonneg_right (haH i (hi.trans hj)) hCE)
  have hh := mixed_product_uniform_bound_at
    ((quadraticChartDensity_contDiffAt m hzU.2).comp z contDiffAt_snd)
    (hB.contDiffAt.comp z (jointStationaryChart_contDiffAt m hzU))
    hR (mul_nonneg hH hCE) j
    (fun i hi => (hgeometry i (hi.trans hj) z hz).2) hcomp
  change ‖iteratedFDeriv ℝ j (fun z => quadraticChartDensity m z.2 *
    (B ∘ jointStationaryChart m) z) z‖ ≤ _
  apply hh.trans
  calc
    _ ≤ 2^K*R*(H*(C*D^K)) := by gcongr; norm_num
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SafeStationaryChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A global smooth extension of the fixed local stationary chart

The extension equals the actual chart near every direction in the support
of the fixed patch mask. It exists only to express its finite derivatives
as globally smooth separated factors; the stationary coefficients remain
the original coefficients.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem stationarySafePoint_near {n : ℕ} (c x : Space n) (hx : ‖x-c‖ ≤ 1/2) :
    stationarySafePoint c x = x := by
  have hb : stationaryExtensionBump c x = 1 :=
    (stationaryExtensionBump c).one_of_mem_closedBall (by
      simpa only [mem_closedBall,dist_eq_norm,stationaryExtensionBump] using hx)
  simp only [stationarySafePoint,hb,one_smul,add_sub_cancel]

theorem safeStationaryChart_zero (m : ℕ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2) :
    safeStationaryChart m (e,0) = (e : Space (m+3)) := by
  have hu : ‖(0 : Space (m+2))-0‖ ≤ (1 : ℝ)/2 := by norm_num
  have hq : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  simp only [safeStationaryChart,jointStationaryChart,stationarySafePoint_near _ _ he,
    stationarySafePoint_near _ _ hu,hq,← stationaryPoleRotation_apply,stationaryPoleRotation_pole]

theorem maskedStationaryCoefficient_safe (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Space (m+3)) :
    maskedStationaryCoefficient m j B e = (stationaryPatchMask m e : ℂ)*
      quadraticJetCoefficient j (fun u => safeStationaryDensity m u*B (safeStationaryChart m (e,u))) := by
  by_cases he : stationaryPatchMask m e = 0
  · simp only [maskedStationaryCoefficient,he,Complex.ofReal_zero,zero_mul]
  · have hep : ‖e-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 := by
      exact (poleCutoff_support _ _ he).le.trans (by norm_num)
    unfold maskedStationaryCoefficient actualStationaryCoefficient
    congr 1
    apply quadraticJetCoefficient_congr
    filter_upwards [isOpen_ball.mem_nhds (show (0 : Space (m+2)) ∈ ball 0 (1/2) by
      simp only [mem_ball,dist_self]; norm_num)] with u hu
    have hu' : ‖u-(0 : Space (m+2))‖ ≤ 1/2 := by
      exact (mem_ball_iff_norm.mp hu).le
    simp only [safeStationaryDensity,safeStationaryChart,jointStationaryChart,
      stationarySafePoint_near _ e hep,stationarySafePoint_near _ u hu',
      unmaskedStationaryAmplitude,quadraticChartDensity]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetAlgebra
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebra of individual ambient mask jets

A term contains each original mask exactly once, evaluated at one smooth
angular chart point, with a fixed finite jet on each occurrence. The
coefficient contains only the fixed chart geometry. Differentiation can
therefore distribute to one mask without deleting any other occurrence.
-/

namespace Falconer
open Set
open scoped ContDiff

namespace MaskJetIndex

theorem fderiv_value {d : ℕ} (j : MaskJetIndex d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) (z v : Space d) (hv : ‖v‖ ≤ 1) :
    fderiv ℝ (j.value B) z v = (j.prepend v hv).value B z := by
  have hd := (hB.iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : ℕ∞ω)+j.order ≤ ∞)).differentiable
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (fun y => iteratedFDeriv ℝ j.order B y j.vectors) z v = _
  rw [fderiv_continuousMultilinear_apply_const_apply (hd z)]
  rfl

end MaskJetIndex

theorem complex_clm_coordinate_expansion {d : ℕ} (L : Space d →L[ℝ] ℂ) (z : Space d) :
    L z = ∑ i : Fin d, (z i : ℂ)*L ((EuclideanSpace.basisFun (Fin d) ℝ) i) := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr z)
  simpa only [map_sum,map_smul,OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr,smul_eq_mul,
    Complex.real_smul] using h.symm

theorem MaskJetIndex.fderiv_comp {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : MaskJetIndex d) {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B)
    {g : E → Space d} (hg : ContDiff ℝ ∞ g) (z v : E) :
    fderiv ℝ (fun u => j.value B (g u)) z v =
      ∑ i : Fin d, ((fderiv ℝ g z v) i : ℂ)*
        (j.prepend ((EuclideanSpace.basisFun (Fin d) ℝ) i)
          (by simp)).value B (g z) := by
  change fderiv ℝ (j.value B ∘ g) z v = _
  rw [_root_.fderiv_comp z ((j.value_contDiff hB).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
    (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt]
  change fderiv ℝ (j.value B) (g z) (fderiv ℝ g z v) = _
  rw [complex_clm_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [j.fderiv_value hB (g z) _ (by simp)]

namespace MaskJetTerm
variable {ι X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem value_contDiff (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) : ContDiff ℝ ∞ (T.value B x) :=
  T.coefficient_smooth.mul (contDiff_prod (fun i _ =>
    ((T.jet i).value_contDiff (hB i x)).comp T.point_smooth))

theorem derivativeTerm_order [DecidableEq ι] (T : MaskJetTerm ι d E) (v : E)
    (a : Unit ⊕ (ι × Fin d)) : (T.derivativeTerm v a).order ≤ T.order+1 := by
  rcases a with a | ⟨i,j⟩
  · exact Nat.le_succ _
  · have he : (fun l => ((Function.update T.jet i
        ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp))) l).order) =
        Function.update (fun l => (T.jet l).order) i ((T.jet i).order+1) := by
      funext l
      by_cases hl : l = i
      · subst l; simp [MaskJetIndex.prepend]
      · simp [Function.update_of_ne hl]
    change (∑ l, ((Function.update T.jet i _ l)).order) ≤ (∑ l, (T.jet l).order)+1
    rw [he,Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
    have hs := Finset.add_sum_erase Finset.univ (fun l => (T.jet l).order) (Finset.mem_univ i)
    omega

private theorem fderiv_product [DecidableEq ι] (f : ι → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (z v : E) :
    fderiv ℝ (fun z => ∏ i, f i z) z v =
      ∑ i, (∏ j ∈ Finset.univ.erase i, f j z)*fderiv ℝ (f i) z v := by
  have he := congrArg (fun L : E →L[ℝ] ℂ => L v)
    (fderiv_finsetProd (u := Finset.univ) (x := z)
      (fun i _ => ((hf i).differentiable (by simp)).differentiableAt))
  simpa only [sum_apply,smul_apply,smul_eq_mul] using he

private theorem derivativeTerm_value_right [DecidableEq ι]
    (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ) (v : E)
    (i : ι) (j : Fin d) (x : X) (z : E) :
    (T.derivativeTerm v (.inr (i,j))).value B x z =
      T.coefficient z*((fderiv ℝ T.point z v) j : ℂ)*
      ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp)).value
        (B i x) (T.point z)*
      ∏ l ∈ Finset.univ.erase i, (T.jet l).value (B l x) (T.point z) := by
  have he : (fun l => ((Function.update T.jet i
      ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp))) l).value
        (B l x) (T.point z)) =
      Function.update (fun l => (T.jet l).value (B l x) (T.point z)) i
        (((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp)).value
          (B i x) (T.point z)) := by
    funext l
    by_cases hl : l = i
    · subst l; simp
    · simp [Function.update_of_ne hl]
  dsimp only [derivativeTerm]
  change (T.coefficient z*((fderiv ℝ T.point z v) j : ℂ))*_ = _
  rw [he,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
  ring

theorem derivative_value [DecidableEq ι] (T : MaskJetTerm ι d E)
    (B : ι → X → Space d → ℂ) (hB : ∀ i x, ContDiff ℝ ∞ (B i x))
    (v : E) (x : X) (z : E) :
    ∑ a : Unit ⊕ (ι × Fin d), (T.derivativeTerm v a).value B x z =
      fderiv ℝ (T.value B x) z v := by
  let f : ι → E → ℂ := fun i z => (T.jet i).value (B i x) (T.point z)
  have hf (i : ι) : ContDiff ℝ ∞ (f i) :=
    ((T.jet i).value_contDiff (hB i x)).comp T.point_smooth
  have hprod : ContDiff ℝ ∞ (fun z => ∏ i, f i z) := contDiff_prod (fun i _ => hf i)
  change _ = fderiv ℝ (fun z => T.coefficient z*∏ i, f i z) z v
  rw [fderiv_fun_mul (T.coefficient_smooth.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
    (hprod.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul,Fintype.sum_sum_type,Fintype.sum_unique,
    Fintype.sum_prod_type]
  rw [fderiv_product f hf z v]
  change (fderiv ℝ T.coefficient z v)*(∏ i, f i z)+_ = _
  have hsum : (∑ i : ι, ∑ j : Fin d,
      (T.derivativeTerm v (.inr (i,j))).value B x z) =
      T.coefficient z*∑ i, (∏ l ∈ Finset.univ.erase i, f l z)*fderiv ℝ (f i) z v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MaskJetIndex.fderiv_comp (T.jet i) (hB i x) T.point_smooth z v]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [derivativeTerm_value_right]
    dsimp only [f]
    ring
  rw [hsum]
  ring

end MaskJetTerm
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseMaskJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse as finite products of individual mask jets

The construction follows the already proved safe-chart inverse recursion.
All mask occurrences survive in every term, and the total order charged to
them is at most twice the inverse index.
-/

namespace Falconer
open scoped ContDiff

attribute [instance] MaskJetExpansion.finite

namespace MaskJetExpansion
variable {ι : Type} {X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem value_contDiff (S : MaskJetExpansion ι d E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) :
    ContDiff ℝ ∞ (S.value B x) :=
  ContDiff.sum (fun a _ => (S.term a).value_contDiff B hB x)

theorem derivative_value [DecidableEq ι] (S : MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (hB : ∀ i x, ContDiff ℝ ∞ (B i x))
    (v : E) (x : X) (z : E) :
    (S.derivative v).value B x z = fderiv ℝ (S.value B x) z v := by
  change (∑ a : S.index × (Unit ⊕ (ι × Fin d)),
    ((S.term a.1).derivativeTerm v a.2).value B x z) = _
  rw [Fintype.sum_prod_type]
  simp_rw [MaskJetTerm.derivative_value _ _ hB]
  change _ = fderiv ℝ (fun z => ∑ a : S.index, (S.term a).value B x z) z v
  rw [fderiv_fun_sum (fun a _ =>
    ((S.term a).value_contDiff B hB x).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.differentiableAt)]
  simp only [sum_apply]

theorem HasOrder.mulFixed {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).HasOrder K := h

theorem HasOrder.pullback {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).HasOrder K := h

theorem sum_hasOrder {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    {K : ℕ} (h : ∀ j, (S j).HasOrder K) : (sum S).HasOrder K :=
  fun a => h a.1 a.2

theorem HasOrder.derivative [DecidableEq ι] {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (v : E) : (S.derivative v).HasOrder (K+1) :=
  fun a => ((S.term a.1).derivativeTerm_order v a.2).trans (Nat.add_le_add_right (h a.1) 1)

theorem laplacian_value [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (z : E) :
    (S.laplacian v).value B x z = directionalLaplacian v (S.value B x) z := by
  rw [laplacian,sum_value,directionalLaplacian,directionalLaplacianTrace_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [derivative_value _ _ hB]
  have he : (S.derivative (v j)).value B x = fun z => fderiv ℝ (S.value B x) z (v j) :=
    funext (derivative_value S B hB (v j) x)
  rw [he]
  have hdf : Differentiable ℝ (fderiv ℝ (S.value B x)) :=
    ((S.value_contDiff B hB x).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := ((ContinuousLinearMap.apply ℝ ℂ (v j)).hasFDerivAt.comp z
    hdf.differentiableAt.hasFDerivAt).fderiv
  have hv := congrArg (fun T : E →L[ℝ] ℂ => T (v j)) hc
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hv

theorem HasOrder.laplacian [DecidableEq ι] {n : ℕ} {S : MaskJetExpansion ι d E}
    {K : ℕ} (h : S.HasOrder K) (v : Fin n → E) : (S.laplacian v).HasOrder (K+2) :=
  sum_hasOrder _ (fun j => (h.derivative (v j)).derivative (v j))

theorem iteratedLaplacian_value [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (j : ℕ) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) :
    (S.iteratedLaplacian v j).value B x = (directionalLaplacian v)^[j] (S.value B x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply']
    funext z
    rw [laplacian_value _ _ _ hB]
    change directionalLaplacian v ((S.iteratedLaplacian v j).value B x) z = _
    rw [ih]

theorem HasOrder.iteratedLaplacian [DecidableEq ι] {n : ℕ} {S : MaskJetExpansion ι d E}
    {K : ℕ} (h : S.HasOrder K) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).HasOrder (K+2*j) := by
  induction j with
  | zero => simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_zero_apply,mul_zero,Nat.add_zero] using h
  | succ j ih =>
    have hh := ih.laplacian v
    rw [show K+2*j+2 = K+2*(j+1) by omega] at hh
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using hh

theorem stationaryJet_value [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Space (m+3)) :
    (S.stationaryJet m j).value B x e = maskedStationaryCoefficient m j (S.value B x) e := by
  rw [maskedStationaryCoefficient_safe]
  rw [stationaryJet,mulFixed_value,pullback_value,iteratedLaplacian_value _ _ _ _ hB]
  rw [iteratedDirectionalLaplacian_vertical]
  · simp only [mulFixed_value,pullback_value,quadraticJetCoefficient,
      SmoothSeparation.stationaryJetMultiplier,SmoothSeparation.stationaryJointDensity]
    ring
  · exact value_contDiff _ B hB x

theorem HasOrder.stationaryJet [DecidableEq ι] {m j K : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} (h : S.HasOrder K) :
    (S.stationaryJet m j).HasOrder (K+2*j) := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem inverse_value [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Space (m+3)) :
    (S.inverse m j).value B x e = localInverseAmplitude m (S.value B x) j e := by
  induction j using Nat.strong_induction_on generalizing e with
  | h j ih =>
    cases j with
    | zero => rw [inverse,mulFixed_value,localInverseAmplitude]
    | succ j =>
      rw [inverse,mulFixed_value,sum_value,localInverseAmplitude]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro h _
      rw [stationaryJet_value _ _ _ _ hB]
      have he : (S.inverse m (j-h)).value B x = localInverseAmplitude m (S.value B x) (j-h) := by
        funext z
        exact ih (j-h) (by have hh := h.isLt; omega) z
      rw [he]

theorem HasOrder.inverse [DecidableEq ι] {m K : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} (h : S.HasOrder K) (j : ℕ) :
    (S.inverse m j).HasOrder (K+2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply HasOrder.mulFixed
      apply sum_hasOrder
      intro k
      have hk := (ih (j-k) (by have hi := k.isLt; omega)).stationaryJet (j := (k:ℕ)+1)
      rwa [show K+2*(j-k)+2*((k:ℕ)+1) = K+2*(j+1) by have hi := k.isLt; omega] at hk

omit [Fintype ι] in
theorem HasPointAt.mulFixed {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).HasPointAt z p := h

omit [Fintype ι] in
theorem HasPointAt.pullback {S : MaskJetExpansion ι d E} {g : H → E}
    {z : H} {p : Space d} (h : S.HasPointAt (g z) p) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).HasPointAt z p := h

omit [Fintype ι] in
theorem sum_hasPointAt {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    {z : E} {p : Space d} (h : ∀ j, (S j).HasPointAt z p) :
    (sum S).HasPointAt z p := fun a => h a.1 a.2

theorem HasPointAt.derivative [DecidableEq ι] {S : MaskJetExpansion ι d E}
    {z : E} {p : Space d} (h : S.HasPointAt z p) (v : E) :
    (S.derivative v).HasPointAt z p := by
  intro a
  rcases a with ⟨a,b⟩
  rcases b with b | ⟨i,j⟩ <;> exact h a

theorem HasPointAt.laplacian [DecidableEq ι] {n : ℕ}
    {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (v : Fin n → E) : (S.laplacian v).HasPointAt z p :=
  sum_hasPointAt _ (fun j => (h.derivative (v j)).derivative (v j))

theorem HasPointAt.iteratedLaplacian [DecidableEq ι] {n : ℕ}
    {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).HasPointAt z p := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem HasPointAt.stationaryJet [DecidableEq ι] {m j : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} {p : Space d}
    {e : Sphere (m+3)} (h : S.HasPointAt e p)
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2) :
    (S.stationaryJet m j).HasPointAt e p := by
  have hchart : S.HasPointAt (safeStationaryChart m (e,0)) p := by
    simpa only [safeStationaryChart_zero m e he] using h
  unfold MaskJetExpansion.stationaryJet
  have hT := (hchart.pullback (g := safeStationaryChart m) (z := (e,0))
    (safeStationaryChart_contDiff m)).mulFixed
      (SmoothSeparation.stationaryJointDensity m)
      (SmoothSeparation.stationaryJointDensity_contDiff m)
  have hU := (hT.iteratedLaplacian (verticalDirections (m+2)) j).pullback
    (g := fun z : Space (m+3) => (z,(0 : Space (m+2)))) (z := (e : Space (m+3)))
    (contDiff_id.prodMk contDiff_const)
  exact hU.mulFixed (SmoothSeparation.stationaryJetMultiplier m j)
    (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem HasPointAt.inverse [DecidableEq ι] {m : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} {p : Space d} {e : Sphere (m+3)}
    (h : S.HasPointAt e p)
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2)
    (j : ℕ) : (S.inverse m j).HasPointAt e p := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply HasPointAt.mulFixed
      apply sum_hasPointAt
      intro k
      exact (ih (j-k) (by have hk := k.isLt; omega)).stationaryJet he

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorInverseJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Individual radius normalization in the actual inverse expansion

Every mask retains its own radius and derivative order. The extracted
coefficient costs only the largest inverse radius to the total order.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

theorem value_ofReal (j : MaskJetIndex d) (f : Space d → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => (f w : ℂ)) z =
      ((iteratedFDeriv ℝ j.order f z) j.vectors : ℝ) := by
  change (iteratedFDeriv ℝ j.order (Complex.ofRealCLM ∘ f) z) j.vectors = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  rfl

end MaskJetIndex

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ComplexMaskJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized jets of the complex angular multiplier

The multiplier is treated as an additional label. Its new derivative
order is charged to the inverse, and its available smoothness budget is
reduced by exactly that order.
-/

namespace Falconer.MaskJetIndex
open Set
open scoped ContDiff
variable {d : ℕ}

theorem value_const_mul (j : MaskJetIndex d) (c : ℂ) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => c*f w) z = c*j.value f z := by
  change (iteratedFDeriv ℝ j.order (fun w => c • f w) z) j.vectors = _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt]
  rfl

theorem value_real_smul (j : MaskJetIndex d) (c : ℝ) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => c • f w) z = c • j.value f z := by
  simp only [Complex.real_smul]
  exact j.value_const_mul c f hf z

theorem scaledValue_ofReal (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.scaledValue r (fun w => (f w : ℂ)) z = j.normalizedValue r f z := by
  rw [scaledValue,value_ofReal j f hf z]
  simp only [normalizedValue,Complex.real_smul,Complex.ofReal_mul]

theorem value_eq_inv_radius_scaled (j : MaskJetIndex d) (r : ℝ) (hr : r ≠ 0)
    (f : Space d → ℂ) (z : Space d) :
    j.value f z = (((r⁻¹)^j.order : ℝ) : ℂ) * j.scaledValue r f z := by
  simp only [scaledValue,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,← mul_pow,
    inv_mul_cancel₀ hr,one_pow,Complex.ofReal_one,one_mul]

private theorem norm_iteratedFDeriv_nested (f : Space d → ℂ)
    (k t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ =
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [← norm_iteratedFDeriv_fderiv,fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,ih]
    rw [show k+1+t = k+(t+1) by omega]

private theorem jetEvaluation_norm_le (j : MaskJetIndex d) : ‖jetEvaluation j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L j.vectors‖ ≤ 1*‖L‖
  have hp : (∏ i, ‖j.vectors i‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => j.norm_vectors i)
  simpa only [one_mul] using (L.le_opNorm j.vectors).trans
    (mul_le_of_le_one_right (norm_nonneg L) hp)

theorem norm_iteratedFDeriv_value_le (j : MaskJetIndex d) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (j.value f) z‖ ≤ ‖iteratedFDeriv ℝ (j.order+t) f z‖ := by
  have hfd : ContDiff ℝ ∞ (iteratedFDeriv ℝ j.order f) :=
    hf.iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ t (jetEvaluation j ∘ iteratedFDeriv ℝ j.order f) z‖ ≤ _
  rw [(jetEvaluation j).iteratedFDeriv_comp_left hfd.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  calc
    _ ≤ ‖jetEvaluation j‖ * ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ j.order f) z‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ j.order f) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (jetEvaluation_norm_le j)
    _ = _ := norm_iteratedFDeriv_nested f j.order t z

theorem norm_iteratedFDeriv_scaledValue_le (j : MaskJetIndex d) {r : ℝ} (hr : 0 ≤ r)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (j.scaledValue r f) z‖ ≤
      r^j.order * ‖iteratedFDeriv ℝ (j.order+t) f z‖ := by
  change ‖iteratedFDeriv ℝ t (fun z => r^j.order • j.value f z) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((j.value_contDiff hf).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr _)]
  exact mul_le_mul_of_nonneg_left (j.norm_iteratedFDeriv_value_le f hf t z) (pow_nonneg hr _)

theorem angular_budget_shift (j : MaskJetIndex d) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) {D : ℝ} (hD : 1 ≤ D) {L : ℕ} (hj : j.order ≤ L)
    (hbudget : ∀ k ≤ L, ∀ w : Sphere d, ‖iteratedFDeriv ℝ k f w‖ ≤ D^k) :
    ∀ t ≤ L-j.order, ∀ w : Sphere d,
      ‖iteratedFDeriv ℝ t (j.scaledValue D⁻¹ f) w‖ ≤ D^t := by
  intro t ht w
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  calc
    _ ≤ (D⁻¹)^j.order * ‖iteratedFDeriv ℝ (j.order+t) f w‖ :=
      j.norm_iteratedFDeriv_scaledValue_le (inv_nonneg.mpr hD0.le) f hf t w
    _ ≤ (D⁻¹)^j.order * D^(j.order+t) :=
      mul_le_mul_of_nonneg_left (hbudget _ (by omega) w) (pow_nonneg (inv_nonneg.mpr hD0.le) _)
    _ = D^t := by
      rw [pow_add,← mul_assoc,← mul_pow,inv_mul_cancel₀ hD0.ne',one_pow,one_mul]

end Falconer.MaskJetIndex

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_AmbientChartBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient symbol bounds imply the ordinary rotated chart bounds

Only derivatives of the original symbol evaluated at sphere points are
used. The one-coordinate curve has a fixed, rotation-independent budget.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem rotatedChartCurve_derivative_scale (n K : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ K →
        ‖iteratedFDeriv ℝ k (rotatedChartCurve e y) u‖ ≤ q^k := by
  obtain ⟨q,hq,hqb⟩ := tangent_line_derivative_scale (E := Space (n+2)) K
  refine ⟨q,hq,?_⟩
  intro e y hy u hu k hk hkK
  have he : rotatedChartCurve e y = e ∘
      normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
    funext t
    simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
  rw [he,e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hqb _ _ _ (chartPole_norm n) (chartAxis_norm n)
    (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
    (by simpa only [transverseLift_norm] using hy) u hu k hk hkK

theorem ambient_symbol_rotated_chart_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ B : Space (n+2) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ K,
        ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => B w) y) u‖ ≤ H*C*D^k := by
  obtain ⟨q,hq,hqb⟩ := rotatedChartCurve_derivative_scale n K
  let a : ℕ → ℝ := fun k => mixedCompositionBudget (fun _ => 1) k*q^k
  have ha (k : ℕ) : 0 ≤ a k := mul_nonneg
    (mixedCompositionBudget_nonneg (fun _ => zero_le_one) k)
    (pow_nonneg (zero_le_one.trans hq) k)
  let H := ∑ k ∈ Finset.range (K+1), a k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => ha k)
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hb e y hy u hu k hk
  let w : Sphere (n+2) := ⟨rotatedChartCurve e y u,by
    rw [mem_sphere,dist_zero_right,rotatedChartCurve_norm]⟩
  have hCE : 0 ≤ C*D^k := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) k)
  have hh := mixed_composition_derivative_bound (B := fun _ => 1) (D := q)
    (rotatedChartCurve_contDiff e y).contDiffAt hB.contDiffAt hCE k
    (fun j hj => (hb j (hj.trans hk) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hj) hC))
    (fun j hj hjk => by simpa only [one_mul] using hqb e y hy u hu j hj (hjk.trans hk))
  have he : rotatedChartAmplitude e (fun w => B w) y = B ∘ rotatedChartCurve e y := rfl
  rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply hh.trans
  have haH : a k ≤ H := Finset.single_le_sum (fun i _ => ha i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  calc
    _ = a k*C*D^k := by dsimp [a]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haH hC)
      (pow_nonneg (zero_le_one.trans hD) k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the finite stationary remainders

These are the exact scale calculations in `osc:stationary`. The ratio
`A^2 / Λ` pays for each extra stationary term. The remaining `d+2`
derivatives are absorbed using `A ≤ R^2`. No stationary-phase estimate is
assumed here.
-/

namespace Falconer

theorem stationary_remainder_ratio (J d : ℕ) (A Λ : ℝ) :
    (Λ⁻¹)^J * A^(2*J+d+2) = (A^2/Λ)^J * A^(d+2) := by
  rw [show 2*J+d+2 = 2*J+(d+2) by omega, pow_add, pow_mul, div_pow, div_eq_mul_inv]
  ring

theorem stationary_remainder_scale (J d : ℕ) {R A Λ κ : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hΛ : 0 < Λ) (hupper : A ≤ R^2)
    (hratio : A^2/Λ ≤ R^(-κ)) :
    (Λ⁻¹)^J * A^(2*J+d+2) ≤ R^(-κ*(J:ℝ)+2*(d+2)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [stationary_remainder_ratio]
  calc
    _ ≤ (R^(-κ))^J * (R^2)^(d+2) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hratio J)
        (pow_le_pow_left₀ hA hupper (d+2)) (by positivity) (by positivity)
    _ = R^(-κ*(J:ℝ)+2*(d+2)) := by
      rw [← Real.rpow_mul_natCast hRp.le, ← pow_mul,
        ← Real.rpow_natCast, ← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

/-- A single finite order, independent of the large scale, achieves any
prescribed negative power. This also permits fixed derivative overhead. -/
theorem exists_stationary_remainder_order (d : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ R A Λ : ℝ,
      1 ≤ R → 0 ≤ A → 0 < Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) →
      (Λ⁻¹)^J * A^(2*J+d+2) ≤ R^(-T) := by
  obtain ⟨J,hJ⟩ := exists_nat_gt ((T+2*(d+2))/κ)
  refine ⟨J+1,by omega,?_⟩
  intro R A Λ hR hA hΛ hupper hratio
  apply (stationary_remainder_scale (J+1) d hR hA hΛ hupper hratio).trans
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hJ' : T+2*(d+2) < (J:ℝ)*κ := (div_lt_iff₀ hκ).mp hJ
  push_cast
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedInverseFactors
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size-one endpoint factors with the exact total derivative cost

Positive upper sizes are selected before the scale label. Division by
those sizes retains all zero sets and chart bounds; their product costs
only the sum of the original endpoint derivative orders.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem ChartSymbolControl.normalized {n K : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D a : ℝ}
    (h : ChartSymbolControl K b B D) (ha : 0 < a) (hBa : B ≤ a) (hD : 0 ≤ D) :
    ChartSymbolControl K (normalizedEndpoint a b) 1 D := by
  have hn : ‖(a⁻¹ : ℝ)‖ = a⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr ha.le)
  refine ⟨measurable_const.mul h.measurable,?_,?_,?_⟩
  · intro x w
    simp only [normalizedEndpoint,norm_mul,Complex.norm_real,hn]
    exact (mul_le_mul_of_nonneg_left ((h.bound x w).trans hBa)
      (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')
  · intro x e y
    exact contDiff_const.mul (h.smooth x e y)
  · intro e k hk x y hy u hu
    change ‖iteratedDeriv k (fun v => (a⁻¹ : ℝ)*rotatedChartAmplitude e (b x) y v) u‖ ≤ _
    rw [iteratedDeriv_const_mul _ ((h.smooth x e y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
      norm_mul,Complex.norm_real,hn]
    calc
      _ ≤ a⁻¹*(B*D^k) := mul_le_mul_of_nonneg_left
        (h.derivative e k hk x y hy u hu) (inv_nonneg.mpr ha.le)
      _ ≤ a⁻¹*(a*D^k) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hBa (pow_nonneg hD _)) (inv_nonneg.mpr ha.le)
      _ = 1*D^k := by rw [← mul_assoc,inv_mul_cancel₀ ha.ne']

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularJetSymbol
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-budget angular jets as normalized recursive multipliers

A fixed chart constant is selected before the angular multiplier or its
previous derivative order. Taking a jet consumes that exact order from
the ambient budget; normalization does not enlarge the derivative scale.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

/-- One fixed normalization controls both ambient and rotated chart jets. -/
theorem ambient_angular_normalization (n K : ℕ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ B : Space (n+2) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 < C → 1 ≤ D →
      (∀ t ≤ K, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ContDiff ℝ ∞ (normalizedAngular (H*C) B) ∧
      (∀ t ≤ K, ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (normalizedAngular (H*C) B) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) => normalizedAngular (H*C) B w) 1 D := by
  obtain ⟨H₀,hH₀,hchart⟩ := ambient_symbol_rotated_chart_budget n K
  let H := H₀+1
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH₀H : H₀ ≤ H := by dsimp [H]; linarith
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hb
  have hHC : 0 < H*C := mul_pos (zero_lt_one.trans_le hH) hC
  have hCHC : C ≤ H*C := le_mul_of_one_le_left hC.le hH
  have hfactor : (H*C)⁻¹*C ≤ 1 := by
    calc
      _ ≤ (H*C)⁻¹*(H*C) :=
        mul_le_mul_of_nonneg_left hCHC (inv_nonneg.mpr hHC.le)
      _ = 1 := inv_mul_cancel₀ hHC.ne'
  have hnormalized : ContDiff ℝ ∞ (normalizedAngular (H*C) B) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (n+2) => (H*C)⁻¹)).smul hB
  refine ⟨hnormalized,?_,?_⟩
  · intro t ht w
    change ‖iteratedFDeriv ℝ t (fun z => (H*C)⁻¹ • B z) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hB.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hHC.le)]
    calc
      _ ≤ (H*C)⁻¹*(C*D^t) :=
        mul_le_mul_of_nonneg_left (hb t ht w) (inv_nonneg.mpr hHC.le)
      _ = ((H*C)⁻¹*C)*D^t := by ring
      _ ≤ 1*D^t := mul_le_mul_of_nonneg_right hfactor
        (pow_nonneg (zero_le_one.trans hD) t)
      _ = _ := one_mul _
  · have hraw : ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) => B w) (H*C) D := by
      refine ⟨hB.continuous.measurable.comp (continuous_subtype_val.comp continuous_snd).measurable,
        ?_,?_,?_⟩
      · intro x w
        have h := hb 0 (Nat.zero_le K) w
        simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at h
        exact h.trans hCHC
      · intro x e y
        exact hB.comp (rotatedChartCurve_contDiff e y)
      · intro e t ht x y hy u hu
        exact (hchart B hB C D hC.le hD hb e y hy u hu t ht).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH₀H hC.le)
            (pow_nonneg (zero_le_one.trans hD) t))
    have hn := hraw.normalized hHC le_rfl (zero_le_one.trans hD)
    have he : (fun (_ : Space (n+2)) (w : Sphere (n+2)) =>
        normalizedAngular (H*C) B w) =
        normalizedEndpoint (H*C) (fun (_ : Space (n+2)) (w : Sphere (n+2)) => B w) := by
      funext x w
      simp only [normalizedEndpoint,normalizedAngular,Complex.real_smul]
    rw [he]
    exact hn

/-- The initial multiplier needs exactly `p+K` derivatives for a new order-`p`
jet to remain in the recursive class with `K` derivatives. -/
theorem angular_jet_symbol (n K : ℕ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ (L : ℕ) (j : MaskJetIndex (n+2))
      (f : Space (n+2) → ℂ), ContDiff ℝ ∞ f → ∀ D : ℝ, 1 ≤ D →
      j.order+K ≤ L →
      (∀ t ≤ L, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t f w‖ ≤ D^t) →
      ContDiff ℝ ∞ (normalizedAngular H (j.scaledValue D⁻¹ f)) ∧
      (∀ t ≤ K, ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (normalizedAngular H (j.scaledValue D⁻¹ f)) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) =>
          normalizedAngular H (j.scaledValue D⁻¹ f) w) 1 D := by
  obtain ⟨H,hH,hbound⟩ := ambient_angular_normalization n K
  refine ⟨H,hH,?_⟩
  intro L j f hf D hD hLK hb
  have hjet : ∀ t ≤ K, ∀ w : Sphere (n+2),
      ‖iteratedFDeriv ℝ t (j.scaledValue D⁻¹ f) w‖ ≤ 1*D^t := by
    intro t ht w
    simpa only [one_mul] using j.angular_budget_shift f hf hD (by omega) hb
      t (by omega) w
  simpa only [mul_one] using hbound (j.scaledValue D⁻¹ f)
    (j.scaledValue_contDiff D⁻¹ f hf) 1 D zero_lt_one hD hjet

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the actual anchored mask jets

The spatial variable only selects one of finitely many Borel anchor cells.
Within such a cell all angular jets are derivatives of its fixed smooth mask.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
attribute [local instance] Classical.propDecidable

 theorem normalizedDescriptorJet_anchor_sum {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      ∑ p ∈ cubePaths d (descriptorAnchor b),
        if x ∈ (Q.descendant p).carrier then
          (((descriptorMaskRadius N σ b)^k *
            (iteratedFDeriv ℝ k
              (capCutoffAmbient (descriptorMaskRadius N σ b)
                (descriptorMaskRadius_pos N σ b) S
                (descriptorGoodDirections Q ρ m N σ J (i+1) p b)) w) v : ℝ) : ℂ)
        else 0 := by
  classical
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    rw [Finset.sum_eq_single p]
    · have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
        ((mem_cubePaths d _ p).mp hp) hxp)
      simp only [normalizedDescriptorJet,he,ite_eq_left hxp]
    · intro q hq hqp
      have hdis := Q.descendants_disjoint
        (((mem_cubePaths d _ q).mp hq).trans ((mem_cubePaths d _ p).mp hp).symm) hqp
      exact ite_eq_right (fun hq => Set.disjoint_left.mp hdis hq hxp)
    · exact fun hn => (hn hp).elim
  · have hz : normalizedDescriptorJet Q ρ m N σ J i b S k v x w = 0 := by
      simp only [normalizedDescriptorJet,descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx,
        iteratedFDeriv_fun_zero,Pi.zero_apply,zero_apply,mul_zero,Complex.ofReal_zero]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro p _
    exact ite_eq_right (fun hp => hx (Q.descendant_subset p hp))

 theorem normalizedDescriptorJet_measurable {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Sphere d → Fin k → Space d) (hv : Measurable v) :
    Measurable (fun z : Space d × Sphere d =>
      normalizedDescriptorJet Q ρ m N σ J i b S k (v z.2) z.1 z.2) := by
  classical
  simp_rw [normalizedDescriptorJet_anchor_sum]
  apply Finset.measurable_sum
  intro p _
  let f := capCutoffAmbient (descriptorMaskRadius N σ b)
    (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b)
  have hf : ContDiff ℝ ∞ f := capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _
  have he : Continuous (fun z : Space d × (Fin k → Space d) =>
      (iteratedFDeriv ℝ k f z.1) z.2) :=
    ((hf.continuous_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp continuous_fst).eval continuous_snd
  have hm : Measurable (fun w : Sphere d =>
      (((descriptorMaskRadius N σ b)^k * (iteratedFDeriv ℝ k f w) (v w) : ℝ) : ℂ)) :=
    ((he.measurable.comp (continuous_subtype_val.measurable.prodMk hv)).const_mul _).complex_ofReal
  exact (hm.comp measurable_snd).ite
    ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

 theorem descriptorJetProduct_measurable {d : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) :
    Measurable (Function.uncurry (descriptorJetProduct Q ρ m N σ J i F b S k v)) := by
  apply Finset.measurable_prod
  intro j hj
  exact normalizedDescriptorJet_measurable Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) (hv j hj)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetRemoval
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetBound_one_le (d K : ℕ) : 1 ≤ descriptorJetBound d K :=
  (normalizedDescriptorJet_order_bound d K).choose_spec.1

theorem descriptorJetProduct_norm_le {d K : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hsep : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (horder : (∑ j ∈ F, k j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) (x : Space d) (w : Sphere d) :
    ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ (descriptorJetBound d K)^K := by
  have hA := descriptorJetBound_one_le d K
  have hbound := (normalizedDescriptorJet_order_bound d K).choose_spec.2
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, (descriptorJetBound d K)^(k j) := by
      apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = (descriptorJetBound d K)^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k _
    _ ≤ (descriptorJetBound d K)^K := pow_le_pow_right₀ hA horder

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FactorizedAngularState
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem multiplier_measurable (f : DescriptorJetSymbol n K L F D) (A : ℝ) :
    Measurable (Function.uncurry (f.multiplier A)) :=
  (f.spatial_measurable.comp measurable_fst).mul measurable_const |>.mul
    f.angular_control.measurable

 theorem multiplier_bound (f : DescriptorJetSymbol n K L F D) {A : ℝ} (hA : 0 < A)
    (x : Space (n+2)) (w : Sphere (n+2)) : ‖f.multiplier A x w‖ ≤ A⁻¹ := by
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    _ ≤ (1*A⁻¹)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_nonneg.mpr hA.le))
      (f.angular_control.bound x w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem value_measurable (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    Measurable (Function.uncurry (f.value Q ρ m N σ J i S A)) := by
  have hp := descriptorJetProduct_measurable Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun _ _ => measurable_const)
  exact hp.mul (f.multiplier_measurable A)

 theorem value_norm_le (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x : Space (n+2)) (w : Sphere (n+2)) :
    ‖f.value Q ρ m N σ J i S A x w‖ ≤ ((descriptorJetBound (n+2) K)^K)*A⁻¹ := by
  rw [value,norm_mul]
  exact mul_le_mul
    (descriptorJetProduct_norm_le Q ρ m N σ J i F id S
      (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)
      hsep f.order_le (fun b _ _ => (f.jet b).norm_vectors) x w)
    (f.multiplier_bound hA x w) (norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global original-point factors for the inverse expansion

Every inverse coefficient vanishes off the fixed patch. Thus its individual
mask jets can be evaluated at the original sphere point globally, and each
resulting descriptor factor retains every original angular good condition.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]

theorem stationaryJet_coefficient_eq_zero (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (a : (S.stationaryJet m j).index)
    (e : Space (m+3)) (he : stationaryPatchMask m e = 0) :
    ((S.stationaryJet m j).term a).coefficient e = 0 := by
  change SmoothSeparation.stationaryJetMultiplier m j e * _ = 0
  rw [show SmoothSeparation.stationaryJetMultiplier m j e = 0 by
    simp only [SmoothSeparation.stationaryJetMultiplier,he,Complex.ofReal_zero,zero_mul],zero_mul]

theorem inverse_coefficient_eq_zero (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (a : (S.inverse m j).index)
    (e : Space (m+3)) (he : stationaryPatchMask m e = 0) :
    ((S.inverse m j).term a).coefficient e = 0 := by
  revert a
  cases j with
  | zero =>
    rw [MaskJetExpansion.inverse]
    intro a
    change ((sphereStationaryConstant (m+2))⁻¹*(stationaryPatchMask m e : ℂ))*_ = 0
    simp only [he,Complex.ofReal_zero,mul_zero,zero_mul]
  | succ j =>
    rw [MaskJetExpansion.inverse]
    intro a
    change -(sphereStationaryConstant (m+2))⁻¹ *
      (((S.inverse m (j-a.1)).stationaryJet m ((a.1:ℕ)+1)).term a.2).coefficient e = 0
    rw [stationaryJet_coefficient_eq_zero _ _ _ _ e he,mul_zero]

end MaskJetExpansion

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family for the inverse's geometric coefficients

Changing which mask receives a derivative changes its jet index, but not
the smooth coefficient or evaluation point. Collapse all mask choices to
one label to obtain a coefficient family independent of the list length.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι τ : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [Fintype ι] [Fintype τ] in
theorem GeometryCoveredBy.mulFixed {S : MaskJetExpansion ι d E}
    {T : MaskJetExpansion τ d E} (h : S.GeometryCoveredBy T)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).GeometryCoveredBy (T.mulFixed c hc) := by
  intro a
  obtain ⟨b,hc',hp⟩ := h a
  refine ⟨b,?_,hp⟩
  change (fun z => c z*(S.term a).coefficient z) = _
  rw [hc']
  rfl

omit [Fintype ι] [Fintype τ] in
theorem GeometryCoveredBy.pullback {S : MaskJetExpansion ι d E}
    {T : MaskJetExpansion τ d E} (h : S.GeometryCoveredBy T)
    (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).GeometryCoveredBy (T.pullback g hg) := by
  intro a
  obtain ⟨b,hc,hp⟩ := h a
  refine ⟨b,?_,?_⟩
  · change (S.term a).coefficient ∘ g = _
    rw [hc]
    rfl
  · change (S.term a).point ∘ g = _
    rw [hp]
    rfl

omit [Fintype ι] [Fintype τ] in
theorem sum_geometryCoveredBy {J : Type} [Fintype J]
    (S : J → MaskJetExpansion ι d E) (T : J → MaskJetExpansion τ d E)
    (h : ∀ j, (S j).GeometryCoveredBy (T j)) : (sum S).GeometryCoveredBy (sum T) := by
  rintro ⟨j,a⟩
  obtain ⟨b,hc,hp⟩ := h j a
  exact ⟨⟨j,b⟩,hc,hp⟩

theorem GeometryCoveredBy.derivative [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : E) :
    (S.derivative v).GeometryCoveredBy (T.derivative v) := by
  classical
  rintro ⟨a,c⟩
  obtain ⟨b,hc,hp⟩ := h a
  cases c with
  | inl c =>
    refine ⟨(b,.inl c),?_,?_⟩
    · change (fun z => fderiv ℝ (S.term a).coefficient z v) = _
      rw [hc]
      rfl
    · exact hp
  | inr c =>
    rcases c with ⟨i,j⟩
    refine ⟨(b,.inr (Classical.choice inferInstance,j)),?_,?_⟩
    · change (fun z => (S.term a).coefficient z *
        ((fderiv ℝ (S.term a).point z v) j : ℂ)) = _
      rw [hc,hp]
      rfl
    · exact hp

theorem GeometryCoveredBy.laplacian [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {n : ℕ} {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : Fin n → E) :
    (S.laplacian v).GeometryCoveredBy (T.laplacian v) :=
  sum_geometryCoveredBy _ _ (fun j => (h.derivative (v j)).derivative (v j))

theorem GeometryCoveredBy.iteratedLaplacian [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {n : ℕ} {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).GeometryCoveredBy (T.iteratedLaplacian v j) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem GeometryCoveredBy.stationaryJet [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {T : MaskJetExpansion τ d (Space (m+3))} (h : S.GeometryCoveredBy T) (j : ℕ) :
    (S.stationaryJet m j).GeometryCoveredBy (T.stationaryJet m j) := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem GeometryCoveredBy.inverse [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {T : MaskJetExpansion τ d (Space (m+3))} (h : S.GeometryCoveredBy T) (j : ℕ) :
    (S.inverse m j).GeometryCoveredBy (T.inverse m j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse,MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse,MaskJetExpansion.inverse]
      apply GeometryCoveredBy.mulFixed
      apply sum_geometryCoveredBy
      intro k
      exact (ih (j-k) (by have hk := k.isLt; omega)).stationaryJet _

omit [Fintype ι] [Fintype τ] in
theorem coefficient_derivatives_bounded_on (T : MaskJetExpansion τ d E)
    (k : ℕ) {s : Set E} (hs : IsCompact s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a z, z ∈ s →
      ‖iteratedFDeriv ℝ k (T.term a).coefficient z‖ ≤ C := by
  classical
  have hbound (a : T.index) := hs.exists_bound_of_continuousOn
    (((T.term a).coefficient_smooth.iteratedFDeriv_right (m := ∞) (i := k)
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.continuousOn)
  choose c hc using hbound
  refine ⟨∑ a : T.index, |c a|,Finset.sum_nonneg (fun a _ => abs_nonneg _),?_⟩
  intro a z hz
  exact (hc a z hz).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun b _ => abs_nonneg (c b)) (Finset.mem_univ a)))

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetSeed
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Starting the inverse expansion with existing individual mask jets

Previously charged derivatives remain in their original occurrences. The
new inverse adds at most twice its index to the total order, and radius
normalization cancels every previously charged power exactly.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H X : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [DecidableEq ι] in
theorem seed_value (k : ι → MaskJetIndex d) (B : ι → X → Space d → ℂ)
    (x : X) (z : Space d) :
    (seed k).value B x z = ∏ i, (k i).value (B i x) z := by
  change (∑ _a : Unit, (1 : ℂ)*∏ i, (k i).value (B i x) z) = _
  simp

omit [DecidableEq ι] in
theorem seed_hasOrder (k : ι → MaskJetIndex d) :
    (seed k).HasOrder (∑ i, (k i).order) := fun _ => le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem seed_hasPointAt (k : ι → MaskJetIndex d) (z : Space d) :
    (seed k).HasPointAt z z := fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem seed_geometryCoveredBy_unit (k : ι → MaskJetIndex d) :
    (seed k).GeometryCoveredBy (product : MaskJetExpansion Unit d (Space d)) :=
  fun _ => ⟨(),rfl,rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem seed_ordersExtend (k : ι → MaskJetIndex d) : (seed k).OrdersExtend k :=
  fun _ _ => le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem OrdersExtend.mulFixed {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).OrdersExtend k := h

omit [Fintype ι] [DecidableEq ι] in
theorem OrdersExtend.pullback {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).OrdersExtend k := h

omit [Fintype ι] [DecidableEq ι] in
theorem sum_ordersExtend {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    (k : ι → MaskJetIndex d) (h : ∀ j, (S j).OrdersExtend k) :
    (sum S).OrdersExtend k := fun a => h a.1 a.2

theorem OrdersExtend.derivative {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (v : E) : (S.derivative v).OrdersExtend k := by
  rintro ⟨a,b⟩ i
  cases b with
  | inl b => exact h a i
  | inr b =>
    rcases b with ⟨l,t⟩
    change (k i).order ≤ (Function.update (S.term a).jet l _ i).order
    by_cases hi : i = l
    · subst i
      rw [Function.update_self]
      exact (h a l).trans (Nat.le_succ _)
    · rw [Function.update_of_ne hi]
      exact h a i

theorem OrdersExtend.laplacian {n : ℕ} {S : MaskJetExpansion ι d E}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (v : Fin n → E) :
    (S.laplacian v).OrdersExtend k :=
  sum_ordersExtend _ _ (fun j => (h.derivative (v j)).derivative (v j))

theorem OrdersExtend.iteratedLaplacian {n : ℕ} {S : MaskJetExpansion ι d E}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).OrdersExtend k := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem OrdersExtend.stationaryJet {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (j : ℕ) :
    (S.stationaryJet m j).OrdersExtend k := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem OrdersExtend.inverse {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (j : ℕ) :
    (S.inverse m j).OrdersExtend k := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply OrdersExtend.mulFixed
      apply sum_ordersExtend
      intro l
      exact (ih (j-l) (by have hl := l.isLt; omega)).stationaryJet _

theorem seed_inverse_added_order (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) ≤ 2*j := by
  have hbase := (seed_ordersExtend k).inverse j a
  have htotal := (seed_hasOrder k).inverse j a
  have heq :
      (∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) +
        (∑ i, (k i).order) = (((seed k).inverse m j).term a).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hbase i)
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem radius_power_cancel {r : ℝ} (hr : r ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    r^a * (r⁻¹)^b = (r⁻¹)^(b-a) := by
  calc
    _ = r^a * ((r⁻¹)^a * (r⁻¹)^(b-a)) := by
      rw [← pow_add,Nat.add_sub_of_le hab]
    _ = (r*r⁻¹)^a * (r⁻¹)^(b-a) := by rw [mul_pow]; ring
    _ = _ := by rw [mul_inv_cancel₀ hr,one_pow,one_mul]

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SeededInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse acting on already normalized individual jets

Only the additional derivative orders enter the extracted radius weight.
The formula also permits a complex angular multiplier as a separate label.
-/

namespace Falconer
open scoped ContDiff

namespace MaskJetIndex

theorem value_scaled_input {d : ℕ} (j : MaskJetIndex d) (k : ℕ)
    (hkj : k ≤ j.order) (r : ℝ) (hr : r ≠ 0) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => r^k • f w) z =
      (((r⁻¹)^(j.order-k) : ℝ) : ℂ) * j.scaledValue r f z := by
  rw [j.value_real_smul (r^k) f hf z,j.value_eq_inv_radius_scaled r hr f z,
    Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    MaskJetExpansion.radius_power_cancel hr hkj]

end MaskJetIndex

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_seed_term_normalized (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (seed k).inverse m j
    ∀ a : T.index,
      (T.term a).value (fun i x z => (r i)^(k i).order • B i x z) x e =
        (T.term a).coefficient e * (seededRadiusWeight m j k r a : ℂ) *
          ∏ i, ((T.term a).jet i).scaledValue (r i) (B i x) e := by
  intro T a
  by_cases he : stationaryPatchMask m e = 0
  · have hc : (T.term a).coefficient e = 0 := inverse_coefficient_eq_zero m j (seed k) a e he
    simp only [MaskJetTerm.value,hc,zero_mul]
  · have hnear : ‖(e : Space (m+3))-
        (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 :=
      (poleCutoff_support _ _ he).le.trans (by norm_num)
    have hp : (T.term a).point e = (e : Space (m+3)) :=
      ((seed_hasPointAt k (e : Space (m+3))).inverse hnear j a)
    have hi (i : ι) :
        ((T.term a).jet i).value (fun z => (r i)^(k i).order • B i x z) e =
          (((r i)⁻¹^(((T.term a).jet i).order-(k i).order) : ℝ) : ℂ) *
            ((T.term a).jet i).scaledValue (r i) (B i x) e :=
      MaskJetIndex.value_scaled_input _ _ ((seed_ordersExtend k).inverse j a i)
        (r i) (hr i) (B i x) (hB i x) e
    unfold MaskJetTerm.value
    rw [hp]
    simp_rw [hi]
    have hw : (∏ i, (((r i)⁻¹^(((T.term a).jet i).order-(k i).order) : ℝ) : ℂ)) =
        (seededRadiusWeight m j k r a : ℂ) := by
      exact_mod_cast (rfl :
      (∏ i, (r i)⁻¹^(((T.term a).jet i).order-(k i).order)) =
        seededRadiusWeight m j k r a)
    rw [Finset.prod_mul_distrib,hw,mul_assoc]

/-- Exact global expansion with every old radius normalization cancelled. -/
theorem localInverseAmplitude_seeded_jets (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (seed k).inverse m j
    localInverseAmplitude m (fun z => ∏ i, (k i).scaledValue (r i) (B i x) z) j e =
      ∑ a : T.index, (T.term a).coefficient e * (seededRadiusWeight m j k r a : ℂ) *
        ∏ i, ((T.term a).jet i).scaledValue (r i) (B i x) e := by
  intro T
  let C : ι → X → Space (m+3) → ℂ := fun i x z => (r i)^(k i).order • B i x z
  have hC (i : ι) (x : X) : ContDiff ℝ ∞ (C i x) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (m+3) => (r i)^(k i).order)).smul (hB i x)
  have hseed : (seed k).value C x = fun z => ∏ i, (k i).scaledValue (r i) (B i x) z := by
    funext z
    rw [seed_value]
    apply Finset.prod_congr rfl
    intro i _
    exact (k i).value_real_smul _ _ (hB i x) z
  have hv := inverse_value m j (seed k) C hC x e
  rw [hseed] at hv
  rw [← hv]
  apply Finset.sum_congr rfl
  intro a _
  exact inverse_seed_term_normalized m j k r hr B hB x e a

/-- The smooth coefficients are drawn from a fixed finite geometric family,
independent of the number and previous orders of the masks. -/
theorem inverse_seed_geometryCoveredBy_unit (m j : ℕ) (k : ι → MaskJetIndex (m+3)) :
    ((seed k).inverse m j).GeometryCoveredBy
      ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) :=
  (seed_geometryCoveredBy_unit k).inverse j

omit [Fintype ι] [DecidableEq ι] in
theorem inverse_seed_coefficient_derivatives (m j t : ℕ)
    {s : Set (Space (m+3))} (hs : IsCompact s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3)) (a : ((seed k).inverse m j).index),
        ∀ z ∈ s, ‖iteratedFDeriv ℝ t (((seed k).inverse m j).term a).coefficient z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coefficient_derivatives_bounded_on
    ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) t hs
  refine ⟨C,hC,?_⟩
  intro ι _ _ k a z hz
  obtain ⟨b,hcoeff,_⟩ := inverse_seed_geometryCoveredBy_unit m j k a
  rw [hcoeff]
  exact hbound b z hz

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_InverseAngularSymbol
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual inverse coefficients preserve the finite angular symbol budget

The geometric coefficient and the newly differentiated multiplier are
normalized by one constant chosen before all descriptor lists and scales.
The derivative scale stays fixed; only the consumed order is removed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

/-- Simultaneous bounds for all required derivatives of every geometric
coefficient, independent of the descriptor labels and initial orders. -/
theorem inverse_seed_coefficient_budget (m j K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3))
        (a : ((MaskJetExpansion.seed k).inverse m j).index),
      ∀ t ≤ K, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ t (((MaskJetExpansion.seed k).inverse m j).term a).coefficient w‖ ≤ C := by
  classical
  have hs : IsCompact (Sphere (m+3)) := isCompact_sphere (0 : Space (m+3)) 1
  choose c hc hb using fun t : Fin (K+1) =>
    MaskJetExpansion.inverse_seed_coefficient_derivatives m j t.val hs
  let C := 1+∑ t : Fin (K+1), c t
  have hsum : 0 ≤ ∑ t : Fin (K+1), c t := Finset.sum_nonneg (fun t _ => hc t)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro ι _ _ k a t ht w
  let q : Fin (K+1) := ⟨t,Nat.lt_succ_of_le ht⟩
  have hsingle : c q ≤ ∑ t : Fin (K+1), c t :=
    Finset.single_le_sum (fun t _ => hc t) (Finset.mem_univ q)
  exact (hb q ι k a w w.property).trans (by dsimp [C]; linarith)

/-- This is the angular multiplier appearing in an actual separated inverse
term. Taking order `p` requires exactly `p+K` derivatives of the old multiplier. -/
theorem inverse_angular_symbol (m j K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3))
        (a : ((MaskJetExpansion.seed k).inverse m j).index)
        (p : MaskJetIndex (m+3)) (L : ℕ) (f : Space (m+3) → ℂ),
      ContDiff ℝ ∞ f → ∀ D : ℝ, 1 ≤ D → p.order+K ≤ L →
      (∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t f w‖ ≤ D^t) →
      let g := fun z => (((MaskJetExpansion.seed k).inverse m j).term a).coefficient z *
        p.scaledValue D⁻¹ f z
      ContDiff ℝ ∞ (normalizedAngular A g) ∧
      (∀ t ≤ K, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ t (normalizedAngular A g) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (m+3)) (w : Sphere (m+3)) => normalizedAngular A g w) 1 D := by
  obtain ⟨C,hC,hcoeff⟩ := inverse_seed_coefficient_budget m j K
  obtain ⟨H,hH,hnormalize⟩ := ambient_angular_normalization (m+1) K
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hpow : 1 ≤ (2 : ℝ)^K := one_le_pow₀ (by norm_num)
  have hP : 1 ≤ (2 : ℝ)^K*C :=
    (show 1 = (1:ℝ)*1 by ring).le.trans (mul_le_mul hpow hC (by norm_num) (by positivity))
  have hA : 1 ≤ H*((2 : ℝ)^K*C) :=
    (show 1 = (1:ℝ)*1 by ring).le.trans (mul_le_mul hH hP (by norm_num) (by positivity))
  refine ⟨H*((2 : ℝ)^K*C),hA,?_⟩
  intro ι _ _ k a p L f hf D hD hLK hb g
  have hg : ContDiff ℝ ∞ g :=
    (((MaskJetExpansion.seed k).inverse m j).term a).coefficient_smooth.mul
      (p.scaledValue_contDiff D⁻¹ f hf)
  have hp := p.angular_budget_shift f hf hD (by omega) hb
  have hbudget : ∀ t ≤ K, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ t g w‖ ≤ ((2 : ℝ)^K*C)*D^t := by
    intro t ht w
    have hprod := mixed_product_uniform_bound_at
      ((((MaskJetExpansion.seed k).inverse m j).term a).coefficient_smooth.contDiffAt)
      ((p.scaledValue_contDiff D⁻¹ f hf).contDiffAt) hC0.le
      (pow_nonneg (zero_le_one.trans hD) t) t
      (fun l hl => hcoeff ι k a l (hl.trans ht) w)
      (fun l hl => (hp l (by omega) w).trans (pow_le_pow_right₀ hD hl))
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ht) hC0.le)
      (pow_nonneg (zero_le_one.trans hD) t))
  exact hnormalize g hg ((2 : ℝ)^K*C) D (zero_lt_one.trans_le hP) hD hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_InverseSphereFubini
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair and sphere integration of one inverse term

The spatial inverse power is separated after exchanging the sphere and
original endpoint integrations. All measures on the endpoints remain the
original restrictions; the Fourier multipliers have modulus one.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatial_inverse_sphere_joint_integrable
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    Integrable (fun p : Sphere d × (Space d × Space d) =>
      (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
        (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
          (b p.2.1 p.1*star (c p.2.2 p.1)))) ((sphereMeasure d).prod (μ.prod ν)) := by
  let K : Sphere d × (Space d × Space d) → ℂ := fun p =>
    (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
      (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
        (b p.2.1 p.1*star (c p.2.2 p.1)))
  have hK : Measurable K := by
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp
        (((measurable_snd.fst.dist measurable_snd.snd).div_const s).pow_const j).inv
    · apply Measurable.mul
      · fun_prop
      · exact (hb.comp (measurable_snd.fst.prodMk measurable_fst)).mul
          (continuous_star.measurable.comp (hc.comp (measurable_snd.snd.prodMk measurable_fst)))
  have hbound : ∀ᵐ p ∂(sphereMeasure d).prod (μ.prod ν), ‖K p‖ ≤ (δ^j)⁻¹*(B*C) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsep] with p hp
    have hp0 : 0 ≤ dist p.2.1 p.2.2/s := (hδ.trans_le hp).le
    have hpower : ((dist p.2.1 p.2.2/s)^j)⁻¹ ≤ (δ^j)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hδ j)
        (pow_le_pow_left₀ hδ.le hp j)
    have hphase : ‖Complex.exp
        (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [K,norm_mul,hphase,one_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hp0 j))]
    exact mul_le_mul hpower (mul_le_mul (hbB _ _) (hcC _ _) (norm_nonneg _) hB)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.mpr (pow_nonneg hδ.le j))
  exact Integrable.of_bound hK.aestronglyMeasurable ((δ^j)⁻¹*(B*C)) hbound

theorem spatial_inverse_sphere_term_integrable
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    Integrable (fun z : Space d × Space d =>
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d) (μ.prod ν) := by
  simpa only [integral_const_mul] using
    (spatial_inverse_sphere_joint_integrable δ hδ j s μ ν hsep b c hb hc hB hbB hcC r).integral_prod_right

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskedJetBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact derivative cost of the local stationary coefficients

The actual coefficient of order `j` costs `2*j` derivatives. The fixed
patch mask extends it smoothly to the whole ambient space without changing
that scale exponent.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem actualStationaryCoefficient_uniform_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ e : Space (m+3),
        ‖e-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 →
        ‖iteratedFDeriv ℝ k (actualStationaryCoefficient m j B) e‖ ≤ A*C*D^(r+2*j) := by
  obtain ⟨H,hH,hHb⟩ := joint_stationary_amplitude_budget m (r+2*j)
  let a := ‖sphereStationaryConstant (m+2) /
    ((2*Complex.I)^j * (j.factorial : ℂ))‖ * ((m+2 : ℕ) : ℝ)^j
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
  refine ⟨a*H,mul_nonneg ha hH,?_⟩
  intro B hB C D hC hD hder k hk e he
  have heK : (e,(0 : Space (m+2))) ∈ jointStationaryCompact m := by
    constructor
    · simpa only [mem_closedBall,dist_eq_norm] using he
    · simp
  have hb := quadraticJetCoefficient_derivative_bound_on
    (jointStationaryRegion_isOpen m)
    (fun z hz => (unmaskedStationaryAmplitude_contDiffAt_region m hB hz).contDiffWithinAt)
    j k (jointStationaryCompact_subset m heK)
  change ‖iteratedFDeriv ℝ k (actualStationaryCoefficient m j B) e‖ ≤ _ at hb
  have hh := hHb B hB C D hC hD hder (k+2*j) (by omega) (e,0) heK
  apply (hb.trans (mul_le_mul_of_nonneg_left hh ha)).trans_eq
  dsimp [a]
  ring

theorem stationaryPatchMask_uniform_budget (m r : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ k ≤ r, ∀ x : Space (m+3),
      ‖iteratedFDeriv ℝ k (fun x => (stationaryPatchMask m x : ℂ)) x‖ ≤ Q := by
  choose P hP hPb using fun j => capBump_ambient_derivatives (m+3) j
  let Q := ∑ j ∈ Finset.range (r+1), P j*(4 : ℝ)^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  refine ⟨Q,hQ,?_⟩
  intro k hk x
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((stationaryPatchMask_contDiff m).contDiffAt (x := x))
    (show (k : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘ stationaryPatchMask m) x‖ ≤ _
  rw [hn]
  apply (hPb k (1/4) (by norm_num) (gnomonicChart (0 : Space (m+2))) x).trans
  simp only [one_div,inv_inv]
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- This global bound is suitable for iterating the inverse recurrence.
Only the original symbol's derivatives at sphere points are needed. -/
theorem maskedStationaryCoefficient_uniform_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ x : Space (m+3),
        ‖iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x‖ ≤ A*C*D^(r+2*j) := by
  obtain ⟨H,hH,hHb⟩ := actualStationaryCoefficient_uniform_budget m j r
  obtain ⟨Q,hQ,hQb⟩ := stationaryPatchMask_uniform_budget m r
  refine ⟨2^r*Q*H,by positivity,?_⟩
  intro B hB C D hC hD hder k hk x
  by_cases hx : x ∈ tsupport (stationaryPatchMask m)
  · have he : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
      simpa only [stationaryPatchMask_support,mem_closedBall,dist_eq_norm] using hx
    have hE : 0 ≤ H*C*D^(r+2*j) := by positivity
    have hh := mixed_product_uniform_bound_at
      ((Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).contDiffAt)
      (actualStationaryCoefficient_contDiffAt m j hB (stationary_patch_ne_antipode m he))
      hQ hE k (fun l hl => hQb l (hl.trans hk) x)
      (fun l hl => hHb B hB C D hC hD hder l (hl.trans hk) x he)
    change ‖iteratedFDeriv ℝ k (fun y => (stationaryPatchMask m y : ℂ)*
      actualStationaryCoefficient m j B y) x‖ ≤ _
    apply hh.trans
    calc
      _ ≤ 2^r*Q*(H*C*D^(r+2*j)) := by gcongr; norm_num
      _ = _ := by ring
  · have he : maskedStationaryCoefficient m j B =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change stationaryPatchMask m y = (0 : ℝ) at hy
      simp only [maskedStationaryCoefficient,hy,Complex.ofReal_zero,zero_mul]
    have hz : iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x = 0 := by
      simpa using (he.iteratedFDeriv ℝ k).self_of_nhds
    rw [hz,norm_zero]
    positivity

/-- A common constant retains each derivative's own scale power. This is
the form used by the triangular inverse recursion. -/
theorem maskedStationaryCoefficient_scaled_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ x : Space (m+3),
        ‖iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x‖ ≤ A*C*D^(k+2*j) := by
  choose A hA hAb using fun k => maskedStationaryCoefficient_uniform_budget m j k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hder k hk x
  have hh := hAb k B hB C D hC hD
    (fun l hl => hder l (by omega)) k le_rfl x
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAH hC) (pow_nonneg (zero_le_one.trans hD) _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative inverse amplitudes

The inverse coefficient of order `j` loses exactly `2*j` derivatives. Its
derivative bounds are asserted on sphere points, the set used by every
subsequent stationary chart.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem localInverseAmplitude_zero_budget (m r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (localInverseAmplitude m B 0) w‖ ≤ A*C*D^k := by
  choose A hA hAb using fun k => poleLocalizedAmbient_uniform_budget (m+3) k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  let c := (sphereStationaryConstant (m+2))⁻¹
  refine ⟨‖c‖*H,mul_nonneg (norm_nonneg _) hH,?_⟩
  intro B hB C D hC hD hb k hk w
  let e := gnomonicChart (0 : Space (m+2))
  have he : localInverseAmplitude m B 0 = c • poleLocalizedAmbient e B := by
    funext x
    simp only [localInverseAmplitude,Pi.smul_apply,smul_eq_mul,poleLocalizedAmbient,
      stationaryPatchMask,c,e]
    ring
  rw [he,iteratedFDeriv_const_smul_apply
    ((poleLocalizedAmbient_contDiff e hB).contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),norm_smul]
  have hh := hAb k e B hB C D hC hD (fun l hl => hb l (hl.trans hk)) k le_rfl w
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  apply (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
  calc
    _ ≤ ‖c‖*(H*C*D^k) := by gcongr
    _ = _ := by ring

theorem localInverseAmplitude_scaled_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (localInverseAmplitude m B j) w‖ ≤ A*C*D^(k+2*j) := by
  induction j using Nat.strong_induction_on generalizing r with
  | h j ih =>
    cases j with
    | zero => simpa using localInverseAmplitude_zero_budget m r
    | succ j =>
      choose A hA hAb using fun h : ℕ =>
        ih (j-h) (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self j)) (r+2*(h+1))
      choose M hM hMb using fun h : ℕ => maskedStationaryCoefficient_scaled_budget m (h+1) r
      let S := ∑ h ∈ Finset.range (j+1), M h*A h
      have hS : 0 ≤ S := Finset.sum_nonneg (fun h _ => mul_nonneg (hM h) (hA h))
      let c := (sphereStationaryConstant (m+2))⁻¹
      refine ⟨‖c‖*S,mul_nonneg (norm_nonneg _) hS,?_⟩
      intro B hB C D hC hD hb k hk w
      let F : Space (m+3) → ℂ := fun x => ∑ h ∈ Finset.range (j+1),
        maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h)) x
      have hF : ContDiff ℝ ∞ F := ContDiff.sum (fun h _ =>
        maskedStationaryCoefficient_contDiff m (h+1) (localInverseAmplitude_contDiff m hB (j-h)))
      have he : localInverseAmplitude m B (j+1) = (-c) • F := by
        funext x
        rw [localInverseAmplitude]
        rfl
      rw [he,iteratedFDeriv_const_smul_apply (hF.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),norm_smul,norm_neg]
      have hsum : iteratedFDeriv ℝ k F w = ∑ h ∈ Finset.range (j+1),
          iteratedFDeriv ℝ k
            (maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h))) w :=
        iteratedFDeriv_fun_sum_apply (fun h _ =>
          ((maskedStationaryCoefficient_contDiff m (h+1)
            (localInverseAmplitude_contDiff m hB (j-h))).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)
      rw [hsum]
      have hterm (h : ℕ) (hh : h ∈ Finset.range (j+1)) :
          ‖iteratedFDeriv ℝ k
            (maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h))) w‖ ≤
            M h*A h*C*D^(k+2*(j+1)) := by
        have hhj : h ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
        have hinput := hAb h B hB C D hC hD (fun l hl v => hb l (by omega) v)
        have hC' : 0 ≤ A h*C*D^(2*(j-h)) :=
          mul_nonneg (mul_nonneg (hA h) hC) (pow_nonneg (zero_le_one.trans hD) _)
        have hshift : ∀ l ≤ r+2*(h+1), ∀ v : Sphere (m+3),
            ‖iteratedFDeriv ℝ l (localInverseAmplitude m B (j-h)) v‖ ≤
              (A h*C*D^(2*(j-h)))*D^l := by
          intro l hl v
          apply (hinput l hl v).trans_eq
          rw [pow_add]
          ring
        have hbound := hMb h (localInverseAmplitude m B (j-h))
          (localInverseAmplitude_contDiff m hB (j-h))
          (A h*C*D^(2*(j-h))) D hC' hD hshift k hk w
        apply hbound.trans_eq
        calc
          _ = M h*A h*C*(D^(2*(j-h))*D^(k+2*(h+1))) := by ring
          _ = _ := by
            rw [← pow_add,show 2*(j-h)+(k+2*(h+1)) = k+2*(j+1) by omega]
      have ht := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      apply (mul_le_mul_of_nonneg_left ht (norm_nonneg c)).trans_eq
      have hfactor : (∑ h ∈ Finset.range (j+1), M h*A h*C*D^(k+2*(j+1))) =
          S*C*D^(k+2*(j+1)) := by rw [← Finset.sum_mul,← Finset.sum_mul]
      rw [hfactor]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_InverseSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse amplitudes have no incoming-pole contribution

Their fixed patch support places the opposite prepared direction outside
their support. Locality of the actual stationary coefficients then removes
all incoming coefficients, without a differential-operator assumption.
-/

namespace Falconer
open Set
open scoped Topology

theorem prepared_direction_opposite_far (m : ℕ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    1/4 < ‖-(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ := by
  let p : Space (m+3) := gnomonicChart (0 : Space (m+2))
  have htwo : ‖(p-(e : Space (m+3)))+((e : Space (m+3))+p)‖ = 2 := by
    have heq : (p-(e : Space (m+3)))+((e : Space (m+3))+p) = (2 : ℝ) • p := by module
    rw [heq,norm_smul]
    change ‖(2 : ℝ)‖*‖(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ = 2
    rw [sphere_norm]
    norm_num
  have ht := norm_add_le (p-(e : Space (m+3))) ((e : Space (m+3))+p)
  rw [htwo,norm_sub_rev p (e : Space (m+3))] at ht
  have hn : ‖-(e : Space (m+3))-p‖ = ‖(e : Space (m+3))+p‖ := by
    rw [show -(e : Space (m+3))-p = -((e : Space (m+3))+p) by abel,norm_neg]
  change 1/4 < ‖-(e : Space (m+3))-p‖
  rw [hn]
  change ‖(e : Space (m+3))-p‖ ≤ 1/8 at he
  linarith

theorem localInverseAmplitude_antipodal_coefficient_zero (m j h : ℕ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    actualStationaryCoefficient m h (antipodalConjugate (localInverseAmplitude m B j)) e = 0 := by
  have hfar := prepared_direction_opposite_far m e he
  have hout : -(e : Space (m+3)) ∉ tsupport (localInverseAmplitude m B j) := by
    intro hm
    have hc := localInverseAmplitude_tsupport m j B hm
    rw [stationaryPatchMask_support,Metric.mem_closedBall,dist_eq_norm] at hc
    exact (not_le.mpr hfar) hc
  have hz := notMem_tsupport_iff_eventuallyEq.mp hout
  have hneg : Filter.Tendsto (fun x : Space (m+3) => -x)
      (𝓝 (e : Space (m+3))) (𝓝 (-(e : Space (m+3)))) :=
    continuous_neg.continuousAt
  have heq : antipodalConjugate (localInverseAmplitude m B j) =ᶠ[𝓝 (e : Space (m+3))]
      (fun _ => 0) := by
    filter_upwards [hz.comp_tendsto hneg] with x hx
    change localInverseAmplitude m B j (-x) = 0 at hx
    simp only [antipodalConjugate,hx,star_zero]
  rw [actualStationaryCoefficient_local m h e heq]
  exact actualStationaryCoefficient_zero_amplitude m h e

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outgoing inverse expansion on the prepared patch

The finite inverse amplitudes remove the outgoing coefficient series.
Their fixed patch support removes every incoming coefficient. All errors
have the same total frequency order and the same derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem stationary_weight_eq (Λ : ℝ) (j : ℕ) :
    ((Λ^(-(j : ℝ)) : ℝ) : ℂ) = ((Λ : ℂ)⁻¹)^j := by
  simp only [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,Complex.ofReal_inv,
    Complex.ofReal_pow,inv_pow]

theorem stationary_weight_mul {Λ : ℝ} (hΛ : 0 < Λ) {J j : ℕ} (hj : j ≤ J) :
    Λ^(-(j : ℝ))*Λ^(-((J-j : ℕ) : ℝ)) = Λ^(-(J : ℝ)) := by
  rw [← Real.rpow_add hΛ,← neg_add,← Nat.cast_add,Nat.add_sub_of_le hj]

theorem inverse_direct_sum (m J : ℕ) (Λ : ℝ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    (∑ j ∈ Finset.range (J+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
      directStationarySum m (J+1-j) Λ (localInverseAmplitude m B j) e) = B e := by
  simpa only [directStationarySum,stationary_weight_eq] using
    localInverseAmplitude_triangle m J B e (stationaryPatchMask_one m e he) ((Λ : ℂ)⁻¹)

theorem sphere_inverse_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)),
      ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseSphereSum m J Λ B e -
        Complex.exp (Complex.I*(Λ : ℂ))*B e‖ ≤
        A*Λ^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
  choose F hF hFb using fun k => sphere_stationary_expansion hgnomonic hquadratic m (k+1) (by omega)
  choose U hU hUb using fun j => localInverseAmplitude_scaled_budget m j
    (2*(J-j+1)+(m+2)+1)
  let A := ∑ j ∈ Finset.range (J+1), F (J-j)*U j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => mul_nonneg (hF (J-j)) (hU j))
  refine ⟨A,hA,?_⟩
  intro e he B hB C D hC hD hb Λ hΛ
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  let E : ℕ → ℂ := fun j => ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
    (p*sphereOscillation Λ e (fun w => localInverseAmplitude m B j w)-
      z*directStationarySum m (J+1-j) Λ (localInverseAmplitude m B j) e)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (J+1)) :
      ‖E j‖ ≤ F (J-j)*U j*Λ^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
    have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hN : J-j+1 = J+1-j := by omega
    have hder := hUb j B hB C D hC hD (fun l hl w => hb l (by omega) w)
    have hCj : 0 ≤ U j*C*D^(2*j) :=
      mul_nonneg (mul_nonneg (hU j) hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hinput : ∀ l ≤ 2*(J-j+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ l (localInverseAmplitude m B j) w‖ ≤ (U j*C*D^(2*j))*D^l := by
      intro l hl w
      apply (hder l hl w).trans_eq
      rw [pow_add]
      ring
    have hf := hFb (J-j) e (localInverseAmplitude m B j)
      (localInverseAmplitude_contDiff m hB j) (U j*C*D^(2*j)) D hCj hD hinput Λ hΛ
    have hz : directStationarySum m (J-j+1) Λ
        (antipodalConjugate (localInverseAmplitude m B j)) e = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [localInverseAmplitude_antipodal_coefficient_zero m j k B e he,mul_zero]
    rw [hz,mul_zero,star_zero,add_zero,hN] at hf
    have hw : ‖((Λ^(-(j : ℝ)) : ℝ) : ℂ)‖ = Λ^(-(j : ℝ)) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛp _)]
    dsimp only [E]
    rw [norm_mul,hw]
    apply (mul_le_mul_of_nonneg_left hf (Real.rpow_pos_of_pos hΛp _).le).trans_eq
    calc
      _ = F (J-j)*U j*C*(Λ^(-(j : ℝ))*Λ^(-((J+1-j : ℕ) : ℝ)))*
          D^(2*j+(2*(J+1-j)+(m+2)+1)) := by rw [pow_add]; ring
      _ = _ := by
        rw [stationary_weight_mul hΛp (by omega : j ≤ J+1),
          show 2*j+(2*(J+1-j)+(m+2)+1) = 2*(J+1)+(m+2)+1 by omega]
        ring
  have hsum : p*inverseSphereSum m J Λ B e-z*B e = ∑ j ∈ Finset.range (J+1), E j := by
    rw [← inverse_direct_sum m J Λ B e he]
    simp only [inverseSphereSum,Finset.mul_sum,← Finset.sum_sub_distrib,E]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change ‖p*inverseSphereSum m J Λ B e-z*B e‖ ≤ _
  rw [hsum]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hterm).trans_eq
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DistanceInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse stationary phase for the original Euclidean displacement

The direction and oscillation parameter are exactly `z/‖z‖` and `r*‖z‖`.
No projected distance is substituted for the original distance.
-/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ContDiff

theorem sphereOscillation_displacement {d : ℕ} (r : ℝ) (z : Space d) (hz : z ≠ 0)
    (B : Sphere d → ℂ) :
    sphereOscillation (r*‖z‖) (displacementDirection z hz) B =
      ∫ w : Sphere d, Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) z : ℂ))*B w
        ∂sphereMeasure d := by
  unfold sphereOscillation
  apply integral_congr_ae
  filter_upwards with w
  congr 2
  have hi : (r*‖z‖)*inner ℝ (w : Space d) (normalize z) = r*inner ℝ (w : Space d) z := by
    rw [mul_assoc,← real_inner_smul_right,norm_smul_normalize]
  have hc := congrArg (fun a : ℝ => (a : ℂ)) hi
  push_cast at hc
  push_cast
  change Complex.I*((r : ℂ)*(‖z‖ : ℂ))*(inner ℝ (w : Space d) (normalize z) : ℂ) = _
  calc
    _ = Complex.I*(((r : ℂ)*(‖z‖ : ℂ))*(inner ℝ (w : Space d) (normalize z) : ℂ)) := by ring
    _ = Complex.I*((r : ℂ)*(inner ℝ (w : Space d) z : ℂ)) := congrArg (fun a => Complex.I*a) hc
    _ = _ := by ring

theorem inverseSphereSum_displacement (m J : ℕ) (r : ℝ) (z : Space (m+3)) (hz : z ≠ 0)
    (B : Space (m+3) → ℂ) :
    inverseSphereSum m J (r*‖z‖) B (displacementDirection z hz) =
      inverseDisplacementSum m J r z B := by
  apply Finset.sum_congr rfl
  intro j _
  rw [sphereOscillation_displacement]

theorem displacement_inverse_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ →
      ‖(((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        A*(r*‖z‖)^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
  obtain ⟨A,hA,hAb⟩ := sphere_inverse_expansion hgnomonic hquadratic m J
  refine ⟨A,hA,?_⟩
  intro z hz he B hB C D hC hD hb r hr
  have hh := hAb (displacementDirection z hz) he B hB C D hC hD hb (r*‖z‖) hr
  rw [inverseSphereSum_displacement] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arbitrary scale decay of the actual inverse remainder

One finite inverse order works uniformly at all large scales. Only the
ratio of the squared symbol scale to the oscillation parameter matters.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

theorem exists_displacement_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖(((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤ A*C*R^(-T) := by
  obtain ⟨L,hL,hscale⟩ := exists_stationary_remainder_order (m+1) (κ := κ) (T := T) hκ
  let J := L-1
  have hJL : J+1 = L := by dsimp [J]; omega
  obtain ⟨A,hA,hAb⟩ := displacement_inverse_expansion hgnomonic hquadratic m J
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDu z hz he B hB C hC hb r hr hratio
  have hh := hAb z hz he B hB C D hC hD hb r hr
  have ht := hscale R D (r*‖z‖) hR (zero_le_one.trans hD)
    (zero_lt_one.trans_le hr) hDu hratio
  have hs : (r*‖z‖)^(-((J+1 : ℕ) : ℝ))*D^(2*(J+1)+(m+2)+1) ≤ R^(-T) := by
    simpa only [hJL,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,inv_pow,
      Nat.add_assoc] using ht
  apply hh.trans
  calc
    _ = A*C*((r*‖z‖)^(-((J+1 : ℕ) : ℝ))*D^(2*(J+1)+(m+2)+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hA hC)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryWeightCancellation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the original distance weight

The fixed weight `q^(-(d-1)/2)` cancels the base spatial power in the
inverse expansion. Only the integer inverse powers need spatial Fourier
separation. The same weight occurs in each direct factor.
-/

namespace Falconer

theorem stationary_weighted_inverse_power (n j : ℕ) {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) :
    q^(-((n : ℝ)/2))*(r*q)^((n : ℝ)/2)*(r*q)^(-(j : ℝ)) =
      r^((n : ℝ)/2)*(r^j)⁻¹*(q^j)⁻¹ := by
  rw [Real.mul_rpow hr.le hq.le,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,
    mul_pow,mul_inv_rev]
  have hbase : q^(-((n : ℝ)/2))*q^((n : ℝ)/2) = 1 := by
    rw [← Real.rpow_add hq,neg_add_cancel,Real.rpow_zero]
  calc
    _ = (q^(-((n : ℝ)/2))*q^((n : ℝ)/2))*r^((n : ℝ)/2)*(r^j)⁻¹*(q^j)⁻¹ := by ring
    _ = _ := by rw [hbase,one_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary inverse with the original distance weight

After multiplication by `‖z‖^(-(d-1)/2)`, the only spatial powers in
the finite expansion have integer exponents. These are exactly the
powers handled by the spatial Fourier separation.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

theorem weightedInverseDisplacementSum_eq (m J : ℕ) {r : ℝ}
    (hr : 0 < r) (z : Space (m+3)) (hz : z ≠ 0) (B : Space (m+3) → ℂ) :
    weightedInverseDisplacementSum m J r z B =
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ) *
        (((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) *
          inverseDisplacementSum m J r z B := by
  unfold weightedInverseDisplacementSum inverseDisplacementSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc,← Complex.ofReal_mul,← Complex.ofReal_mul,
    stationary_weighted_inverse_power (m+2) j hr (norm_pos_iff.mpr hz)]

theorem exists_weighted_displacement_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖weightedInverseDisplacementSum m J r z B -
          ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        ‖z‖^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
  obtain ⟨J,A,hA,hb⟩ := exists_displacement_inverse_order hgnomonic hquadratic m hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR z hz he B hB C hC hBD r hr hratio
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrp : 0 < r := (mul_pos_iff_of_pos_right hzp).mp (zero_lt_one.trans_le hr)
  rw [weightedInverseDisplacementSum_eq m J hrp z hz B]
  have heq :
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
          (((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
          Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z) =
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
        ((((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
          Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)) := by ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hzp _)]
  exact (mul_le_mul_of_nonneg_left
    (hb R D hR hD hDR z hz he B hB C hC hBD r hr hratio)
    (Real.rpow_pos_of_pos hzp _).le).trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScaledWeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse expansion at the actual cell scale

Only the distance weight is rescaled. The oscillatory phase still uses the
original displacement and original radial frequency. The integer inverse
powers therefore match the spatial Fourier separation at the cell scale.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

theorem scaled_weighted_inverse_coefficient (h : ℝ) (j : ℕ)
    {s r t : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (r*s)^h*((r*s)^j)⁻¹*((t/s)^j)⁻¹ =
      s^h*(r^h*(r^j)⁻¹*(t^j)⁻¹) := by
  rw [Real.mul_rpow hr.le hs.le,mul_pow,div_pow,mul_inv_rev,inv_div]
  have hsj : s^j ≠ 0 := pow_ne_zero _ hs.ne'
  calc
    _ = (s^j)⁻¹*s^j*(s^h*(r^h*(r^j)⁻¹*(t^j)⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hsj,one_mul]

theorem scaledWeightedInverseSum_eq (m J : ℕ) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Space (m+3)) (B : Space (m+3) → ℂ) :
    scaledWeightedInverseSum m J s r z B =
      ((s^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*weightedInverseDisplacementSum m J r z B := by
  unfold scaledWeightedInverseSum weightedInverseDisplacementSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [scaled_weighted_inverse_coefficient _ j hs hr,Complex.ofReal_mul]
  ring

theorem scaled_weighted_inverse_distance {h s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    s^h*t^(-h) = (t/s)^(-h) := by
  rw [Real.div_rpow ht.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul]
  ring

theorem exists_scaled_weighted_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ s r : ℝ, 0 < s → 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖scaledWeightedInverseSum m J s r z B -
          (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        (‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
  obtain ⟨J,A,hA,hbound⟩ := exists_weighted_displacement_inverse_order
    hgnomonic hquadratic m hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR z hz hnear B hB C hC hBD s r hs hfreq hratio
  have hzpos := norm_pos_iff.mpr hz
  have hr : 0 < r := (mul_pos_iff_of_pos_right hzpos).mp (zero_lt_one.trans_le hfreq)
  have he := hbound R D hR hD hDR z hz hnear B hB C hC hBD r hfreq hratio
  have hp : 0 ≤ s^(((m+2 : ℕ) : ℝ)/2) := Real.rpow_nonneg hs.le _
  have heq : scaledWeightedInverseSum m J s r z B -
      (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z) =
      ((s^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*
        (weightedInverseDisplacementSum m J r z B -
          ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)) := by
    rw [scaledWeightedInverseSum_eq m J hs hr,
      ← scaled_weighted_inverse_distance hs hzpos,Complex.ofReal_mul]
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (by
    rw [← mul_assoc,← mul_assoc,← mul_assoc,scaled_weighted_inverse_distance hs hzpos])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScaledInverseRemainder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse remainder under the original pair measure

The scaled distance weight and the original endpoint laws are retained.
The estimate integrates the pointwise stationary remainder; no change of
measure or unproved Fourier estimate is used.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

theorem scaledDistanceKernel_measurable (m : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (hB : Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) =>
      B p.1.1 p.1.2 p.2)) : Measurable (scaledDistanceKernel m s r B) := by
  have hn : Measurable (fun z : Space (m+3) × Space (m+3) => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  unfold scaledDistanceKernel
  apply Measurable.mul
  · fun_prop
  · exact hB.comp (measurable_id.prodMk hn)

theorem scaledDistanceKernel_integrable (m : ℕ) (s r δ : ℝ) (hδ : 0 < δ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (hB : Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) =>
      B p.1.1 p.1.2 p.2))
    {C : ℝ} (hbound : ∀ x y w, ‖B x y w‖ ≤ C) :
    Integrable (scaledDistanceKernel m s r B) (μ.prod ν) := by
  apply Integrable.of_bound (scaledDistanceKernel_measurable m s r B hB).aestronglyMeasurable
    (δ^(-(((m+2 : ℕ) : ℝ)/2))*C)
  filter_upwards [hsep] with z hz
  have hp : 0 ≤ (dist z.1 z.2/s)^(-(((m+2 : ℕ) : ℝ)/2)) :=
    Real.rpow_nonneg (hδ.trans_le hz).le _
  have he : ‖Complex.exp (Complex.I*((r*dist z.1 z.2 : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [scaledDistanceKernel,norm_mul,he,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_nonpos hδ hz (neg_nonpos.mpr (by positivity)))
    (hbound _ _ _) (norm_nonneg _) (Real.rpow_nonneg hδ.le _)

theorem exists_integrated_scaled_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ R D s r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < s → 0 < δ →
      ∀ (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ,
      Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) => B p.1.1 p.1.2 p.2) →
      (∀ x y, ContDiff ℝ ∞ (B x y)) →
      ∀ C : ℝ, 0 ≤ C → (∀ x y w, ‖B x y w‖ ≤ C) →
      (∀ x y k, k ≤ 2*(J+1)+(m+2)+1 → ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (B x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (m+3) × Space (m+3) =>
        scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2)) (μ.prod ν) →
      ∀ M P : ℝ,
      ‖(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
          scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) ∂μ.prod ν) -
        (M⁻¹*P⁻¹) • (∫ z, scaledDistanceKernel m s r B z ∂μ.prod ν)‖ ≤
      |M⁻¹*P⁻¹| *((δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T))*(μ.prod ν).real univ) := by
  obtain ⟨J,A,hA,hi⟩ := exists_scaled_weighted_inverse_order hgnomonic hquadratic m (T := T) hκ
  refine ⟨J,A,hA,?_⟩
  intro R D s r δ hR hD hDR hs hδ μ ν _ _ hsep hnear hfreq B hBm hBs C hC hbound hderiv hInt M P
  have ht := scaledDistanceKernel_integrable m s r δ hδ μ ν hsep B hBm hbound
  have he : ∀ᵐ z ∂μ.prod ν,
      ‖scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) -
        scaledDistanceKernel m s r B z‖ ≤ δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
    filter_upwards [hsep,hnear,hfreq] with z hz hn hf
    have hdist : 0 < dist z.1 z.2 := (div_pos_iff_of_pos_right hs).mp (hδ.trans_le hz)
    have hzne : z.1-z.2 ≠ 0 := by
      intro h
      exact (ne_of_gt hdist) (by rw [sub_eq_zero.mp h,dist_self])
    have hnorm : ‖z.1-z.2‖ = dist z.1 z.2 := rfl
    have hh := hi R D hR hD hDR (z.1-z.2) hzne hn (B z.1 z.2) (hBs _ _)
      C hC (hderiv _ _) s r hs (by simpa only [hnorm] using hf.1)
      (by simpa only [hnorm] using hf.2)
    simp only [hnorm] at hh
    change ‖scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) -
      scaledDistanceKernel m s r B z‖ ≤ _ at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hδ hz (neg_nonpos.mpr (by positivity))) hA) hC)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  rw [← smul_sub,← integral_sub hInt ht,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const he) (abs_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorPairBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual two-endpoint descriptor amplitude -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {d : ℕ}

theorem descriptorAmbientProduct_global_bounds (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x w : Space d) :
    0 ≤ descriptorAmbientProduct Q ρ f N σ J i B S x w ∧
      descriptorAmbientProduct Q ρ f N σ J i B S x w ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).1)
  · exact Finset.prod_le_one
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).1)
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseScalarPullout
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial scalar factors commute with the angular inverse

This is used pointwise in the two original endpoints: their spatial
multipliers do not depend on the angular variable.
-/

namespace Falconer
open scoped ContDiff

private theorem localInverseAmplitude_single_jet (m j : ℕ)
    (f : Space (m+3) → ℂ) (hf : ContDiff ℝ ∞ f) (e : Space (m+3)) :
    let T := (MaskJetExpansion.product :
      MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j
    localInverseAmplitude m f j e =
      ∑ a : T.index, (T.term a).coefficient e *
        ((T.term a).jet ()).value f ((T.term a).point e) := by
  intro T
  let B : Unit → Unit → Space (m+3) → ℂ := fun _ _ => f
  have hv := MaskJetExpansion.inverse_value m j MaskJetExpansion.product B
    (fun _ _ => hf) () e
  have hp : (MaskJetExpansion.product : MaskJetExpansion Unit (m+3) (Space (m+3))).value
      B () = f := by
    funext z
    simp only [MaskJetExpansion.product_value,Fintype.prod_unique]
    rfl
  rw [hp] at hv
  simpa only [MaskJetExpansion.value,MaskJetTerm.value,Fintype.prod_unique] using hv.symm

theorem localInverseAmplitude_const_mul (m j : ℕ) (c : ℂ)
    (f : Space (m+3) → ℂ) (hf : ContDiff ℝ ∞ f) (e : Space (m+3)) :
    localInverseAmplitude m (fun z => c*f z) j e = c*localInverseAmplitude m f j e := by
  rw [localInverseAmplitude_single_jet m j _ (contDiff_const.mul hf) e,
    localInverseAmplitude_single_jet m j f hf e,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MaskJetIndex.value_const_mul _ c f hf]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetSeparation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite normalized endpoint factors for the actual inverse

The original individual-mask jets remain in the smooth endpoint factors.
All inverse-radius powers are kept in a separate scalar weight per term.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace SmoothSeparation
variable {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaleTerms_value (S : SmoothSeparation X Y E) (c : S.index → ℂ)
    (x : X) (y : Y) (z : E) :
    (S.scaleTerms c).value x y z = ∑ i : S.index, c i*(S.left i x z*S.right i y z) := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

end SmoothSeparation

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SeededSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint separation after a new inverse acts on existing jets

Both endpoint families keep all their original labels. Extracted scalar
weights charge only the newly added derivative orders, including the
complex angular multiplier when it is included as an extra label.
-/

namespace Falconer
open scoped ContDiff

variable {ι τ : Type} {X Y : Type*} [Fintype ι] [Fintype τ]
  [DecidableEq ι] [DecidableEq τ]

theorem seededJetSeparation_left (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (seededPairJets m j k).index) (x : X) (z : Space (m+3)) :
    (seededJetSeparation m j k r B C hB hC).left a x z =
      ((seededPairJets m j k).term a).coefficient z *
        ∏ i, (((seededPairJets m j k).term a).jet (.inl i)).scaledValue
          (r (.inl i)) (B i x) z := rfl

theorem seededJetSeparation_right (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (seededPairJets m j k).index) (y : Y) (z : Space (m+3)) :
    (seededJetSeparation m j k r B C hB hC).right a y z =
      ∏ i, (((seededPairJets m j k).term a).jet (.inr i)).scaledValue
        (r (.inr i)) (C i y) z := rfl

theorem seededJetSeparation_exact (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (hr : ∀ i, r i ≠ 0)
    (B : ι → X → Space (m+3) → ℂ) (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (x : X) (y : Y) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => (∏ i, (k (.inl i)).scaledValue (r (.inl i)) (B i x) z) *
        (∏ i, (k (.inr i)).scaledValue (r (.inr i)) (C i y) z)) j e =
      ((seededJetSeparation m j k r B C hB hC).scaleTerms
        (fun a => (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ))).value x y e := by
  let F : ι ⊕ τ → X × Y → Space (m+3) → ℂ :=
    fun i xy z => Sum.elim (fun a => B a xy.1 z) (fun b => C b xy.2 z) i
  have hF (i : ι ⊕ τ) (xy : X × Y) : ContDiff ℝ ∞ (F i xy) := by
    cases i with
    | inl i => exact hB i xy.1
    | inr i => exact hC i xy.2
  have heq :
      (fun z => (∏ i, (k (.inl i)).scaledValue (r (.inl i)) (B i x) z) *
        (∏ i, (k (.inr i)).scaledValue (r (.inr i)) (C i y) z)) =
      fun z => ∏ i, (k i).scaledValue (r i) (F i (x,y)) z := by
    funext z
    rw [Fintype.prod_sum_type]
    rfl
  rw [heq,MaskJetExpansion.localInverseAmplitude_seeded_jets m j k r hr F hF (x,y) e,
    SmoothSeparation.scaleTerms_value]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_sum_type,seededJetSeparation_left,seededJetSeparation_right]
  dsimp only [F,Sum.elim_inl,Sum.elim_inr]
  change (((seededPairJets m j k).term a).coefficient e *
      (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ)) * (_ * _) =
    (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ) *
      ((((seededPairJets m j k).term a).coefficient e * _) * _)
  ring

theorem seededJetSeparation_added_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : (seededPairJets m j k).index) :
    (∑ i, ((((seededPairJets m j k).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, ((((seededPairJets m j k).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j := by
  have h := MaskJetExpansion.seed_inverse_added_order m j k a
  rw [Fintype.sum_sum_type] at h
  exact h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetState
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse step on factorized descriptor symbols

An endpoint is labelled by one angular multiplier and its original finite
set of descriptors. The seed retains every old jet order. A new inverse
adds at most `2*j` to each endpoint's descriptor budget.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace MaskJetExpansion
variable {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem seed_inverse_single_order (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) (i : ι) :
    ((((seed k).inverse m j).term a).jet i).order ≤ (k i).order+2*j := by
  have hbase := (seed_ordersExtend k).inverse j a i
  have hsingle : ((((seed k).inverse m j).term a).jet i).order-(k i).order ≤
      ∑ t, (((((seed k).inverse m j).term a).jet t).order-(k t).order) :=
    Finset.single_le_sum
      (f := fun t => ((((seed k).inverse m j).term a).jet t).order-(k t).order)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have htotal := seed_inverse_added_order m j k a
  omega

theorem seed_inverse_left_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, ((((seed k).inverse m j).term a).jet (.inl i)).order) ≤
      (∑ i, (k (.inl i)).order)+2*j := by
  have htotal := seededJetSeparation_added_order m j k a
  change
    (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j
    at htotal
  have hsum :
      (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
        (∑ i, (k (.inl i)).order) =
        ∑ i, ((((seed k).inverse m j).term a).jet (.inl i)).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel ((seed_ordersExtend k).inverse j a (.inl i))
  omega

end MaskJetExpansion

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

theorem inverseLeftJets_order (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    (∑ b ∈ F, (f.inverseLeftJets g j a b).order) ≤ KL+2*j := by
  let k := descriptorInverseSeed f g
  let T := (MaskJetExpansion.seed k).inverse m j
  have hleft := MaskJetExpansion.seed_inverse_left_order m j k a
  have hinitial : (∑ i : DescriptorInverseLabel F, (k (.inl i)).order) =
      ∑ b ∈ F, (f.jet b).order := by
    rw [Fintype.sum_sum_type]
    simp only [k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Fintype.sum_unique,zero_add]
    exact Finset.sum_coe_sort F (fun b => (f.jet b).order)
  have hout : (∑ b ∈ F, (f.inverseLeftJets g j a b).order) =
      ∑ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [inverseLeftJets,dite_eq_left b.property]
    rfl
  rw [hinitial] at hleft
  rw [hout]
  have hpartial : (∑ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).order) ≤
      ∑ i : DescriptorInverseLabel F, ((T.term a).jet (.inl i)).order := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    omega
  exact hpartial.trans (hleft.trans (Nat.add_le_add_right f.order_le (2*j)))

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual recursive symbols produced by the inverse

The old descriptor list and spatial multiplier survive unchanged. The
angular multiplier is the geometric inverse coefficient times the newly
differentiated old multiplier, with a fixed normalization. The new finite
smoothness budget is explicit.
-/

namespace Falconer
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace MaskJetExpansion
variable {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem seed_inverse_right_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, ((((seed k).inverse m j).term a).jet (.inr i)).order) ≤
      (∑ i, (k (.inr i)).order)+2*j := by
  have htotal := seededJetSeparation_added_order m j k a
  change
    (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j
    at htotal
  have hsum :
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) +
        (∑ i, (k (.inr i)).order) =
        ∑ i, ((((seed k).inverse m j).term a).jet (.inr i)).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel ((seed_ordersExtend k).inverse j a (.inr i))
  omega

end MaskJetExpansion

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

theorem inverseRightJets_order (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    (∑ b ∈ G, (f.inverseRightJets g j a b).order) ≤ KR+2*j := by
  let k := descriptorInverseSeed f g
  let T := (MaskJetExpansion.seed k).inverse m j
  have hright := MaskJetExpansion.seed_inverse_right_order m j k a
  have hinitial : (∑ i : DescriptorInverseLabel G, (k (.inr i)).order) =
      ∑ b ∈ G, (g.jet b).order := by
    rw [Fintype.sum_sum_type]
    simp only [k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Fintype.sum_unique,zero_add]
    exact Finset.sum_coe_sort G (fun b => (g.jet b).order)
  have hout : (∑ b ∈ G, (f.inverseRightJets g j a b).order) =
      ∑ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [inverseRightJets,dite_eq_left b.property]
    rfl
  rw [hinitial] at hright
  rw [hout]
  have hpartial : (∑ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).order) ≤
      ∑ i : DescriptorInverseLabel G, ((T.term a).jet (.inr i)).order := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    omega
  exact hpartial.trans (hright.trans (Nat.add_le_add_right g.order_le (2*j)))

end DescriptorJetSymbol

/-- The left endpoint factor of each actual inverse term belongs to the
factorized class. The old multiplier needs `R+2*j` available derivatives. -/
theorem exists_inverse_left_symbol (m j R : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
      (f : DescriptorJetSymbol (m+1) KL L F D)
      (g : DescriptorJetSymbol (m+1) KR L G D),
      1 ≤ D → R+2*j ≤ L →
      ∀ a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index,
      ∃ u : DescriptorJetSymbol (m+1) (KL+2*j) R F D,
        u.jet = f.inverseLeftJets g j a ∧ u.spatial = f.spatial ∧
        u.angular = normalizedAngular A
          (fun z => (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient z *
            ((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
              (.inl (.inl ()))).scaledValue D⁻¹ f.angular z) := by
  obtain ⟨A,hA,hnormalize⟩ := inverse_angular_symbol m j R
  refine ⟨A,hA,?_⟩
  intro KL KR L F G D f g hD hL a
  let k := descriptorInverseSeed f g
  let p := (((MaskJetExpansion.seed k).inverse m j).term a).jet (.inl (.inl ()))
  have hp : p.order ≤ 2*j := by
    have h := MaskJetExpansion.seed_inverse_single_order m j k a (.inl (.inl ()))
    simpa only [p,k,descriptorInverseSeed,Sum.elim_inl,MaskJetIndex.zero,Nat.zero_add] using h
  have hbudget := hnormalize (DescriptorInverseLabel F ⊕ DescriptorInverseLabel G)
    k a p L f.angular f.angular_smooth D hD (by omega) f.angular_derivative
  rcases hbudget with ⟨hsmooth,hderivative,hcontrol⟩
  refine ⟨{
    jet := f.inverseLeftJets g j a
    order_le := f.inverseLeftJets_order g j a
    angular := normalizedAngular A (fun z =>
      (((MaskJetExpansion.seed k).inverse m j).term a).coefficient z *
        p.scaledValue D⁻¹ f.angular z)
    angular_smooth := hsmooth
    angular_derivative := hderivative
    angular_control := hcontrol
    spatial := f.spatial
    spatial_measurable := f.spatial_measurable
    spatial_bound := f.spatial_bound },rfl,rfl,rfl⟩

/-- The right endpoint retains its own original descriptors and spatial
multiplier. Its angular factor has no geometric coefficient. -/
theorem exists_inverse_right_symbol (m j R : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
      (f : DescriptorJetSymbol (m+1) KL L F D)
      (g : DescriptorJetSymbol (m+1) KR L G D),
      1 ≤ D → R+2*j ≤ L →
      ∀ a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index,
      ∃ u : DescriptorJetSymbol (m+1) (KR+2*j) R G D,
        u.jet = f.inverseRightJets g j a ∧ u.spatial = g.spatial ∧
        u.angular = normalizedAngular A
          (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
              (.inr (.inl ()))).scaledValue D⁻¹ g.angular) := by
  obtain ⟨A,hA,hnormalize⟩ := angular_jet_symbol (m+1) R
  refine ⟨A,hA,?_⟩
  intro KL KR L F G D f g hD hL a
  let k := descriptorInverseSeed f g
  let p := (((MaskJetExpansion.seed k).inverse m j).term a).jet (.inr (.inl ()))
  have hp : p.order ≤ 2*j := by
    have h := MaskJetExpansion.seed_inverse_single_order m j k a (.inr (.inl ()))
    simpa only [p,k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Nat.zero_add] using h
  have hbudget := hnormalize L p g.angular g.angular_smooth D hD (by omega)
    g.angular_derivative
  rcases hbudget with ⟨hsmooth,hderivative,hcontrol⟩
  refine ⟨{
    jet := f.inverseRightJets g j a
    order_le := f.inverseRightJets_order g j a
    angular := normalizedAngular A (p.scaledValue D⁻¹ g.angular)
    angular_smooth := hsmooth
    angular_derivative := hderivative
    angular_control := hcontrol
    spatial := g.spatial
    spatial_measurable := g.spatial_measurable
    spatial_bound := g.spatial_bound },rfl,rfl,rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetValues
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact values of the descriptor inverse factors

The additional label is the actual smooth angular multiplier. The other
labels are the original ambient descriptor masks, each occurring once.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {m K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem seedRadius_pos (f : DescriptorJetSymbol (m+1) K L F D) (hD : 0 < D)
    (N : ℕ) (σ : ℝ) (a : DescriptorInverseLabel F) : 0 < f.seedRadius N σ a := by
  cases a with
  | inl a => exact inv_pos.mpr hD
  | inr b => exact descriptorMaskRadius_pos N σ b

 theorem seedProduct (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (x z : Space (m+3)) :
    (∏ a : DescriptorInverseLabel F, (f.seedJet a).scaledValue (f.seedRadius N σ a)
      (f.seedMask Q ρ profile N σ J i S a x) z) =
      (∏ b ∈ F, normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (f.jet b).order (f.jet b).vectors x z : ℝ)*f.angular z := by
  have hzero : (f.seedJet (.inl ())).scaledValue (f.seedRadius N σ (.inl ()))
      (f.seedMask Q ρ profile N σ J i S (.inl ()) x) z = f.angular z := by
    change (MaskJetIndex.zero (m+3)).scaledValue D⁻¹ f.angular z = _
    rw [MaskJetIndex.scaledValue,MaskJetIndex.zero_value]
    change (1 : ℝ) • f.angular z = _
    exact one_smul ℝ _
  have hmask (b : {b // b ∈ F}) :
      (f.seedJet (.inr b)).scaledValue (f.seedRadius N σ (.inr b))
        (f.seedMask Q ρ profile N σ J i S (.inr b) x) z =
      (normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (f.jet b).order (f.jet b).vectors x z : ℂ) := by
    change (f.jet b).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) z = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    rfl
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  rw [hzero]
  simp_rw [hmask]
  rw [Finset.prod_coe_sort F (fun b =>
    (normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z : ℂ)),← Complex.ofReal_prod]
  ring

 theorem ambient_eq_seedProduct (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x z : Space (m+3)) :
    f.ambient Q ρ profile N σ J i S A x z = f.spatial x*(A⁻¹ : ℝ)*
      (∏ a : DescriptorInverseLabel F, (f.seedJet a).scaledValue (f.seedRadius N σ a)
        (f.seedMask Q ρ profile N σ J i S a x) z) := by
  rw [f.seedProduct]
  rfl

end DescriptorJetSymbol

theorem descriptorInverseSeparation_left {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x w =
      (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient w *
        (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
          (.inl (.inl ()))).scaledValue D⁻¹ f.angular w) *
        descriptorJetProduct Q ρ profile N σ J i F id S
          (fun b => (f.inverseLeftJets g j a b).order)
          (fun b _ => (f.inverseLeftJets g j a b).vectors) x w := by
  let T := (MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j
  have hmask (b : {b // b ∈ F}) :
      ((T.term a).jet (.inl (.inr b))).scaledValue
        (f.seedRadius N σ (.inr b))
        (f.seedMask Q ρ profile N σ J i S (.inr b) x) w =
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (f.inverseLeftJets g j a b).order (f.inverseLeftJets g j a b).vectors x w := by
    change ((T.term a).jet (.inl (.inr b))).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) w = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    have hj : f.inverseLeftJets g j a b = (T.term a).jet (.inl (.inr b)) := by
      simp only [DescriptorJetSymbol.inverseLeftJets,dite_eq_left b.property]
      rfl
    rw [← hj]
    rfl
  change (T.term a).coefficient w *
    (∏ l : DescriptorInverseLabel F, ((T.term a).jet (.inl l)).scaledValue
      (f.seedRadius N σ l) (f.seedMask Q ρ profile N σ J i S l x) w) = _
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  change (T.term a).coefficient w *
      (((T.term a).jet (.inl (.inl ()))).scaledValue D⁻¹ f.angular w *
        ∏ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).scaledValue
          (f.seedRadius N σ (.inr b)) (f.seedMask Q ρ profile N σ J i S (.inr b) x) w) = _
  simp_rw [hmask]
  rw [Finset.prod_coe_sort F (fun b =>
    normalizedDescriptorJet Q ρ profile N σ J i b (S b)
      (f.inverseLeftJets g j a b).order (f.inverseLeftJets g j a b).vectors x w)]
  change _ = (T.term a).coefficient w *
    (((T.term a).jet (.inl (.inl ()))).scaledValue D⁻¹ f.angular w) * _
  exact (mul_assoc _ _ _).symm

theorem descriptorInverseSeparation_right {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a x w =
      (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
          (.inr (.inl ()))).scaledValue D⁻¹ g.angular w) *
        descriptorJetProduct Q ρ profile N σ J i G id S
          (fun b => (f.inverseRightJets g j a b).order)
          (fun b _ => (f.inverseRightJets g j a b).vectors) x w := by
  let T := (MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j
  have hmask (b : {b // b ∈ G}) :
      ((T.term a).jet (.inr (.inr b))).scaledValue
        (g.seedRadius N σ (.inr b))
        (g.seedMask Q ρ profile N σ J i S (.inr b) x) w =
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (f.inverseRightJets g j a b).order (f.inverseRightJets g j a b).vectors x w := by
    change ((T.term a).jet (.inr (.inr b))).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) w = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    have hj : f.inverseRightJets g j a b = (T.term a).jet (.inr (.inr b)) := by
      simp only [DescriptorJetSymbol.inverseRightJets,dite_eq_left b.property]
      rfl
    rw [← hj]
    rfl
  change (∏ l : DescriptorInverseLabel G, ((T.term a).jet (.inr l)).scaledValue
    (g.seedRadius N σ l) (g.seedMask Q ρ profile N σ J i S l x) w) = _
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  change ((T.term a).jet (.inr (.inl ()))).scaledValue D⁻¹ g.angular w *
      (∏ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).scaledValue
          (g.seedRadius N σ (.inr b)) (g.seedMask Q ρ profile N σ J i S (.inr b) x) w) = _
  simp_rw [hmask]
  rw [Finset.prod_coe_sort G (fun b =>
    normalizedDescriptorJet Q ρ profile N σ J i b (S b)
      (f.inverseRightJets g j a b).order (f.inverseRightJets g j a b).vectors x w)]
  rfl

namespace DescriptorJetSymbol

/-- Restoring both normalization constants recovers the original spatial
factor and every normalized descriptor jet exactly. -/
theorem value_normalized_angular_restore {n K L : ℕ} {F : Finset PolicyDescriptor}
    {D : ℝ} (u : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (q : Space (n+2) → ℂ)
    (hq : u.angular = normalizedAngular B q) (x : Space (n+2)) (w : Sphere (n+2)) :
    ((A*B : ℝ) : ℂ)*u.value Q ρ profile N σ J i S A x w =
      u.spatial x*q w*descriptorJetProduct Q ρ profile N σ J i F id S
        (fun b => (u.jet b).order) (fun b _ => (u.jet b).vectors) x w := by
  let P := descriptorJetProduct Q ρ profile N σ J i F id S
    (fun b => (u.jet b).order) (fun b _ => (u.jet b).vectors) x w
  have ha : (A : ℂ)*((A⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hA.ne',Complex.ofReal_one]
  have hb : (B : ℂ)*((B⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hB.ne',Complex.ofReal_one]
  change ((A*B : ℝ) : ℂ)*(P*(u.spatial x*((A⁻¹ : ℝ) : ℂ)*u.angular w)) =
    u.spatial x*q w*P
  rw [hq]
  simp only [normalizedAngular,Complex.real_smul,Complex.ofReal_mul]
  calc
    _ = ((A : ℂ)*((A⁻¹ : ℝ) : ℂ))*((B : ℂ)*((B⁻¹ : ℝ) : ℂ))*
        (u.spatial x*q w*P) := by ring
    _ = _ := by rw [ha,hb,one_mul,one_mul]

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorSeededInverse
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The seeded inverse identity for actual recursive amplitudes

Both endpoint symbols use their original ambient masks. Spatial factors
are pulled out exactly, and only newly added derivatives pay radius powers.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

theorem descriptorInverseRadius_pos
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (hD : 0 < D) (N : ℕ) (σ : ℝ)
    (a : DescriptorInverseLabel F ⊕ DescriptorInverseLabel G) :
    0 < descriptorInverseRadius f g N σ a := by
  cases a with
  | inl a => exact f.seedRadius_pos hD N σ a
  | inr a => exact g.seedRadius_pos hD N σ a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseClassExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact inverse expansion in the recursive symbol class

The finite family is constructed from the actual differentiated masks.
Its constants are uniform in both descriptor lists, and the output keeps
the two original spatial multipliers and the remaining smoothness budget.
-/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

/-- The constants are selected before the lists, scale, and input symbols. -/
theorem exists_descriptorInverseSymbols (m j R : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧
      ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
        (f : DescriptorJetSymbol (m+1) KL L F D)
        (g : DescriptorJetSymbol (m+1) KR L G D),
        1 ≤ D → R+2*j ≤ L → Nonempty (DescriptorInverseSymbols f g j R A B) := by
  obtain ⟨A,hA,hleft⟩ := exists_inverse_left_symbol m j R
  obtain ⟨B,hB,hright⟩ := exists_inverse_right_symbol m j R
  refine ⟨A,B,hA,hB,?_⟩
  intro KL KR L F G D f g hD hL
  classical
  choose u hujet huspatial huangular using hleft KL KR L F G D f g hD hL
  choose v hvjet hvspatial hvangular using hright KL KR L F G D f g hD hL
  exact ⟨⟨u,v,hujet,hvjet,huspatial,hvspatial,huangular,hvangular⟩⟩

namespace DescriptorInverseSymbols

variable {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem left_restore (T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {U : ℝ} (hU : 0 < U) (hA : 0 < A)
    (a : DescriptorInverseIndex f g j) (x : Space (m+3)) (e : Sphere (m+3)) :
    ((U*A : ℝ) : ℂ)*(T.left a).value Q ρ profile N σ J i S U x e =
      f.spatial x*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x e := by
  have h := (T.left a).value_normalized_angular_restore Q ρ profile N σ J i S
    hU hA _ (T.left_angular a) x e
  rw [T.left_spatial a,T.left_jet a] at h
  rw [descriptorInverseSeparation_left]
  exact h.trans (by ring)

theorem right_restore (T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {V : ℝ} (hV : 0 < V) (hB : 0 < B)
    (a : DescriptorInverseIndex f g j) (y : Space (m+3)) (e : Sphere (m+3)) :
    ((V*B : ℝ) : ℂ)*(T.right a).value Q ρ profile N σ J i S V y e =
      g.spatial y*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a y e := by
  have h := (T.right a).value_normalized_angular_restore Q ρ profile N σ J i S
    hV hB _ (T.right_angular a) y e
  rw [T.right_spatial a,T.right_jet a] at h
  rw [descriptorInverseSeparation_right]
  exact h.trans (by ring)

end DescriptorInverseSymbols
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BaseJetAmplitude
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked amplitude is the zero-jet root state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem base_ambient {n : ℕ} (F : Finset PolicyDescriptor) (K L : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (c : Space (n+2) → ℂ)
    (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x z : Space (n+2)) :
    (base F K L D hD c hc hcb).ambient Q ρ profile N σ J i S A x z =
      (descriptorAmbientProduct Q ρ profile N σ J i F S x z : ℂ)*(c x*(A⁻¹ : ℝ)) := by
  have hzero (b : PolicyDescriptor) :
      normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (MaskJetIndex.zero (n+2)).order (MaskJetIndex.zero (n+2)).vectors x z =
      descriptorAmbientMask Q ρ profile N σ J i b (S b) x z := by
    simp only [normalizedAmbientDescriptorJet,MaskJetIndex.zero,pow_zero,one_mul]
    rfl
  simp only [ambient,base,hzero,mul_one,descriptorAmbientProduct]
  ring

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ScaledInverseIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the complete cell-scaled inverse

Every term uses the original endpoint measures. The distance weight is
separated at the cell scale, and the radial coefficient is kept explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem scaledWeightedInverseSum_eq_terms (m J : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) :
    scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) =
      ∑ j ∈ Finset.range (J+1),
        (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
          scaledInverseTerm m j s r B z := by
  unfold scaledWeightedInverseSum scaledInverseTerm
  apply Finset.sum_congr rfl
  intro j _
  simp only [dist_eq_norm,Complex.ofReal_mul,mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TwoProfileInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact inverse factors with two independent original profiles

The finite output symbols are the same uniformly constructed symbols.
Only their endpoint evaluations use the two distinct cubes, laws, profiles
and mask families. Radius powers still charge only new derivatives.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem two_profile_expansion (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3)))
    (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag : ℝ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (x y : Space (m+3)) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) j e =
      ∑ a : DescriptorInverseIndex f g j,
        ((descriptorInverseWeight f g j N σ a*(U*A)*(V*B)*Af⁻¹*Ag⁻¹ : ℝ) : ℂ)*
          ((T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U x e *
            (T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ V y e) := by
  let k := descriptorInverseSeed f g
  let r := descriptorInverseRadius f g N σ
  let F₁ := f.seedMask Q₁ ρ₁ profile₁ N σ J i S₁
  let F₂ := g.seedMask Q₂ ρ₂ profile₂ N σ J i S₂
  let H := fun z => (∏ l, (f.seedJet l).scaledValue (f.seedRadius N σ l) (F₁ l x) z)*
    (∏ l, (g.seedJet l).scaledValue (g.seedRadius N σ l) (F₂ l y) z)
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (f.seedMask_smooth Q₁ ρ₁ profile₁ N σ J i S₁ l x))).mul
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (g.seedMask_smooth Q₂ ρ₂ profile₂ N σ J i S₂ l y)))
  have heq : (fun z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
      g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) =
      fun z => ((f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ)))*H z := by
    funext z
    rw [f.ambient_eq_seedProduct,g.ambient_eq_seedProduct]
    dsimp only [H,F₁,F₂]
    ring
  rw [heq,localInverseAmplitude_const_mul m j _ H hH]
  have hinv := seededJetSeparation_exact m j k r
    (fun l => (descriptorInverseRadius_pos f g hD N σ l).ne') F₁ F₂
    (f.seedMask_smooth Q₁ ρ₁ profile₁ N σ J i S₁)
    (g.seedMask_smooth Q₂ ρ₂ profile₂ N σ J i S₂) x y e
  change localInverseAmplitude m H j e = _ at hinv
  rw [hinv]
  change (f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ))*
    (∑ a : DescriptorInverseIndex f g j,
      (descriptorInverseWeight f g j N σ a : ℂ)*
        (descriptorInverseSeparation f g j Q₁ ρ₁ profile₁ N σ J i S₁).left a x e *
        (descriptorInverseSeparation f g j Q₂ ρ₂ profile₂ N σ J i S₂).right a y e) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hl := T.left_restore Q₁ ρ₁ profile₁ N σ J i S₁ hU hA a x e
  have hr := T.right_restore Q₂ ρ₂ profile₂ N σ J i S₂ hV hB a y e
  simp only [Complex.ofReal_mul]
  calc
    _ = ((Af⁻¹ : ℝ) : ℂ)*((Ag⁻¹ : ℝ) : ℂ)*
        (descriptorInverseWeight f g j N σ a : ℂ)*
        (f.spatial x*(descriptorInverseSeparation f g j Q₁ ρ₁ profile₁ N σ J i S₁).left a x e)*
        (g.spatial y*(descriptorInverseSeparation f g j Q₂ ρ₂ profile₂ N σ J i S₂).right a y e) := by ring
    _ = _ := by rw [← hl,← hr]; simp only [Complex.ofReal_mul]; ring

end DescriptorInverseSymbols
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TwoProfileInverseIntegrable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of the two-profile original inverse family -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

private theorem bounded_sphere_phase_integrable_p4 {d : ℕ}
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) (z : Space d × Space d) :
    Integrable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (b z.1 w*c z.2 w)) (sphereMeasure d) := by
  have hm : Measurable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (b z.1 w*c z.2 w)) := by
    apply Measurable.mul
    · fun_prop
    · exact (hb.comp (measurable_const.prodMk measurable_id)).mul
        (hc.comp (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable (B*C)
  filter_upwards with w
  have he : ‖Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  rw [norm_mul,he,one_mul,norm_mul]
  exact mul_le_mul (hbB z.1 w) (hcC z.2 w) (norm_nonneg _) hB

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

theorem two_profile_original_term_integrable (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (scaledInverseTerm m j s r
      (fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z)) (μ.prod ν) := by
  let b := fun a : DescriptorInverseIndex f g j => (T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U
  let c := fun a : DescriptorInverseIndex f g j => (T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ U
  let α := fun a : DescriptorInverseIndex f g j => (T.coefficient N σ Af Ag U U a : ℂ)
  let Z := fun (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₀ := (descriptorJetBound (m+3) (K+2*j))^(K+2*j)*U⁻¹
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (b a)) :=
    (T.left a).value_measurable Q₁ ρ₁ profile₁ N σ J i S₁ U
  have hc (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (c a)) :=
    (T.right a).value_measurable Q₂ ρ₂ profile₂ N σ J i S₂ U
  have hbB (a : DescriptorInverseIndex f g j) (x) (w) : ‖b a x w‖ ≤ C₀ :=
    (T.left a).value_norm_le Q₁ ρ₁ profile₁ N σ J i S₁ hF hU x w
  have hcC (a : DescriptorInverseIndex f g j) (x) (w) : ‖c a x w‖ ≤ C₀ :=
    (T.right a).value_norm_le Q₂ ρ₂ profile₂ N σ J i S₂ hG hU x w
  have hi (a : DescriptorInverseIndex f g j) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      hsep (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₀ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable_p4 (b a) (c a) (hb a) (hc a) hC₀ (hbB a) (hcC a) r z
  have he : scaledInverseTerm m j s r
      (fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) =
      fun z => ∑ a : DescriptorInverseIndex f g j, α a*Z a z := by
    funext z
    unfold scaledInverseTerm
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
              g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w) =
        fun w : Sphere (m+3) => ∑ a : DescriptorInverseIndex f g j, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [T.two_profile_expansion hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ Af Ag hU hU]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change _*(α a*(b a z.1 w*c a z.2 w)) = _
      ring
    rw [hf,integral_finsetSum Finset.univ (fun a _ => (hsphere a z).const_mul (α a))]
    simp only [integral_const_mul,Finset.mul_sum,Z]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun a _ => (hi a).const_mul (α a))

end DescriptorInverseSymbols

theorem two_profile_scaled_inverse_integrable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D} (k R : ℕ)
    (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (fun z : Space (m+3) × Space (m+3) =>
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t)) (μ.prod ν) := by
  let V := fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
    g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z
  have hi (j : Fin (k+1)) : Integrable (scaledInverseTerm m j.val s r V) (μ.prod ν) :=
    (T j).two_profile_original_term_integrable hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
      Af Ag hU δ hδ s μ ν hsep r
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1),
      (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
        scaledInverseTerm m j s r V z) (μ.prod ν) := by
    apply integrable_finsetSum
    intro j hj
    exact (hi ⟨j,Finset.mem_range.mp hj⟩).const_mul _
  apply hs.congr
  filter_upwards with z
  exact (scaledWeightedInverseSum_eq_terms m k s r V z).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_EndpointWeightedDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted distance law for two different endpoint profiles

Both original marginal laws and their separate normalizations are retained.
The endpoint factors may be the actual descriptor products of different
regularized classes. No common probability law is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem endpointDistanceWeight_measurable {d : ℕ} (s : ℝ)
    (B C : Space d → Space d → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) :
    Measurable (endpointDistanceWeight s B C) := by
  have hn : Measurable (fun z : Space d × Space d => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  exact (((measurable_fst.dist measurable_snd).div_const s).pow_const _).mul
    (hB.comp (measurable_fst.prodMk hn)) |>.mul (hC.comp (measurable_snd.prodMk hn))

 theorem endpointDistanceWeight_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, 0 ≤ B x w) (hC : ∀ x w, 0 ≤ C x w) (z : Space d × Space d) :
    0 ≤ endpointDistanceWeight s B C z :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg dist_nonneg hs) _) (hB _ _)) (hC _ _)

 theorem endpointDistanceWeight_bound {d : ℕ} (hd : 1 ≤ d) {s δ : ℝ} (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (z : Space d × Space d) (hz : δ ≤ dist z.1 z.2/s) :
    endpointDistanceWeight s B C z ≤ δ^(-(((d:ℝ)-1)/2)) := by
  have hr : 0 ≤ (dist z.1 z.2/s)^(-(((d:ℝ)-1)/2)) := Real.rpow_nonneg (hδ.trans_le hz).le _
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply (mul_le_of_le_one_right (mul_nonneg hr (hB _ _).1) (hC _ _).2).trans
  exact (mul_le_of_le_one_right hr (hB _ _).2).trans
    (Real.rpow_le_rpow_of_nonpos hδ hz (by linarith))

 theorem endpointWeightedDistance_finite {d : ℕ} (hd : 1 ≤ d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P s δ : ℝ} (hM : 0 < M) (hP : 0 < P) (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) :
    IsFiniteMeasure (endpointWeightedDistance μ ν M P s B C) := by
  have hbound : ∀ᵐ z ∂μ.prod ν,
      ENNReal.ofReal ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z) ≤
        ENNReal.ofReal ((M⁻¹*P⁻¹)*δ^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (endpointDistanceWeight_bound hd hδ B C hB hC z hz) (by positivity))
  let := finite_withDensity_of_bounded (μ.prod ν) _ ENNReal.ofReal_lt_top hbound
  unfold endpointWeightedDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 theorem endpointWeightedDistance_fourier (n : ℕ)
    (μ ν : Measure (Space (n+3))) {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    {s : ℝ} (hs : 0 < s) (B C : Space (n+3) → Space (n+3) → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C))
    (hB0 : ∀ x w, 0 ≤ B x w) (hC0 : ∀ x w, 0 ≤ C x w) (r : ℝ) :
    charFun (endpointWeightedDistance μ ν M P s B C) r =
      (M⁻¹*P⁻¹) • ∫ z, scaledDistanceKernel n s r
        (fun x y w => (B x w : ℂ)*(C y w : ℂ)) z ∂μ.prod ν := by
  rw [charFun_apply_real,endpointWeightedDistance,integral_map (by fun_prop) (by fun_prop)]
  have hw : Measurable (fun z => ENNReal.ofReal
      ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z)) :=
    ((endpointDistanceWeight_measurable s B C hB hC).const_mul _).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity)
    (endpointDistanceWeight_nonneg hs.le B C hB0 hC0 z))]
  have he : -((((n+3:ℕ):ℝ)-1)/2) = -(((n+2:ℕ):ℝ)/2) := by push_cast; ring
  simp only [endpointDistanceWeight,scaledDistanceKernel,he,Complex.real_smul,Complex.ofReal_mul]
  push_cast
  ring_nf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_TwoProfileMaskedShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar shell for two actual descriptor products

The Fourier law is formed from the original two measures. Its inverse
terms keep the two profile and descriptor data throughout the shell bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_two_profile_masked_shell_order_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
      ∃ A B : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧ (∀ j, 1 ≤ B j) ∧
      ∀ R E δ W C₀ : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C₀ →
      ∀ (Q₁ Q₂ : DyadicCube (n+3)) (ρ₁ ρ₂ : Measure (Space (n+3)))
        (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
        (F G : Finset PolicyDescriptor) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (n+3))),
      (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      (∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      ∀ (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
        (M P s : ℝ), 0 < M → 0 < P → 0 < s →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (fun t =>
          (descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁ x t : ℂ)*
          (descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂ y t : ℂ)) w‖ ≤ C₀*E^l) →
      ∀ U : ℝ, 0 < U → ∀ (a v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ energy : ℝ,
      (∀ (u : DescriptorJetSymbol (n+1) (2*k) L F 1)
        (w : DescriptorJetSymbol (n+1) (2*k) L G 1),
        independentAngularEnergy a v Ψ
          (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
          (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy) →
      let f := descriptorRootSymbol (n+1) F (L+2*k)
      let g := descriptorRootSymbol (n+1) G (L+2*k)
      let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
      let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
      (2:ℝ)^(-a) * (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖charFun (endpointWeightedDistance μ ν M P s left right) r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW*energy)+
        2*(2:ℝ)^(v-a)*
          (|M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  obtain ⟨k,A₀,hA₀,hrem⟩ := exists_integrated_scaled_inverse_order hgnomonic hquadratic n (T := T) hκ
  refine ⟨k,A₀,hA₀,?_⟩
  intro L
  choose A B hA hB hfamily using fun j : Fin (k+1) => exists_descriptorInverseSymbols n j.val L
  refine ⟨A,B,hA,hB,?_⟩
  intro R E δ W C₀ hR hE hER hδ hW hC₀ Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i F G S₁ S₂
    hsepF hsepG hFE hGE μ ν _ _ M P s hM hP hs hsep hnear hderiv U hU a v Ψ hΨ hpos hzero hone _
    hregime hfreq energy henergy
  let f := descriptorRootSymbol (n+1) F (L+2*k)
  let g := descriptorRootSymbol (n+1) G (L+2*k)
  let family (j : Fin (k+1)) : DescriptorInverseSymbols f g j.val L (A j) (B j) :=
    Classical.choice (hfamily j 0 0 (L+2*k) F G 1 f g (by norm_num) (by have := j.isLt; omega))
  let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
  let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
  have hleft (x t : Space (n+3)) : f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ 1 x t = (left x t : ℂ) := by
    simp only [f,descriptorRootSymbol,DescriptorJetSymbol.base_ambient,inv_one,
      Complex.ofReal_one,mul_one,left]
  have hright (x t : Space (n+3)) : g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ 1 x t = (right x t : ℂ) := by
    simp only [g,descriptorRootSymbol,DescriptorJetSymbol.base_ambient,inv_one,
      Complex.ofReal_one,mul_one,right]
  have hInt (r : ℝ) := two_profile_scaled_inverse_integrable k L A B family (by norm_num)
    (fun j => zero_lt_one.trans_le (hA j)) (fun j => zero_lt_one.trans_le (hB j))
    Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hsepF hsepG 1 1 hU δ hδ s μ ν
    (hsep.mono fun _ hz => hz.1) r
  have hleftB (x t) : left x t ∈ Icc (0:ℝ) 1 :=
    descriptorAmbientProduct_global_bounds Q₁ ρ₁ profile₁ N σ J i F S₁ x t
  have hrightB (x t) : right x t ∈ Icc (0:ℝ) 1 :=
    descriptorAmbientProduct_global_bounds Q₂ ρ₂ profile₂ N σ J i G S₂ x t
  have hmleft : Measurable (Function.uncurry left) := descriptorAmbientProduct_measurable _ _ _ _ _ _ _ _ _
  have hmright : Measurable (Function.uncurry right) := descriptorAmbientProduct_measurable _ _ _ _ _ _ _ _ _
  let := endpointWeightedDistance_finite (by omega : 1 ≤ n+3) μ ν hM hP hδ left right hleftB hrightB
    (hsep.mono fun _ hz => hz.1)
  have hscalar := scalar_shell_of_two_profile_inverse k L A B family (by norm_num)
    (fun j => zero_lt_one.trans_le (hA j)) (fun j => zero_lt_one.trans_le (hB j))
    Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hsepF hsepG 1 1 hU hE hE hFE hGE δ W hδ hW
    hs μ ν hsep hM hP a v Ψ hΨ hpos hzero hone hregime energy
    (by
      intro u w
      exact henergy (u.relax (by omega) le_rfl (by norm_num) le_rfl)
        (w.relax (by omega) le_rfl (by norm_num) le_rfl))
    (charFun (endpointWeightedDistance μ ν M P s left right)) measurable_charFun
    (ε := |M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))
  have hb := hscalar (by
    filter_upwards [hfreq] with r hr
    rw [norm_sub_rev,endpointWeightedDistance_fourier n μ ν hM hP hs left right hmleft hmright
      (fun x w => (hleftB x w).1) (fun x w => (hrightB x w).1)]
    simp only [hleft,hright]
    apply hrem R E s r δ hR hE hER hs hδ μ ν (hsep.mono fun _ hz => hz.1) hnear hr
      (fun x y w => (left x w : ℂ)*(right y w : ℂ))
    · exact (hmleft.comp (measurable_fst.fst.prodMk measurable_snd)).complex_ofReal |>.mul
        (hmright.comp (measurable_fst.snd.prodMk measurable_snd)).complex_ofReal
    · intro x y
      exact (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff _ _ _ _ _ _ _ _ _ x)).mul
        (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff _ _ _ _ _ _ _ _ _ y))
    · exact zero_le_one.trans hC₀
    · intro x y w
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hleftB x w).1,
        abs_of_nonneg (hrightB y w).1]
      exact (mul_le_mul (hleftB x w).2 (hrightB y w).2 (hrightB y w).1 (by norm_num)).trans
        (by simpa only [one_mul] using hC₀)
    · exact hderiv
    · simpa only [hleft,hright] using hInt r)
  exact hb.2

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_two_profile_masked_shell_order_oai := @OAI.Falconer.exists_two_profile_masked_shell_order_oai
