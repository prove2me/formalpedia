-- Prove2me | solution 1 for OAI.Falconer.exists_policy_scalar_conversion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:20:58.203433+00:00
-- url     : https://prove2.me/submissions/fe71f8d4-3f58-43a1-87db-89ec35764b6d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_rotated_masked_fourier_inverse_order

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      all_goals try with_reducible_and_instances rfl
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphere_integral_rotation {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (f : Sphere d → ℂ) :
    (∫ w, f (sphereMap e w) ∂sphereMeasure d) = ∫ w, f w ∂sphereMeasure d :=
  (sphereMap_measurePreserving e).integral_comp (sphereHomeomorph e).measurableEmbedding f

end Falconer

end OAI
end

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothMask
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth angular masks from buffered good sets

A finite subcollection of the normalized cap partition gives a cutoff
supported inside a prescribed set. It equals one wherever a closed ball
of twice the cap radius lies in that set. No regularity of the set is
needed for this finite construction.
-/

namespace Falconer
open Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem capCutoffAmbient_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (U : Set (Sphere d)) :
    (∀ w : Sphere d, 0 ≤ capCutoffAmbient δ hδ S U w ∧ capCutoffAmbient δ hδ S U w ≤ 1) ∧
    (∀ w : Sphere d, capCutoffAmbient δ hδ S U w ≠ 0 → w ∈ U) ∧
    (∀ w : Sphere d, (∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U) →
      capCutoffAmbient δ hδ S U w = 1) := by
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  have hsub : cutoffCapCenters δ S U ⊆ S := Finset.filter_subset _ _
  refine ⟨?_,?_,?_⟩
  · intro w
    constructor
    · exact Finset.sum_nonneg (fun c hc => (hbounds c (hsub hc) w).1)
    · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc _ => (hbounds c hc w).1))
      exact (hpart w).le
  · intro w hw
    obtain ⟨c,hc,hcw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have hsel := (Finset.mem_filter.mp hc).2
    apply hsel w
    exact hsupport c (hsub hc) w hcw
  · intro w hcore
    rw [← hpart w]
    apply Finset.sum_subset hsub
    intro c hc hnot
    by_contra hn
    have hdist : dist w c ≤ δ := hsupport c hc w hn
    apply hnot
    apply Finset.mem_filter.mpr ⟨hc,?_⟩
    intro z hz
    apply hcore z
    calc
      dist z w ≤ dist z c+dist c w := dist_triangle _ _ _
      _ ≤ δ+δ := add_le_add hz (by simpa only [dist_comm] using hdist)
      _ = 2*δ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientMaskProductBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial mixed-derivative cost of an actual finite mask product

The zeroth-order bound is one. Consequently no constant is raised to the
number of descriptors: order `k` costs only `card^k`.
-/

namespace Falconer
open scoped ContDiff

variable {E A ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A] [DecidableEq ι]

theorem ambient_mask_product_derivatives (S : Finset ι) (f : ι → E → A)
    {D : ℝ} (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*D)^k := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a S ha ih =>
    have hfs : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbs : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k :=
      fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hih := ih hfs hbs
    intro k hk
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfp : ContDiff ℝ ∞ (fun z => ∏ i ∈ S, f i z) := contDiff_prod hfs
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfa hfp x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (k+1), (k.choose l : ℝ)*D^l*((S.card : ℝ)*D)^(k-l) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a (Finset.mem_insert_self _ _) l (hlk.trans hk))
            (Nat.cast_nonneg _))
          (hih (k-l) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      _ = (D+(S.card : ℝ)*D)^k := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by congr 1; ring

/-- A fixed positive-order derivative constant is absorbed into each
differentiated mask's scale, never into every undifferentiated mask. -/
theorem ambient_mask_product_budget (S : Finset ι) (f : ι → E → A)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (hzero : ∀ i ∈ S, ‖f i x‖ ≤ 1)
    (hb : ∀ i ∈ S, ∀ k, 1 ≤ k → k ≤ K → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C*D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*C*D)^k := by
  have hscaled : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ (C*D)^k := by
    intro i hi k hk
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero,pow_zero] using hzero i hi
    | succ k =>
      apply (hb i hi (k+1) (by omega) hk).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hC (by omega)) (pow_nonneg hD _)
  simpa only [mul_assoc] using ambient_mask_product_derivatives S f
    (mul_nonneg (zero_le_one.trans hC) hD) K x hf hscaled

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Angular masks attached to actual dyadic anchor cells

The spatial dependence is a finite Borel choice of the anchor cell.
On every descendant of an anchor cell, its angular mask is exactly
constant in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem anchoredMask_on_cell {d n : ℕ} (Q : DyadicCube d)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (p : List (Fin d → Bool)) (hp : p.length = n)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    anchoredMask Q n F x w = F p w := by
  unfold anchoredMask
  rw [Finset.sum_eq_single p]
  · simp [hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint ((mem_cubePaths d n q).mp hq |>.trans hp.symm) hqp
    have hn : x ∉ (Q.descendant q).carrier := fun hq => Set.disjoint_left.mp hdis hq hx
    simp [hn]
  · exact fun hn => (hn ((mem_cubePaths d n p).mpr hp)).elim

theorem anchoredMask_off_parent {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) {x : Space d} (hx : x ∉ Q.carrier)
    (w : Sphere d) : anchoredMask Q n F x w = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  have hn : x ∉ (Q.descendant p).carrier := fun h => hx (Q.descendant_subset p h)
  simp [hn]

theorem anchoredMask_bounds {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ)
    (hF : ∀ p ∈ cubePaths d n, ∀ w, 0 ≤ F p w ∧ F p w ≤ 1)
    (x : Space d) (w : Sphere d) :
    0 ≤ anchoredMask Q n F x w ∧ anchoredMask Q n F x w ≤ 1 := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx
    rw [anchoredMask_on_cell Q F p ((mem_cubePaths d n p).mp hp) hxp]
    exact hF p hp w
  · rw [anchoredMask_off_parent Q n F hx]
    norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredBufferedMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Buffered masks on the original spatial anchor cells

These masks are jointly measurable, bounded between zero and one, smooth
in every adapted angular chart, and constant in the spatial variable on
all descendants of a reached anchor. Their angular derivative constants
are independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem anchoredBufferedMask_bounds {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d)) (x : Space d) (w : Sphere d) :
    0 ≤ anchoredBufferedMask Q g δ hδ S U x w ∧
      anchoredBufferedMask Q g δ hδ S U x w ≤ 1 :=
  anchoredMask_bounds Q g _ (fun p _ => (capCutoffAmbient_properties hδ S hcover (U p)).1) x w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SphericalEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sphereMoment_nonneg {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) :
    0 ≤ sphereMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem sphere_norm_square_integrable {d : ℕ} (U : Sphere d → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w, ‖U w‖ ≤ C) :
    Integrable (fun w => ‖U w‖^2) (sphereMeasure d) := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb w)

theorem sphereMoment_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment U r ≤ C^2 * (sphereMeasure d).real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb (r,w))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorMask Q ρ m N σ J i b S x w ∧
      descriptorMask Q ρ m N σ J i b S x w ≤ 1 :=
  anchoredBufferedMask_bounds Q _ (descriptorMaskRadius_pos N σ b) S hcover _ x w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SharedAngular
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared-angle energy and the independent-angle bound

The shell conversion uses one shared angular variable. Cauchy--Schwarz
transfers it to the positive independent-angle energy with exactly the
same endpoint symbols and radial measure.
-/

namespace Falconer
open Set MeasureTheory

theorem real_integral_product_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable (fun x => f x^2) μ) (hg : Integrable (fun x => g x^2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ) * (∫ x, g x^2 ∂μ) := by
  have hp (t : ℝ) : 0 ≤
      (∫ x, g x^2 ∂μ) * (t*t) + (-2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x^2 ∂μ := by
    have hn : (0 : ℝ) ≤ ∫ x, (f x - t*g x)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (f x - t*g x))
    have he (x : X) : (f x - t*g x)^2 =
        (t*t) * g x^2 + (-2*t) * (f x*g x) + f x^2 := by ring
    simp_rw [he] at hn
    have hadd := integral_add ((hg.const_mul (t*t)).add (hfg.const_mul (-2*t))) hf
    dsimp only [Pi.add_apply] at hadd
    rw [hadd, integral_add (hg.const_mul (t*t)) (hfg.const_mul (-2*t)),
      integral_const_mul, integral_const_mul] at hn
    nlinarith [hn]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

theorem sphere_shared_integral_sq_le {d : ℕ} (U V : Sphere d → ℂ)
    (ψ : Sphere d → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hψb : ∀ w, |ψ w| ≤ 1)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ w, ‖U w‖ ≤ C) (hbV : ∀ w, ‖V w‖ ≤ D) :
    ‖∫ w, ψ w • (U w * star (V w)) ∂sphereMeasure d‖^2 ≤
      (∫ w, ‖U w‖^2 ∂sphereMeasure d) * (∫ w, ‖V w‖^2 ∂sphereMeasure d) := by
  have hfg : Integrable (fun w => ‖U w‖ * ‖V w‖) (sphereMeasure d) := by
    apply Integrable.of_bound (hU.norm.mul hV.norm).aestronglyMeasurable (C*D)
    filter_upwards with w
    change ‖‖U w‖ * ‖V w‖‖ ≤ C*D
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (hbU w) (hbV w) (norm_nonneg _) hC
  have hn : ‖∫ w, ψ w • (U w * star (V w)) ∂sphereMeasure d‖ ≤
      ∫ w, ‖U w‖ * ‖V w‖ ∂sphereMeasure d := by
    apply norm_integral_le_of_norm_le hfg
    filter_upwards with w
    rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_star]
    exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hψb w)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (real_integral_product_sq_le (sphereMeasure d) (fun w => ‖U w‖) (fun w => ‖V w‖)
      (sphere_norm_square_integrable U hU hC hbU)
      (sphere_norm_square_integrable V hV hD hbV) hfg)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EndpointTransform
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

theorem endpoint_integrand_norm {d : ℕ} (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) (x : Space d) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w‖ = ‖b x w‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem endpointTransform_norm_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {M C : ℝ} (hM : 0 < M) (b : Space d → Sphere d → ℂ)
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    ‖endpointTransform ρ M b r w‖ ≤ C * ρ.real Set.univ / M := by
  unfold endpointTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_integral_le_of_norm_le_const (μ := ρ)
    (Filter.Eventually.of_forall (fun x => (endpoint_integrand_norm b r w x).trans_le (hC x w)))
  calc
    _ ≤ M⁻¹ * (C * ρ.real Set.univ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DescriptorProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descriptor products and their reached angular factors -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorProduct_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorProduct Q ρ m N σ J i B S x w ∧
      descriptorProduct Q ρ m N σ J i B S x w ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
  · exact Finset.prod_le_one (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
      (fun b hb => (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).2)

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GlobalDescriptorBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global derivative budgets for actual descriptor products

The constants are chosen before the scale, cells, descriptor list and cap
families.  The only list-size loss is a power of its cardinality.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer

theorem descriptorAmbientProduct_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  classical
  choose A hA hAb using fun k => descriptorAmbientMask_global_derivatives d k
  let C := 1+∑ k ∈ Finset.range (K+1), A k
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (K+1)) => hA k)]
  have hAC (k : ℕ) (hk : k ≤ K) : A k ≤ C := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.range (K+1)) => hA k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z
  apply ambient_mask_product_budget B
    (fun b => descriptorAmbientMask Q ρ m N σ J i b (S b) x) hC hD K z
  · exact fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x
  · intro b _
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b (S b) x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · intro b hb k _ hk
    apply (hAb k Q ρ m N σ J i b (S b) (hsep b hb) x z).trans
    exact mul_le_mul (hAC k hk)
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) (hscale b hb) k)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)
      (zero_le_one.trans hC)

theorem descriptorAmbientProduct_complex_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w =>
          (descriptorAmbientProduct Q ρ m N σ J i B S x w : ℂ)) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  obtain ⟨C,hC,hCb⟩ := descriptorAmbientProduct_global_budget d K
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z k hk
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((descriptorAmbientProduct_contDiff Q ρ m N σ J i B S x).contDiffAt (x := z))
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘
    descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤ _
  rw [hn]
  exact hCb Q ρ m N σ J i B S D hD hsep hscale x z k hk

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

theorem product_hasOrder : (product : MaskJetExpansion ι d (Space d)).HasOrder 0 := by
  intro a
  simp [product,MaskJetTerm.order,MaskJetIndex.zero]

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
theorem product_hasPointAt (z : Space d) :
    (product : MaskJetExpansion ι d (Space d)).HasPointAt z z := fun _ => rfl

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

theorem value_eq_inv_radius_normalized (j : MaskJetIndex d) (r : ℝ) (hr : r ≠ 0)
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => (f w : ℂ)) z =
      (((r⁻¹)^j.order : ℝ) : ℂ) * j.normalizedValue r f z := by
  rw [value_ofReal j f hf z,normalizedValue,Complex.ofReal_mul,← mul_assoc,
    ← Complex.ofReal_mul,← mul_pow,inv_mul_cancel₀ hr,one_pow,Complex.ofReal_one,one_mul]

end MaskJetIndex

namespace MaskJetTerm
variable {ι X E : Type*} {d : ℕ} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem value_radius_normalized (T : MaskJetTerm ι d E)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space d → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (z : E) (p : Space d)
    (hp : T.point z = p) :
    T.value (fun i x w => (B i x w : ℂ)) x z =
      T.radiusCoefficient r z * ∏ i, (T.jet i).normalizedValue (r i) (B i x) p := by
  unfold value
  rw [hp]
  have hi (i : ι) := (T.jet i).value_eq_inv_radius_normalized
    (r i) (hr i) (B i x) (hB i x) p
  simp_rw [hi]
  rw [Finset.prod_mul_distrib,← Complex.ofReal_prod]
  exact (mul_assoc _ _ _).symm

end MaskJetTerm

end Falconer

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OscillatoryExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oscillatory spatial expansion before absolute values

The product of an endpoint transform and a conjugate transform is written
as the exact two-point integral with displacement phase. The identity uses
the original spatial measures and does not assume spatial smoothness.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem exponential_mul_conj (s t : ℝ) :
    Complex.exp (Complex.I * (s : ℂ)) * star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * ((s-t : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ)) by simp [← Complex.exp_conj]]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem endpointTransform_mul_star {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M P : ℝ) (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M b r w * star (endpointTransform ν P c r w) =
      (M⁻¹ * P⁻¹) • ∫ z : Space d × Space d,
        Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ)) *
          (b z.1 w * star (c z.2 w)) ∂μ.prod ν := by
  have hid (x y : Space d) :
      (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w) *
        star (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) y : ℂ)) * c y w) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (x-y) : ℝ) : ℂ)) *
        (b x w * star (c y w)) := by
    rw [star_mul]
    have he := exponential_mul_conj (r * inner ℝ (w : Space d) x)
      (r * inner ℝ (w : Space d) y)
    push_cast at he
    rw [show r * inner ℝ (w : Space d) (x-y) =
      r * inner ℝ (w : Space d) x - r * inner ℝ (w : Space d) y by
        rw [inner_sub_right, mul_sub]]
    push_cast
    rw [← he]
    ring_nf
  simp only [endpointTransform, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [mul_comm P⁻¹ M⁻¹]
  congr 1
  change _ * conj (∫ x, _ ∂ν) = _
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => hid z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_OriginalShellIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

end PlanarFalconer

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

theorem stationary_normalized_coefficient_le {p q j : ℕ} (hpq : p+q ≤ 2*j)
    {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 1 ≤ D) (h : ℝ) :
    Λ^h*(Λ^j)⁻¹*D^(p+q) ≤ Λ^h*(D^2/Λ)^j := by
  calc
    _ ≤ Λ^h*(Λ^j)⁻¹*D^(2*j) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hpq) (by positivity)
    _ = _ := by rw [div_pow,div_eq_mul_inv,pow_mul]; ring

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

theorem normalizedAngular_restore {d : ℕ} {A : ℝ} (hA : 0 < A)
    (B : Space d → ℂ) (z : Space d) :
    (A : ℂ)*normalizedAngular A B z = B z := by
  simp only [normalizedAngular,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    mul_inv_cancel₀ hA.ne',Complex.ofReal_one,one_mul]

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTerminal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal independent angular energies in every dimension

Only the sup norm of the actual endpoint symbols and the two original
cell masses enter the stopping estimate. The radial shell measure is
normalized, so its total mass has no frequency factor.
-/

namespace Falconer
open MeasureTheory Set

theorem independentAngularEnergy_bound {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V ≤
      (2:ℝ)^((d:ℝ)*(v-a)) * (C^2*D^2*(sphereMeasure d).real univ^2) *
        (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hb : ∀ r, ‖sphereMoment U r*sphereMoment V r‖ ≤
      C^2*D^2*(sphereMeasure d).real univ^2 := by
    intro r
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
    calc
      _ ≤ (C^2*(sphereMeasure d).real univ)*(D^2*(sphereMeasure d).real univ) :=
        mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
          (sphereMoment_nonneg V r) (by positivity)
      _ = _ := by ring
  unfold independentAngularEnergy
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ) (Filter.Eventually.of_forall hb)
  have hn : 0 ≤ ∫ r, sphereMoment U r*sphereMoment V r
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
    integral_nonneg (fun r => mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))
  rw [Real.norm_eq_abs,abs_of_nonneg hn] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by ring)

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialAnnulusKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth annular inverse-distance kernels in the ambient Euclidean space. -/

namespace Falconer
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap
variable {d : ℕ}

theorem spatialAnnulusKernel_eq (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {z : Space d} (hz₁ : δ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ L) :
    spatialAnnulusKernel (d := d) δ L hδ hL j z = ↑((‖z‖^j)⁻¹) := by
  have hi : spatialInnerBump (d := d) δ hδ z = 0 :=
    (spatialInnerBump (d := d) δ hδ).zero_of_le_dist (by simpa [spatialInnerBump] using hz₁)
  have ho : spatialOuterBump (d := d) L hL z = 1 :=
    (spatialOuterBump (d := d) L hL).one_of_mem_closedBall (by simpa [spatialOuterBump] using hz₂)
  simp [spatialAnnulusKernel, hi, ho]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AllDimensionalSpatialFourierSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact separated spatial factors in every dimension. Fourier inversion is applied on Space d, with an integrable coefficient and endpoint phases of norm one. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
variable {d : ℕ}

theorem spatialFourierPhase_sub (s : ℝ) (ξ x y : Space d) :
    spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y) =
      Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • (x-y)))*Complex.I) := by
  simp only [spatialFourierPhase, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, smul_sub,
    inner_sub_right, mul_sub, Complex.ofReal_sub]
  congr 1
  ring

theorem spatialFourierCoeff_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : Integrable (spatialFourierCoeff (d := d) δ L hδ hL j) :=
  (spatialFourierCoeff (d := d) δ L hδ hL j).integrable

theorem spatialFourierSeparation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : Space d) :
    (∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y))) =
      spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (x-y)) := by
  have he := congrArg (fun f : 𝓢(Space d, ℂ) => f (s⁻¹ • (x-y)))
    (show (𝓕⁻ (𝓕 (spatialAnnulusSchwartz (d := d) δ L hδ hL j) : 𝓢(Space d, ℂ)) :
      𝓢(Space d, ℂ)) = spatialAnnulusSchwartz (d := d) δ L hδ hL j from
      FourierTransform.fourierInv_fourier_eq _)
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at he
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatialFourierPhase_sub]
  exact mul_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AllDimensionalSpatialFourierIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fubini for the original pair measure and the actual all-dimensional spatial factors. This is the spatial separation used by osc:spatial-separation. -/

namespace Falconer
open MeasureTheory Filter
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatialPairPhase_norm (s : ℝ) (ξ : Space d) (z : Space d × Space d) :
    ‖spatialPairPhase s ξ z‖ = 1 := by
  simp [spatialPairPhase, spatialFourierPhase_norm]

theorem spatialFourier_joint_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    Integrable (fun p : Space d × (Space d × Space d) =>
      spatialFourierCoeff (d := d) δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : Space d × (Space d × Space d) =>
      spatialFourierCoeff (d := d) δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) :=
    (spatialFourierCoeff (d := d) δ L hδ hL j).continuous.aestronglyMeasurable.comp_fst.mul
      ((spatialPairPhase_continuous s).aestronglyMeasurable.mul
        hA.aestronglyMeasurable.comp_snd)
  apply (((spatialFourierCoeff_integrable δ L hδ hL j).norm.comp_fst μ).mul_const C).mono' hm
  filter_upwards with p
  simp only [norm_mul, spatialPairPhase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (hb p.2) (norm_nonneg _)

theorem spatialFourier_integral_swap (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  have he (z : Space d × Space d) :
      spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z =
        ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ * (spatialPairPhase s ξ z * A z) := by
    rw [← spatialFourierSeparation, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [spatialPairPhase]
    ring
  simp_rw [he]
  simpa only [integral_const_mul] using
    (integral_integral_swap (f := fun ξ z => spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (spatialPairPhase s ξ z * A z))
      (spatialFourier_joint_integrable δ L hδ hL j s μ A hA hb)).symm


/-- The spatial factor needed after a stationary inverse term, separated into
bounded multipliers of the two original endpoints. -/
theorem spatialInverseDistance_integral_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (hsep : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2 / s ∧ dist z.1 z.2 / s ≤ L)
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, (↑((dist z.1 z.2 / s)^j)⁻¹ : ℂ) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  apply Eq.trans _ (spatialFourier_integral_swap δ L hδ hL j s μ A hA hb)
  apply integral_congr_ae
  filter_upwards [hsep] with z hz
  have hn : ‖s⁻¹ • (z.1-z.2)‖ = dist z.1 z.2 / s := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,dist_eq_norm,div_eq_inv_mul]
  rw [spatialAnnulusKernel_eq δ L hδ hL j (by simpa only [hn] using hz.1) (by simpa only [hn] using hz.2),hn,
    Complex.ofReal_inv]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialEndpoint
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint factorization of the integer spatial inverse powers -/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatial_endpoint_pair (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (M P s : ℝ) (ξ : Space d)
    (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
      star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w) =
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      spatialPairPhase s ξ z *
        (Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
          (b z.1 w*star (c z.2 w))) ∂μ.prod ν := by
  rw [endpointTransform_mul_star]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul,spatialPairPhase,starRingEnd_apply]
  ring

theorem spatial_inverse_endpoint_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
          (b z.1 w*star (c z.2 w))) ∂μ.prod ν =
    ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
        star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w)) := by
  let A : Space d × Space d → ℂ := fun z =>
    Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
      (b z.1 w*star (c z.2 w))
  have hA : Measurable A := by
    apply Measurable.mul
    · fun_prop
    · exact (hb.comp (measurable_fst.prodMk measurable_const)).mul
        (Complex.continuous_conj.measurable.comp (hc.comp (measurable_snd.prodMk measurable_const)))
  have hbound : ∀ z, ‖A z‖ ≤ B*C := by
    intro z
    have hphase : ‖Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [A,norm_mul,norm_star,hphase,one_mul]
    exact mul_le_mul (hbB _ _) (hcC _ _) (norm_nonneg _) hB
  change (M⁻¹*P⁻¹) • (∫ z, (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ)*A z ∂μ.prod ν) = _
  rw [spatialInverseDistance_integral_separation δ L hδ hL j hs (μ.prod ν) hsep A hA hbound,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatial_endpoint_pair]
  simp only [Complex.real_smul]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedCauchy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The L1 cost of the spatial Fourier separation

The coefficient is integrated before estimating the shell energy. Its
squared cost is controlled by one L1 factor and a positive weighted energy.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem norm_integral_weighted_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c F : X → ℂ) (hcm : Measurable c) (hc : Integrable c μ)
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x, c x*F x ∂μ‖^2 ≤
      (∫ x, ‖c x‖ ∂μ) * ∫ x, ‖c x‖*‖F x‖^2 ∂μ := by
  let τ := μ.withDensity (fun x => ENNReal.ofReal ‖c x‖)
  let : IsFiniteMeasure τ := isFiniteMeasure_withDensity_ofReal hc.norm.2
  have hchange (g : X → ℝ) : (∫ x, g x ∂τ) = ∫ x, ‖c x‖*g x ∂μ := by
    change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal ‖c x‖)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hcm.norm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _),smul_eq_mul]
  have hsq : Integrable (fun x => ‖F x‖^2) τ := by
    apply Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable (B^2)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x)
  have hn : Integrable (fun x => ‖F x‖) τ := by
    apply Integrable.of_bound hF.norm.aestronglyMeasurable B
    filter_upwards with x
    simpa only [norm_norm] using hb x
  have hcs := real_integral_product_sq_le τ (fun x => ‖F x‖) (fun _ => (1:ℝ))
    hsq (by simpa only [one_pow] using (integrable_const (1:ℝ) (μ := τ)))
    (by simpa only [mul_one] using hn)
  simp only [mul_one,one_pow,hchange] at hcs
  have hprod : Integrable (fun x => ‖c x‖*‖F x‖) μ := by
    apply (hc.norm.mul_const B).mono' (hcm.norm.mul hF.norm).aestronglyMeasurable
    filter_upwards with x
    change ‖‖c x‖*‖F x‖‖ ≤ ‖c x‖*B
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  have hnorm : ‖∫ x, c x*F x ∂μ‖ ≤ ∫ x, ‖c x‖*‖F x‖ ∂μ := by
    apply norm_integral_le_of_norm_le hprod
    filter_upwards with x
    rw [norm_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by
    simpa only [mul_one,mul_comm] using hcs)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialSharedBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial Fourier integration followed by sphere Cauchy--Schwarz

This transfers the actual shared-angle integral of a separated inverse term
to positive independent-angle energies, at the squared L1 cost of its
spatial Fourier coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

variable {d : ℕ}

theorem spatial_shared_integral_sq_le
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C) :
    ‖∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,w)*star (V (ξ,w)) ))
      ∂sphereMeasure d‖^2 ≤
    (∫ ξ : Space d, ‖c ξ‖) *
      ∫ ξ : Space d, ‖c ξ‖*((∫ w : Sphere d, ‖U (ξ,w)‖^2 ∂sphereMeasure d)*
        (∫ w : Sphere d, ‖V (ξ,w)‖^2 ∂sphereMeasure d)) := by
  let F : Space d → ℂ := fun ξ => ∫ w : Sphere d, U (ξ,w)*star (V (ξ,w)) ∂sphereMeasure d
  have hm : Measurable (fun z : Space d × Sphere d => U z*star (V z)) :=
    hU.mul (continuous_star.measurable.comp hV)
  have hFm : Measurable F := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hbound : ∀ z, ‖U z*star (V z)‖ ≤ B*C := by
    intro z
    rw [norm_mul,norm_star]
    exact mul_le_mul (hbU z) (hbV z) (norm_nonneg _) hB
  have hFb : ∀ ξ, ‖F ξ‖ ≤ B*C*(sphereMeasure d).real univ := by
    intro ξ
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun w => hbound (ξ,w))
  have hi : Integrable (fun z : Space d × Sphere d => c z.1*(U z*star (V z)))
      (volume.prod (sphereMeasure d)) := by
    apply ((hc.norm.comp_fst (sphereMeasure d)).mul_const (B*C)).mono'
      ((hcm.comp measurable_fst).mul hm).aestronglyMeasurable
    filter_upwards with z
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)
  have he : (∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,w)*star (V (ξ,w))))
      ∂sphereMeasure d) = ∫ ξ : Space d, c ξ*F ξ := by
    simpa only [F,integral_const_mul] using
      (integral_integral_swap (f := fun ξ w => c ξ*(U (ξ,w)*star (V (ξ,w)))) hi).symm
  rw [he]
  have hcs := norm_integral_weighted_sq_le volume c F hcm hc hFm
    (mul_nonneg (mul_nonneg hB hC) (measureReal_nonneg)) hFb
  let G : Space d → ℝ := fun ξ =>
    (∫ w : Sphere d, ‖U (ξ,w)‖^2 ∂sphereMeasure d)*
      (∫ w : Sphere d, ‖V (ξ,w)‖^2 ∂sphereMeasure d)
  have hGm : Measurable G :=
    (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.mul
      (hV.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => mul_nonneg
    (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hGb : ∀ ξ, G ξ ≤
      (B^2*(sphereMeasure d).real univ)*(C^2*(sphereMeasure d).real univ) := by
    intro ξ
    exact mul_le_mul
      (sphereMoment_le (fun z => U (ξ,z.2)) hB (fun z => hbU (ξ,z.2)) 0)
      (sphereMoment_le (fun z => V (ξ,z.2)) hC (fun z => hbV (ξ,z.2)) 0)
      (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  have hF2 : ∀ ξ, ‖F ξ‖^2 ≤ G ξ := by
    intro ξ
    simpa only [F,G,one_smul] using sphere_shared_integral_sq_le
      (fun w => U (ξ,w)) (fun w => V (ξ,w)) (fun _ => 1)
      (hU.comp (measurable_const.prodMk measurable_id))
      (hV.comp (measurable_const.prodMk measurable_id)) (by simp) hB hC
      (fun w => hbU (ξ,w)) (fun w => hbV (ξ,w))
  have hGi : Integrable (fun ξ => ‖c ξ‖*G ξ) := by
    apply (hc.norm.mul_const ((B^2*(sphereMeasure d).real univ)*
      (C^2*(sphereMeasure d).real univ))).mono' (hcm.norm.mul hGm).aestronglyMeasurable
    filter_upwards with ξ
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (hG0 ξ))]
    exact mul_le_mul_of_nonneg_left (hGb ξ) (norm_nonneg _)
  have hFi : Integrable (fun ξ => ‖c ξ‖*‖F ξ‖^2) := by
    apply hGi.mono' (hcm.norm.mul (hFm.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards with ξ
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hF2 ξ) (norm_nonneg _)
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (integral_mono hFi hGi (fun ξ => mul_le_mul_of_nonneg_left (hF2 ξ) (norm_nonneg _)))
    (integral_nonneg fun _ => norm_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_SpatialSharedShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform independent-angle control removes the spatial Fourier variable

The spatial coefficient pays its squared L1 norm. All exchanges of the
radial and spatial integrations follow from bounded measurable endpoint
families and the finite original shell measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem spatialSharedAmplitude_measurable {d : ℕ} (c : Space d → ℂ)
    (hcm : Measurable c) (U V : Space d × (ℝ × Sphere d) → ℂ)
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (spatialSharedAmplitude c U V) := by
  have hUV : Measurable (fun p : (ℝ × Sphere d) × Space d =>
      c p.2*(U (p.2,p.1)*star (V (p.2,p.1)))) :=
    (hcm.comp measurable_snd).mul ((hU.comp measurable_swap).mul
      (continuous_star.measurable.comp (hV.comp measurable_swap)))
  exact hUV.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem spatial_shared_shell_le {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (E : ℝ) (hE : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U (ξ,p)) (fun p => V (ξ,p)) ≤ E) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      (∫ r : ℝ, ‖spatialSharedAmplitude c U V r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (∫ ξ : Space d, ‖c ξ‖)^2*E := by
  let μ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  let ℓ := ∫ ξ : Space d, ‖c ξ‖
  let N := (2 : ℝ)^((d : ℝ)*(v-a))
  let G : Space d × ℝ → ℝ := fun p =>
    sphereMoment (fun z => U (p.1,z)) p.2 * sphereMoment (fun z => V (p.1,z)) p.2
  let I : ℝ → ℝ := fun r => ∫ ξ : Space d, ‖c ξ‖*G (ξ,r)
  have hℓ : 0 ≤ ℓ := integral_nonneg (fun _ => norm_nonneg _)
  have hN : 0 ≤ N := Real.rpow_nonneg (by norm_num) _
  have hU' : Measurable (fun p : (Space d × ℝ) × Sphere d => U (p.1.1,(p.1.2,p.2))) :=
    hU.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hV' : Measurable (fun p : (Space d × ℝ) × Sphere d => V (p.1.1,(p.1.2,p.2))) :=
    hV.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hGm : Measurable G :=
    (hU'.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.mul
      (hV'.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg
    (sphereMoment_nonneg _ _) (sphereMoment_nonneg _ _)
  let K := (B^2*(sphereMeasure d).real univ)*(C^2*(sphereMeasure d).real univ)
  have hGb (p : Space d × ℝ) : G p ≤ K :=
    mul_le_mul (sphereMoment_le (fun z => U (p.1,z)) hB (fun z => hbU (p.1,z)) p.2)
      (sphereMoment_le (fun z => V (p.1,z)) hC (fun z => hbV (p.1,z)) p.2)
      (sphereMoment_nonneg _ _) (by positivity)
  have hi : Integrable (fun p : Space d × ℝ => ‖c p.1‖*G p) (volume.prod μ) := by
    apply ((hc.norm.comp_fst μ).mul_const K).mono'
      ((hcm.norm.comp measurable_fst).mul hGm).aestronglyMeasurable
    filter_upwards with p
    change ‖‖c p.1‖*G p‖ ≤ ‖c p.1‖*K
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (hG0 p))]
    exact mul_le_mul_of_nonneg_left (hGb p) (norm_nonneg _)
  have hIi : Integrable I μ := hi.integral_prod_right
  have hpoint (r : ℝ) : ‖spatialSharedAmplitude c U V r‖^2 ≤ ℓ*I r := by
    exact spatial_shared_integral_sq_le c hcm hc
      (fun p => U (p.1,(r,p.2))) (fun p => V (p.1,(r,p.2)))
      (hU.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      (hV.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      hB hC (fun p => hbU (p.1,(r,p.2))) (fun p => hbV (p.1,(r,p.2)))
  have hFi : Integrable (fun r => ‖spatialSharedAmplitude c U V r‖^2) μ := by
    apply (hIi.const_mul ℓ).mono'
      ((spatialSharedAmplitude_measurable c hcm U V hU hV).norm.pow_const 2).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hpoint r
  have hswap : (∫ r, I r ∂μ) = ∫ ξ : Space d, ‖c ξ‖*(∫ r, G (ξ,r) ∂μ) := by
    simpa only [I,integral_const_mul] using
      (integral_integral_swap (f := fun ξ r => ‖c ξ‖*G (ξ,r)) hi).symm
  have hQi : Integrable (fun ξ : Space d => ‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) := by
    simpa only [integral_const_mul] using hi.integral_prod_left
  have hbound : N*(∫ r, I r ∂μ) ≤ ℓ*E := by
    rw [hswap,← integral_const_mul]
    calc
      _ ≤ ∫ ξ : Space d, ‖c ξ‖*E :=
        integral_mono (hQi.const_mul N) (hc.norm.mul_const E) (fun ξ => by
          have he := mul_le_mul_of_nonneg_left (hE ξ) (norm_nonneg (c ξ))
          change N*(‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) ≤ ‖c ξ‖*E
          have hid : N*(‖c ξ‖*(∫ r, G (ξ,r) ∂μ)) =
              ‖c ξ‖*independentAngularEnergy a v Ψ (fun p => U (ξ,p)) (fun p => V (ξ,p)) := by
            dsimp only [independentAngularEnergy,N,G,μ]
            ring
          rw [hid]
          exact he)
      _ = ℓ*E := integral_mul_const E _
  change N*(∫ r, ‖spatialSharedAmplitude c U V r‖^2 ∂μ) ≤ ℓ^2*E
  calc
    _ ≤ N*(∫ r, ℓ*I r ∂μ) := mul_le_mul_of_nonneg_left
      (integral_mono hFi (hIi.const_mul ℓ) hpoint) hN
    _ = ℓ*(N*(∫ r, I r ∂μ)) := by rw [integral_const_mul]; ring
    _ ≤ ℓ*(ℓ*E) := mul_le_mul_of_nonneg_left hbound hℓ
    _ = _ := by ring

theorem spatial_fourier_shared_shell_le {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (E : ℝ) (hE : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U (ξ,p)) (fun p => V (ξ,p)) ≤ E) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      (∫ r : ℝ, ‖spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j) U V r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (spatialFourierCost (d := d) δ L hδ hL j)^2*E :=
  spatial_shared_shell_le a v Ψ (spatialFourierCoeff δ L hδ hL j)
    (spatialFourierCoeff (d := d) δ L hδ hL j).continuous.measurable
    (spatialFourierCoeff_integrable δ L hδ hL j) U V hU hV hB hC hbU hbV E hE

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialEndpointFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual endpoint family in the spatial Fourier shell bound

Spatial frequencies are parameters of bounded modulus-one multipliers.
The original endpoint laws and model masses are unchanged.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatialEndpointFamily_measurable (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (M s : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) : Measurable (spatialEndpointFamily μ M s b) := by
  have hm : Measurable (fun z : (Space d × (ℝ × Sphere d)) × Space d =>
      Complex.exp (Complex.I * (z.1.2.1 : ℂ) * (inner ℝ (z.1.2.2 : Space d) z.2 : ℂ)) *
        (spatialFourierPhase s z.1.1 z.2*b z.2 z.1.2.2)) := by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.mul
      · unfold spatialFourierPhase
        fun_prop
      · exact hb.comp (measurable_snd.prodMk measurable_fst.snd.snd)
  have hi : Measurable (fun p : Space d × (ℝ × Sphere d) =>
      ∫ x, Complex.exp (Complex.I * (p.2.1 : ℂ) *
        (inner ℝ (p.2.2 : Space d) x : ℂ)) *
        (spatialFourierPhase s p.1 x*b x p.2.2) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact hi.const_smul (M⁻¹ : ℝ)

theorem spatialEndpointFamily_norm_le (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {M : ℝ} (hM : 0 < M) (s : ℝ) (b : Space d → Sphere d → ℂ)
    {B : ℝ} (hB : ∀ x w, ‖b x w‖ ≤ B) (p : Space d × (ℝ × Sphere d)) :
    ‖spatialEndpointFamily μ M s b p‖ ≤ B*μ.real univ/M := by
  apply endpointTransform_norm_le μ hM _ _ p.2.1 p.2.2
  intro x w
  rw [norm_mul,spatialFourierPhase_norm,one_mul]
  exact hB x w

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

theorem inverse_product_term_radius_normalized (m j : ℕ)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    ∀ a : T.index,
      (T.term a).value (fun i x z => (B i x z : ℂ)) x e =
        (T.term a).radiusCoefficient r e *
          ∏ i, ((T.term a).jet i).normalizedValue (r i) (B i x) e := by
  intro T a
  by_cases he : stationaryPatchMask m e = 0
  · have hc : (T.term a).coefficient e = 0 := inverse_coefficient_eq_zero m j product a e he
    simp only [MaskJetTerm.value,MaskJetTerm.radiusCoefficient,hc,zero_mul]
  · have hnear : ‖(e : Space (m+3))-
        (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 :=
      (poleCutoff_support _ _ he).le.trans (by norm_num)
    exact (T.term a).value_radius_normalized r hr B hB x e e
      ((product_hasPointAt (ι := ι) (e : Space (m+3))).inverse hnear j a)

/-- The finite normalized expansion holds everywhere on the sphere. -/
theorem localInverseAmplitude_product_radius_jets_global (m j : ℕ)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    localInverseAmplitude m (fun z => ∏ i, (B i x z : ℂ)) j e =
      ∑ a : T.index, (T.term a).radiusCoefficient r e *
        ∏ i, ((T.term a).jet i).normalizedValue (r i) (B i x) e := by
  intro T
  have hcomplex (i : ι) (x : X) : ContDiff ℝ ∞ (fun z => (B i x z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hB i x)
  have hvalue := inverse_value m j product (fun i x z => (B i x z : ℂ)) hcomplex x e
  have hproduct : (product : MaskJetExpansion ι (m+3) (Space (m+3))).value
      (fun i x z => (B i x z : ℂ)) x = fun z => ∏ i, (B i x z : ℂ) :=
    funext (product_value _ x)
  rw [hproduct] at hvalue
  rw [← hvalue]
  apply Finset.sum_congr rfl
  intro a _
  exact inverse_product_term_radius_normalized m j r hr B hB x e a

end MaskJetExpansion

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial term count in the individual-mask inverse expansion -/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [Fintype ι] in
theorem card_sum {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E) :
    Fintype.card (sum S).index = ∑ j, Fintype.card (S j).index :=
  Fintype.card_sigma

theorem card_derivative [DecidableEq ι] (S : MaskJetExpansion ι d E) (v : E) :
    Fintype.card (S.derivative v).index =
      Fintype.card S.index * (1+Fintype.card ι*d) := by
  change Fintype.card (S.index × (Unit ⊕ (ι × Fin d))) = _
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_unique (α := Unit),Fintype.card_prod,
    Fintype.card_fin]

theorem card_laplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) :
    Fintype.card (S.laplacian v).index =
      Fintype.card S.index * n * (1+Fintype.card ι*d)^2 := by
  rw [laplacian,card_sum]
  simp_rw [card_derivative]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem card_iteratedLaplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) (j : ℕ) :
    Fintype.card (S.iteratedLaplacian v j).index =
      Fintype.card S.index * n^j * (1+Fintype.card ι*d)^(2*j) := by
  induction j with
  | zero =>
    change Fintype.card S.index = _
    simp only [Nat.mul_zero,pow_zero,Nat.mul_one]
  | succ j ih =>
    change Fintype.card (((fun T : MaskJetExpansion ι d E => T.laplacian v)^[j+1]) S).index = _
    rw [Function.iterate_succ_apply',card_laplacian]
    change Fintype.card (S.iteratedLaplacian v j).index * _ * _ = _
    rw [ih,show 2*(j+1)=2*j+2 by omega,pow_add,pow_succ]
    ring

theorem card_stationaryJet [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.stationaryJet m j).index =
      Fintype.card S.index * (m+2)^j * (1+Fintype.card ι*d)^(2*j) := by
  change Fintype.card
    ((((S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulFixed
      (SmoothSeparation.stationaryJointDensity m)
      (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian
        (verticalDirections (m+2)) j)).index = _
  rw [card_iteratedLaplacian]
  rfl

theorem card_inverse [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.inverse m j).index =
      Fintype.card S.index * inverseMultiplicity (m+2) j *
        (1+Fintype.card ι*d)^(2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [MaskJetExpansion.inverse,inverseMultiplicity]
    | succ j =>
      rw [MaskJetExpansion.inverse,card_mulFixed,card_sum,inverseMultiplicity]
      simp_rw [card_stationaryJet]
      have hterm (h : Fin (j+1)) :
          Fintype.card (S.inverse m (j-h)).index * (m+2)^((h:ℕ)+1) *
            (1+Fintype.card ι*d)^(2*((h:ℕ)+1)) =
          Fintype.card S.index * (1+Fintype.card ι*d)^(2*(j+1)) *
            (inverseMultiplicity (m+2) (j-h) * (m+2)^((h:ℕ)+1)) := by
        rw [ih (j-h) (by have hh := h.isLt; omega)]
        have hp : 2*(j-h)+2*((h:ℕ)+1) = 2*(j+1) := by have hh := h.isLt; omega
        rw [← hp,pow_add]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring

theorem card_inverse_product [DecidableEq ι] (m j : ℕ) :
    Fintype.card ((product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j).index =
      inverseMultiplicity (m+2) j * (1+Fintype.card ι*(m+3))^(2*j) := by
  rw [card_inverse]
  change 1 * _ * _ = _
  rw [one_mul]

end Falconer.MaskJetExpansion

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

omit [Fintype ι] [DecidableEq ι] in
theorem seed_geometryCoveredBy_unit (k : ι → MaskJetIndex d) :
    (seed k).GeometryCoveredBy (product : MaskJetExpansion Unit d (Space d)) :=
  fun _ => ⟨(),rfl,rfl⟩

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

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

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

theorem spatial_inverse_sphere_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d ∂μ.prod ν =
    ∫ w : Sphere d, (∫ ξ : Space d, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
        star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w)))
      ∂sphereMeasure d := by
  let K : Sphere d × (Space d × Space d) → ℂ := fun p =>
    (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
      (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
        (b p.2.1 p.1*star (c p.2.2 p.1)))
  have hi : Integrable K ((sphereMeasure d).prod (μ.prod ν)) :=
    spatial_inverse_sphere_joint_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) b c hb hc hB hbB hcC r
  have hswap := (integral_integral_swap (f := fun w z => K (w,z)) hi).symm
  have he : (∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d ∂μ.prod ν) =
        ∫ w : Sphere d, ∫ z : Space d × Space d, K (w,z) ∂μ.prod ν ∂sphereMeasure d := by
    simpa only [K,integral_const_mul] using hswap
  rw [he,← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  exact spatial_inverse_endpoint_separation δ L hδ hL j hs μ ν hsep M P b c hb hc hB hbB hcC r w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NorthRotation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sending the prepared direction to the canonical north pole

An orthogonal reflection handles every equal-norm pair, including opposite
directions. Normalization and all cap distances commute with this fixed
linear isometry, so the original prepared cap can be transported exactly.
-/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem linearIsometryEquiv_normalize {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) : normalize (e x) = e (normalize x) := by
  simp only [NormedSpace.normalize,e.norm_map,map_smul]

theorem linearIsometryEquiv_normalize_sub {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y : Space d) : normalize (e x-e y) = e (normalize (x-y)) := by
  rw [← map_sub,linearIsometryEquiv_normalize]

theorem linearIsometryEquiv_cap_norm {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y u : Space d) :
    ‖normalize (e x-e y)-e u‖ = ‖normalize (x-y)-u‖ := by
  rw [linearIsometryEquiv_normalize_sub,← map_sub,e.norm_map]

theorem northRotation_cap_norm {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    ‖normalize (northRotation u x-northRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ =
      ‖normalize (x-y)-(u : Space (n+1))‖ := by
  rw [← northRotation_apply u]
  exact linearIsometryEquiv_cap_norm (northRotation u) x y u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ScalarAngularShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension-exact scalar to angular shell normalization

The one-dimensional shell comparison is independent of ambient dimension.
The stationary factor contributes exactly the remaining d-1 powers.
-/

namespace Falconer
open Set MeasureTheory

theorem scalar_angular_shell_normalization (d : ℕ) (a v : ℝ) :
    (2:ℝ)^(-a)*(2:ℝ)^v*((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2 =
      (2:ℝ)^((d:ℝ)*(v-a)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num),← Real.rpow_add (by norm_num)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorDerivativeScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derivative scale for the actual descriptor family

The fixed derivative constants and polynomial list size are absorbed before
choosing any cells, net points or descriptor family. The retained scale
remembers the largest nominal descriptor length.
-/

namespace Falconer
open Set MeasureTheory

theorem descriptorDerivativeScale_ge_one (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) :
    1 ≤ descriptorDerivativeScale N σ L := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) hσ
  · exact le_max_left _ _

theorem uniform_descriptor_global_scale (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (f : ℝ → ℝ) (J i L : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
      (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      B.card ≤ (N+1)^P → (∀ b ∈ B, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w => (descriptorAmbientProduct Q ρ f N σ J i B S x w : ℂ)) z‖ ≤
          (descriptorDerivativeScale N σ L)^k := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientProduct_complex_global_budget d K
  obtain ⟨N₁,hcount⟩ := descriptor_count_subpower P (half_pos hσ)
  obtain ⟨N₂,hconst⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) (8*C)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q ρ f J i L B S hcard hlength hsep x z k hk
  let W := max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))
  have hW : 0 ≤ W := (zero_le_one.trans (le_max_left _ _))
  have hc := hcount N ((le_max_left _ _).trans hN) B hcard
  have hC' := hconst N ((le_max_right _ _).trans hN)
  have hs : (B.card:ℝ)*C*(8*W) ≤ descriptorDerivativeScale N σ L := by
    calc
      _ = ((B.card:ℝ)*(8*C))*W := by ring
      _ ≤ (((2:ℝ)^N)^(σ/2)*((2:ℝ)^N)^(σ/2))*W :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc hC' (by positivity) (by positivity)) hW
      _ = descriptorDerivativeScale N σ L := by
        rw [← Real.rpow_add (by positivity),show σ/2+σ/2 = σ by ring]
        rfl
  have hb := hbound Q ρ f N σ J i B S (8*W) (by positivity) hsep
    (fun b hb => descriptorMaskRadius_inv_le N σ b (hlength b hb)) x z k hk
  exact hb.trans (pow_le_pow_left₀ (by positivity) hs k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorInverseRegime
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual descriptor derivative scale is in the inverse regime

The high-frequency condition and the retained descriptor length give a
uniform gap between the squared derivative scale and the oscillation.
The fixed shell factor four is absorbed before selecting any cells.
-/

namespace Falconer

theorem descriptorDerivativeScale_inverse_regime (N L : ℕ) {σ q : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hLN : L ≤ N)
    (hq : 20*σ*(N : ℝ) ≤ q) (hL : (L : ℝ) ≤ q/2+σ*(N : ℝ)) :
    1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      (descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q ≤ ((2 : ℝ)^N)^(-18*σ) :=
  ⟨descriptorDerivativeScale_ge_one N hσ.le L,
    descriptorDerivativeScale_le_square N L hσ.le hσ1 hLN,
    descriptorDerivativeScale_inverse_ratio N L hσ.le hq hL⟩

theorem eventual_descriptor_inverse_frequency {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (q Λ : ℝ), L ≤ N →
      20*σ*(N : ℝ) ≤ q → (L : ℝ) ≤ q/2+σ*(N : ℝ) →
      (2 : ℝ)^q/4 ≤ Λ →
      1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      1 ≤ Λ ∧ (descriptorDerivativeScale N σ L)^2/Λ ≤ ((2 : ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ 4
  refine ⟨N₀,?_⟩
  intro N hN L q Λ hLN hq hL hΛ
  obtain ⟨hD,hDupper,hratio⟩ := descriptorDerivativeScale_inverse_regime N L hσ hσ1 hLN hq hL
  have hσN : 0 ≤ σ*(N : ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hRq : ((2 : ℝ)^N)^σ ≤ (2 : ℝ)^q := by
    rw [dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hfour : 4 ≤ (2 : ℝ)^q := (hN₀ N hN).trans hRq
  have hΛ1 : 1 ≤ Λ := (by linarith : (1 : ℝ) ≤ (2 : ℝ)^q/4).trans hΛ
  refine ⟨hD,hDupper,hΛ1,?_⟩
  calc
    _ ≤ (descriptorDerivativeScale N σ L)^2/((2 : ℝ)^q/4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΛ
    _ = 4*((descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q) := by ring
    _ ≤ 4*((2 : ℝ)^N)^(-18*σ) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ ((2 : ℝ)^N)^σ*((2 : ℝ)^N)^(-18*σ) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2 : ℝ)^N)^(-17*σ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

theorem dyadic_shell_frequency_lower {a v r : ℝ} (hr : (2 : ℝ)^v/4 ≤ r) :
    (2 : ℝ)^(v-a)/4 ≤ r*(2 : ℝ)^(-a) := by
  calc
    _ = ((2 : ℝ)^v/4)*(2 : ℝ)^(-a) := by
      rw [div_mul_eq_mul_div,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DistanceLinearization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual distance Taylor error for the suffix reduction

The error estimate is dimension independent before insertion of the cube
diameter. Its proof is the exact squared-norm identity, so no differentiable
extension across the diagonal is needed.
-/

namespace Falconer
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem pair_displacement_bound (x y c₁ c₂ : E) {δ₁ δ₂ : ℝ}
    (h₁ : ‖x-c₁‖ ≤ δ₁) (h₂ : ‖y-c₂‖ ≤ δ₂) :
    ‖(x-y)-(c₁-c₂)‖ ≤ δ₁+δ₂ := by
  have he : (x-y)-(c₁-c₂) = (x-c₁)-(y-c₂) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add h₁ h₂)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

theorem DyadicCube.separated_pairs_lower {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*((d:ℝ)+1)*P.side ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    100*((d:ℝ)+1)*P.side ≤ ‖x-y‖ := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hnorm : ‖P.center-Q.center‖ ≤ ‖x-y‖+‖(x-y)-(P.center-Q.center)‖ := by
    have he : P.center-Q.center = (x-y)-((x-y)-(P.center-Q.center)) := by abel
    calc
      _ = ‖(x-y)-((x-y)-(P.center-Q.center))‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateOperations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root symbols and Fourier operations in the exact descriptor class -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped ContDiff

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem spatialMultiplier_value (f : DescriptorJetSymbol n K L F D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (f.spatialMultiplier c hc hcb).value Q ρ m N σ J i S A x w =
      c x*f.value Q ρ m N σ J i S A x w := by
  simp only [value,multiplier,spatialMultiplier]
  ring

 theorem conj_value (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    f.conj.value Q ρ m N σ J i S A x w = star (f.value Q ρ m N σ J i S A x w) := by
  simp only [value,multiplier,conj,map_mul,map_prod,descriptorJetProduct,
    normalizedDescriptorJet,Complex.star_def,Complex.conj_ofReal]
  rfl

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizedCellCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem jetStateBound_nonneg {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ jetStateBound K A μ ν M P a v Ψ := by
  unfold jetStateBound
  positivity

 theorem jetStateEnergy_bound {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateBound K A μ ν M P a v Ψ := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  unfold jetStateBound
  apply independentAngularEnergy_bound a v Ψ
  · positivity
  · positivity
  · intro z
    exact endpointTransform_norm_le μ hM _ (f.value_norm_le Q ρ m N σ J i S hF hA) z.1 z.2
  · intro z
    exact endpointTransform_norm_le ν hP _ (g.value_norm_le Q ρ m N σ J i S hG hA) z.1 z.2

 theorem jetStateValues_bddAbove {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    BddAbove (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ) := by
  refine ⟨jetStateBound K A μ ν M P a v Ψ,?_⟩
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact jetStateBound_nonneg K A μ ν M P a v Ψ
  · exact jetStateEnergy_bound Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ f g

 theorem jetStateEnergy_le_envelope {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ :=
  le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ)
    (Or.inr ⟨f,g,rfl⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetIsometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometry transport keeps the original individual mask jets -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

theorem normalizedValue_comp_isometry (j : MaskJetIndex d) (T : Space d ≃ₗᵢ[ℝ] Space d)
    (r : ℝ) {B : Space d → ℝ} (hB : ContDiff ℝ ∞ B) (z : Space d) :
    j.normalizedValue r (B ∘ T) z = (j.mapIsometry T).normalizedValue r B (T z) := by
  unfold normalizedValue
  change ((r^j.order*(iteratedFDeriv ℝ j.order
    (B ∘ (T.toContinuousLinearEquiv.toContinuousLinearMap : Space d → Space d)) z) j.vectors:ℝ):ℂ) = _
  rw [T.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hB z (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  rfl

end MaskJetIndex

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

theorem rotatedInverseAmplitude_product_radius_jets (m j : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let S := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    rotatedInverseAmplitude m T (fun z => ∏ i, (B i x z:ℂ)) j e =
      ∑ a : S.index, (S.term a).radiusCoefficient r (T e) *
        ∏ i, (((S.term a).jet i).mapIsometry T.symm).normalizedValue (r i) (B i x) e := by
  intro S
  have hh := localInverseAmplitude_product_radius_jets_global m j r hr
    (fun i x => B i x ∘ T.symm) (fun i x => (hB i x).comp T.symm.contDiff) x (sphereMap T e)
  change localInverseAmplitude m (fun z => ∏ i, (B i x (T.symm z):ℂ)) j (T e) = _ at hh
  change localInverseAmplitude m (fun z => ∏ i, (B i x (T.symm z):ℂ)) j (T e) = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [MaskJetIndex.normalizedValue_comp_isometry _ _ _ (hB i x)]
  simp only [sphereMap,T.symm_apply_apply]
  rfl

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_RotatedInverseSymbols
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform original-mask symbols for a rotated inverse patch -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem rotated_inverse_coefficient_symbol (m j L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (F : Finset PolicyDescriptor)
      (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F),
      let g := normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
      ContDiff ℝ ∞ g ∧
      (∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t g w‖ ≤ (1:ℝ)^t) ∧
      ChartSymbolControl L (fun (_ : Space (m+3)) (w : Sphere (m+3)) => g w) 1 1 := by
  obtain ⟨C,hC,hcoeff⟩ := inverse_seed_coefficient_budget m j L
  obtain ⟨H,hH,hnormalize⟩ := ambient_angular_normalization (m+1) L
  refine ⟨H*C,one_le_mul_of_one_le_of_one_le hH hC,?_⟩
  intro F T a
  let B := (rootInverseTerm m j F a).coefficient
  have hB : ContDiff ℝ ∞ (B ∘ T) := (rootInverseTerm m j F a).coefficient_smooth.comp T.contDiff
  have hb : ∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t (B ∘ T) w‖ ≤ C*(1:ℝ)^t := by
    intro t ht w
    rw [T.norm_iteratedFDeriv_comp_right,one_pow,mul_one]
    exact hcoeff ({b // b ∈ F} ⊕ {b // b ∈ F}) (fun _ => MaskJetIndex.zero (m+3)) a t ht (sphereMap T w)
  exact hnormalize (B ∘ T) hB C 1 (zero_lt_one.trans_le hC) le_rfl hb

theorem rootInverseLeftJets_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    (∑ b ∈ F, (rootInverseLeftJets m j F T a b).order) ≤ 2*j := by
  have h := (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse j a
  change (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 0+2*j at h
  rw [Fintype.sum_sum_type] at h
  have he : (∑ b ∈ F, (rootInverseLeftJets m j F T a b).order) =
      ∑ b : {b // b ∈ F}, ((rootInverseTerm m j F a).jet (.inl b)).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [rootInverseLeftJets,dite_eq_left b.property,MaskJetIndex.mapIsometry]
  rw [he]
  omega

theorem rootInverseRightJets_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    (∑ b ∈ F, (rootInverseRightJets m j F T a b).order) ≤ 2*j := by
  have h := (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse j a
  change (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 0+2*j at h
  rw [Fintype.sum_sum_type] at h
  have he : (∑ b ∈ F, (rootInverseRightJets m j F T a b).order) =
      ∑ b : {b // b ∈ F}, ((rootInverseTerm m j F a).jet (.inr b)).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [rootInverseRightJets,dite_eq_left b.property,MaskJetIndex.mapIsometry]
  rw [he]
  omega

theorem exists_rotatedRootSymbols (m j L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (F : Finset PolicyDescriptor)
      (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)), Nonempty (RotatedRootSymbols m j L F T A) := by
  obtain ⟨A,hA,hcoeff⟩ := rotated_inverse_coefficient_symbol m j L
  refine ⟨A,hA,?_⟩
  intro F T
  let base := DescriptorJetSymbol.base (n := m+1) F (2*j) L 1 (by norm_num)
    (fun _ => 1) measurable_const (by simp)
  let left (a : RootInverseIndex m j F) : DescriptorJetSymbol (m+1) (2*j) L F 1 :=
    { base with
      jet := rootInverseLeftJets m j F T a
      order_le := rootInverseLeftJets_order m j F T a
      angular := normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
      angular_smooth := (hcoeff F T a).1
      angular_derivative := (hcoeff F T a).2.1
      angular_control := (hcoeff F T a).2.2 }
  let right (a : RootInverseIndex m j F) : DescriptorJetSymbol (m+1) (2*j) L F 1 :=
    { base with jet := rootInverseRightJets m j F T a, order_le := rootInverseRightJets_order m j F T a }
  exact ⟨⟨left,right,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseExpansion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rotated inverse on the original two endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace RotatedRootSymbols
variable {m j L : ℕ} {F : Finset PolicyDescriptor}
  {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} {A : ℝ}

theorem left_value (H : RotatedRootSymbols m j L F T A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U : ℝ) (a : RootInverseIndex m j F) (x : Space (m+3)) (w : Sphere (m+3)) :
    (H.left a).value Q ρ profile N σ J i S U x w =
      (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w) *
      ((U⁻¹:ℝ):ℂ)*normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T) w := by
  simp only [DescriptorJetSymbol.value,DescriptorJetSymbol.multiplier,descriptorJetProduct,H.left_spatial,
    H.left_angular,one_mul,id_eq]
  rw [H.left_jet a]
  rw [← Finset.prod_coe_sort]
  have hp : (∏ b : {b // b ∈ F},
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (rootInverseLeftJets m j F T a b).order (rootInverseLeftJets m j F T a b).vectors x w) =
      ∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w := by
    apply Finset.prod_congr rfl
    intro b _
    have hj : rootInverseLeftJets m j F T a b =
        ((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm := by
      unfold rootInverseLeftJets
      exact dite_eq_left b.property
    rw [hj]
    rfl
  change (∏ b : {b // b ∈ F}, _) * _ = _
  rw [hp]
  ring

theorem right_value (H : RotatedRootSymbols m j L F T A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U : ℝ) (a : RootInverseIndex m j F) (y : Space (m+3)) (w : Sphere (m+3)) :
    (H.right a).value Q ρ profile N σ J i S U y w =
      (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) y) w) *
      ((U⁻¹:ℝ):ℂ) := by
  simp only [DescriptorJetSymbol.value,DescriptorJetSymbol.multiplier,descriptorJetProduct,H.right_spatial,
    H.right_angular,one_mul,mul_one,id_eq]
  rw [H.right_jet a]
  rw [← Finset.prod_coe_sort]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  have hj : rootInverseRightJets m j F T a b =
      ((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm := by
    unfold rootInverseRightJets
    exact dite_eq_left b.property
  rw [hj]
  rfl

theorem expansion (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {U : ℝ} (hU : 0 < U) (x y : Space (m+3)) (w : Sphere (m+3)) :
    rotatedInverseAmplitude m T (descriptorPairAmplitude Q ρ profile N σ J i F S x y) j w =
      ∑ a : RootInverseIndex m j F, ((rootInverseWeight m j F N σ a*(U*A)*U:ℝ):ℂ) *
        ((H.left a).value Q ρ profile N σ J i S U x w *
          (H.right a).value Q ρ profile N σ J i S U y w) := by
  let B : ({b // b ∈ F} ⊕ {b // b ∈ F}) → (Space (m+3) × Space (m+3)) → Space (m+3) → ℝ :=
    fun b xy => Sum.elim (fun c : {b // b ∈ F} => descriptorAmbientMask Q ρ profile N σ J i c (S c) xy.1)
      (fun c : {b // b ∈ F} => descriptorAmbientMask Q ρ profile N σ J i c (S c) xy.2) b
  have hB (b) (xy : Space (m+3) × Space (m+3)) : ContDiff ℝ ∞ (B b xy) := by
    cases b with
    | inl b => exact descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) xy.1
    | inr b => exact descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) xy.2
  have hp : descriptorPairAmplitude Q ρ profile N σ J i F S x y =
      fun z => ∏ b, (B b (x,y) z:ℂ) := by
    funext z
    simp only [B,descriptorPairAmplitude,descriptorAmbientProduct,Fintype.prod_sum_type,
      Sum.elim_inl,Sum.elim_inr,Complex.ofReal_prod]
    rw [← Finset.prod_coe_sort F,← Finset.prod_coe_sort F]
  rw [hp]
  have hr : ∀ b, rootInverseRadii F N σ b ≠ 0 := by
    intro b
    cases b with
    | inl b => exact (descriptorMaskRadius_pos N σ b).ne'
    | inr b => exact (descriptorMaskRadius_pos N σ b).ne'
  rw [MaskJetExpansion.rotatedInverseAmplitude_product_radius_jets m j T _ hr B hB (x,y) w]
  apply Finset.sum_congr rfl
  intro a _
  change (rootInverseTerm m j F a).radiusCoefficient (rootInverseRadii F N σ) (T w) *
      (∏ b, (((rootInverseTerm m j F a).jet b).mapIsometry T.symm).normalizedValue
        (rootInverseRadii F N σ b) (B b (x,y)) w) = _
  rw [MaskJetTerm.radiusCoefficient]
  change (rootInverseTerm m j F a).coefficient (T w) * (rootInverseWeight m j F N σ a : ℂ) *
      (∏ b, (((rootInverseTerm m j F a).jet b).mapIsometry T.symm).normalizedValue
        (rootInverseRadii F N σ b) (B b (x,y)) w) = _
  rw [Fintype.prod_sum_type,H.left_value,H.right_value]
  simp only [rootInverseRadii,B,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_mul]
  have hn := normalizedAngular_restore hA ((rootInverseTerm m j F a).coefficient ∘ T) (w:Space (m+3))
  simp only [Function.comp_apply] at hn
  have hu : (U:ℂ)*(U⁻¹:ℝ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hU.ne',Complex.ofReal_one]
  rw [← hn]
  symm
  calc
    _ = ((A:ℂ)*normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T) w) *
        (rootInverseWeight m j F N σ a : ℂ) *
        ((∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
          (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w) *
        (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm).normalizedValue
          (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) y) w)) *
        ((U:ℂ)*(U⁻¹:ℝ))*((U:ℂ)*(U⁻¹:ℝ)) := by ring
    _ = _ := by rw [hu]; ring

end RotatedRootSymbols
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_NormalizedShellCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform radial coefficients after the stationary shell normalization

The inverse order pays for the sum of the two endpoint derivative orders.
The remaining radial ratio is bounded on the fixed shell, independently of
its frequency and cell depth.
-/

namespace Falconer

theorem normalized_stationary_coefficient_le {p q j : ℕ}
    (hpq : p+q ≤ 2*j) {Λ D s h : ℝ} (hΛ : 0 < Λ) (hD : 1 ≤ D)
    (hs : 0 < s) (hh : 0 ≤ h) (hDΛ : D^2 ≤ Λ) (hΛs : Λ ≤ 4*s) :
    |Λ^h*(Λ^j)⁻¹*D^(p+q)/(s^h)| ≤ 4^h := by
  have hc : 0 ≤ Λ^h*(Λ^j)⁻¹*D^(p+q) := by positivity
  rw [abs_of_nonneg (div_nonneg hc (Real.rpow_nonneg hs.le _))]
  have hratio : D^2/Λ ≤ 1 := (div_le_one hΛ).mpr hDΛ
  have hpow : (D^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) hratio
  have hnum : Λ^h*(Λ^j)⁻¹*D^(p+q) ≤ Λ^h :=
    (stationary_normalized_coefficient_le hpq hΛ hD h).trans
      ((mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hΛ.le _)).trans_eq (mul_one _))
  calc
    _ ≤ Λ^h/s^h := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hs.le _)
    _ = (Λ/s)^h := (Real.div_rpow hΛ.le hs.le h).symm
    _ ≤ 4^h := Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hs).mpr hΛs) hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseCoefficient
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact added-order radius cost in the rotated root inverse -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem rootInverseTerm_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (a : RootInverseIndex m j F) :
    (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 2*j := by
  simpa only [MaskJetTerm.order,Nat.zero_add,rootInverseTerm] using
    (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse (m := m) j a

theorem card_rootInverseIndex (m j : ℕ) (F : Finset PolicyDescriptor) :
    Fintype.card (RootInverseIndex m j F) =
      MaskJetExpansion.inverseMultiplicity (m+2) j*(1+2*F.card*(m+3))^(2*j) := by
  rw [MaskJetExpansion.card_inverse_product,Fintype.card_sum]
  simp only [Fintype.card_coe]
  congr 3
  ring

theorem rootInverseWeight_nonneg (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    (a : RootInverseIndex m j F) : 0 ≤ rootInverseWeight m j F N σ a := by
  apply Finset.prod_nonneg
  intro b _
  apply pow_nonneg
  apply inv_nonneg.mpr
  cases b with
  | inl b => exact (descriptorMaskRadius_pos N σ b).le
  | inr b => exact (descriptorMaskRadius_pos N σ b).le

theorem rootInverseWeight_le (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    {E : ℝ} (hE : 1 ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : RootInverseIndex m j F) : rootInverseWeight m j F N σ a ≤ E^(2*j) := by
  have hr (b) : 0 ≤ (rootInverseRadii F N σ b)⁻¹ := by
    cases b with
    | inl b => exact inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le
    | inr b => exact inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le
  have hbound (b) : (rootInverseRadii F N σ b)⁻¹ ≤ E := by
    cases b with
    | inl b => exact hF b b.property
    | inr b => exact hF b b.property
  calc
    _ ≤ ∏ b : {b // b ∈ F} ⊕ {b // b ∈ F}, E^((rootInverseTerm m j F a).jet b).order :=
      Finset.prod_le_prod (fun b _ => pow_nonneg (hr b) _)
        (fun b _ => pow_le_pow_left₀ (hr b) (hbound b) _)
    _ = E^(∑ b, ((rootInverseTerm m j F a).jet b).order) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ E^(2*j) := pow_le_pow_right₀ hE (rootInverseTerm_order m j F a)

theorem rotated_root_normalized_coefficient_le (m j : ℕ) (F : Finset PolicyDescriptor)
    (N : ℕ) (σ U A : ℝ) {E Λ V h : ℝ} (hE : 1 ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hΛ : 0 < Λ) (hV : 0 < V) (hh : 0 ≤ h)
    (hEΛ : E^2 ≤ Λ) (hΛV : Λ ≤ 4*V) (a : RootInverseIndex m j F) :
    ‖((Λ^h*(Λ^j)⁻¹/(V^h) : ℝ) : ℂ)*
      (rootInverseWeight m j F N σ a*(U*A)*U : ℝ)‖ ≤ (|U*A| * |U|)*4^h := by
  have hγ : 0 ≤ Λ^h*(Λ^j)⁻¹/(V^h) := by positivity
  have hr := normalized_stationary_coefficient_le
    (p := 2*j) (q := 0) (j := j) (by omega) hΛ hE hV hh hEΛ hΛV
  simp only [add_zero] at hr
  have hr' : Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h) ≤ (4:ℝ)^h := (le_abs_self _).trans hr
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hγ,abs_mul,abs_mul,abs_of_nonneg (rootInverseWeight_nonneg m j F N σ a)]
  calc
    _ ≤ (Λ^h*(Λ^j)⁻¹/(V^h))*(E^(2*j)*|U*A| * |U|) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (rootInverseWeight_le m j F N σ hE hF a) (abs_nonneg _))
          (abs_nonneg _)) hγ
    _ = (|U*A| * |U|)*(Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialSharedRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundedness and shell integrability of the shared spatial amplitude -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem spatialSharedAmplitude_norm_le
    (c : Space d → ℂ) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ)
    {B C : ℝ} (hB : 0 ≤ B)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C) (r : ℝ) :
    ‖spatialSharedAmplitude c U V r‖ ≤
      ((∫ ξ : Space d, ‖c ξ‖)*(B*C))*(sphereMeasure d).real univ := by
  apply norm_integral_le_of_norm_le_const
  apply Filter.Eventually.of_forall
  intro w
  calc
    _ ≤ ∫ ξ : Space d, ‖c ξ‖*(B*C) := by
      apply norm_integral_le_of_norm_le (hc.norm.mul_const (B*C))
      apply Filter.Eventually.of_forall
      intro ξ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hbU (ξ,(r,w))) (hbV (ξ,(r,w))) (norm_nonneg _) hB)
        (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem spatialSharedAmplitude_sq_integrable
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ)
    (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun r => ‖spatialSharedAmplitude c U V r‖^2) μ := by
  let K := ((∫ ξ : Space d, ‖c ξ‖)*(B*C))*(sphereMeasure d).real univ
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (mul_nonneg hB hC))
    measureReal_nonneg
  apply (integrable_const (K^2)).mono'
    ((spatialSharedAmplitude_measurable c hcm U V hU hV).norm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mpr
    (spatialSharedAmplitude_norm_le c hc U V hB hbU hbV r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FiniteShellSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite summation of the stationary shell terms

The finite inverse order and separated factor count contribute only their
explicit finite cardinality. No supremum or interchange with a variable
measure is hidden in this step.
-/

namespace Falconer
open Set MeasureTheory

private theorem norm_sum_sq_le_card {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖^2 ≤ (S.card:ℝ)*∑ i ∈ S, ‖f i‖^2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) 2).trans
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
    using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖f i‖)

theorem finite_shell_sum_sq_integrable {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (c F : ι → α → ℂ) (C : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hF : ∀ i ∈ S, Measurable (F i))
    (hFi : ∀ i ∈ S, Integrable (fun r => ‖F i r‖^2) μ)
    (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbound : ∀ᵐ r ∂μ, ∀ i ∈ S, ‖c i r‖ ≤ C i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) μ := by
  have hr : Integrable (fun r => (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2) μ :=
    (integrable_finsetSum S (fun i hi => (hFi i hi).const_mul ((C i)^2))).const_mul _
  have hm : Measurable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) :=
    (Finset.measurable_sum S (fun i hi => (hc i hi).mul (hF i hi))).norm.pow_const 2
  apply hr.mono' hm.aestronglyMeasurable
  filter_upwards [hbound] with r h
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (norm_sum_sq_le_card S (fun i => c i r*F i r)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (hC i hi)).mpr (h i hi)) (sq_nonneg _)

theorem finite_shell_sum_le {ι : Type*} (S : Finset ι) (v : ℝ) (Ψ : ℝ → ℝ)
    (c F : ι → ℝ → ℂ) (C E : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hF : ∀ i ∈ S, Measurable (F i))
    (hFi : ∀ i ∈ S, Integrable (fun r => ‖F i r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ C i)
    {P : ℝ} (hP : 0 ≤ P)
    (hE : ∀ i ∈ S, P*(∫ r, ‖F i r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ E i) :
    P*(∫ r, ‖∑ i ∈ S, c i r*F i r‖^2
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (S.card:ℝ)*∑ i ∈ S, (C i)^2*E i := by
  let μ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  have hr : Integrable (fun r => (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2) μ :=
    (integrable_finsetSum S (fun i hi => (hFi i hi).const_mul ((C i)^2))).const_mul _
  have hm : Measurable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) :=
    (Finset.measurable_sum S (fun i hi => (hc i hi).mul (hF i hi))).norm.pow_const 2
  have hb : ∀ᵐ r ∂μ, ‖∑ i ∈ S, c i r*F i r‖^2 ≤
      (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2 := by
    filter_upwards [hbound] with r hr
    apply (norm_sum_sq_le_card S (fun i => c i r*F i r)).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (hC i hi)).mpr (hr i hi)) (sq_nonneg _)
  have hi : Integrable (fun r => ‖∑ i ∈ S, c i r*F i r‖^2) μ := by
    apply hr.mono' hm.aestronglyMeasurable
    filter_upwards [hb] with r h
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ P*(∫ r, (S.card:ℝ)*∑ i ∈ S, (C i)^2*‖F i r‖^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hi hr hb) hP
    _ = (S.card:ℝ)*∑ i ∈ S,
        (C i)^2*(P*(∫ r, ‖F i r‖^2 ∂μ)) := by
      rw [integral_const_mul,integral_finsetSum S (fun i hi => (hFi i hi).const_mul _)]
      simp only [integral_const_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hE i hi) (sq_nonneg _)))
      (Nat.cast_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FiniteSpatialShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite separated inverse terms in the independent angular shell

The spatial coefficient is the actual inverse-distance Fourier coefficient.
All radial and spatial integrability is derived from the bounded endpoint
families. The only energy hypotheses concern the two independent angles.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem finite_spatial_shell_sum_integrable {ι : Type*} (S : Finset ι)
    (_a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i) :
    Integrable (fun r => ‖∑ i ∈ S, c i r *
      spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  apply finite_shell_sum_sq_integrable (PlanarFalconer.sourceAngularShellMeasure v Ψ) S c
    (fun i => spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i)) A hc
  · intro i hi
    exact spatialSharedAmplitude_measurable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (U i) (V i) (hU i hi) (hV i hi)
  · intro i hi
    exact spatialSharedAmplitude_sq_integrable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (spatialFourierCoeff_integrable δ L hδ hL (j i))
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) _
  · exact hA
  · exact hbound

theorem finite_spatial_shell_le {ι : Type*} (S : Finset ι)
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A H : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i)
    (hH : ∀ i ∈ S, ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U i (ξ,p)) (fun p => V i (ξ,p)) ≤ H i) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖∑ i ∈ S, c i r *
        spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (S.card:ℝ)*∑ i ∈ S, (A i)^2*
        ((spatialFourierCost (d := d) δ L hδ hL (j i))^2*H i) := by
  apply finite_shell_sum_le S v Ψ c
    (fun i => spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i))
    A (fun i => (spatialFourierCost (d := d) δ L hδ hL (j i))^2*H i) hc
  · intro i hi
    exact spatialSharedAmplitude_measurable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (U i) (V i) (hU i hi) (hV i hi)
  · intro i hi
    exact spatialSharedAmplitude_sq_integrable _
      (spatialFourierCoeff (d := d) δ L hδ hL (j i)).continuous.measurable
      (spatialFourierCoeff_integrable δ L hδ hL (j i))
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) _
  · exact hA
  · exact hbound
  · positivity
  · intro i hi
    exact spatial_fourier_shared_shell_le a v Ψ δ L hδ hL (j i)
      (U i) (V i) (hU i hi) (hV i hi) (hB i hi) (hC i hi)
      (hbU i hi) (hbV i hi) (H i) (hH i hi)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateSpatialShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial Fourier terms controlled by the exact recursive state

Spatial phases and conjugation preserve the actual descriptor symbol
class. Consequently each separated inverse factor is controlled by its
own next-state supremum, without enlarging the class of angular symbols.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

theorem spatialFourier_value (f : DescriptorJetSymbol n K L F D)
    (s : ℝ) (ξ : Space (n+2))
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (f.spatialFourier s ξ).value Q ρ profile N σ J i S A x w =
      spatialFourierPhase s ξ x*f.value Q ρ profile N σ J i S A x w :=
  f.spatialMultiplier_value _ _ _ Q ρ profile N σ J i S A x w

end DescriptorJetSymbol

theorem spatial_endpoint_energy_le_jetStateEnvelope
    {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (s a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D)
    (ξ : Space (n+2)) :
    independentAngularEnergy a v Ψ
      (fun p => spatialEndpointFamily μ M s (f.value Q ρ profile N σ J i S A) (ξ,p))
      (fun p => spatialEndpointFamily ν P s
        (fun x w => star (g.value Q ρ profile N σ J i S A x w)) (ξ,p)) ≤
      jetStateEnvelope n K L D F G Q ρ profile N σ J i S A μ ν M P a v Ψ := by
  have h := jetStateEnergy_le_envelope Q ρ profile N σ J i S hF hG hA μ ν hM hP
    a v Ψ (f.spatialFourier s ξ) (g.conj.spatialFourier s ξ)
  have hf : (f.spatialFourier s ξ).value Q ρ profile N σ J i S A =
      fun x w => spatialFourierPhase s ξ x*f.value Q ρ profile N σ J i S A x w := by
    funext x w
    exact f.spatialFourier_value s ξ Q ρ profile N σ J i S A x w
  have hg : (g.conj.spatialFourier s ξ).value Q ρ profile N σ J i S A =
      fun x w => spatialFourierPhase s ξ x*star (g.value Q ρ profile N σ J i S A x w) := by
    funext x w
    rw [DescriptorJetSymbol.spatialFourier_value,DescriptorJetSymbol.conj_value]
  simpa only [jetStateEnergy,hf,hg,spatialEndpointFamily] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateBudgetOrder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding actual states in the fixed recursive derivative budget -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem jetStateValues_budget_subset {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ⊆
      jetStateValues n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f.relax hK hL hD hDD',g.relax hK hL hD hDD',rfl⟩

theorem jetStateEnvelope_budget_mono {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ≤
      jetStateEnvelope n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  apply csSup_le (show (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  exact le_csSup (jetStateValues_bddAbove (K := K') (L := L') (D := D') Q ρ m N σ J i S
    hF hG hA μ ν hM hP a v Ψ)
    (jetStateValues_budget_subset hK hL hD hDD' Q ρ m N σ J i S A μ ν M P a v Ψ hh)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedWeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cell-scaled inverse in a fixed orthogonal angular frame

Only the angular variable changes. All spatial displacements, distance powers,
frequencies and endpoint laws in the separated formula are the original ones.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

theorem rotatedScaledWeightedInverseSum_eq_terms (m J : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) :
    rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2) =
      ∑ j ∈ Finset.range (J+1),
        (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
          rotatedScaledInverseTerm m j T s r B z := by
  unfold rotatedScaledWeightedInverseSum scaledWeightedInverseSum rotatedScaledInverseTerm
  apply Finset.sum_congr rfl
  intro j _
  rw [← sphere_integral_rotation T]
  simp only [T.norm_map,dist_eq_norm,Complex.ofReal_mul,mul_assoc]
  congr 3
  apply integral_congr_ae
  filter_upwards with w
  simp only [sphereMap,T.inner_map_map,rotatedInverseAmplitude]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_RotatedInverseIntegration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration of the rotated finite inverse on the original pair laws -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

private theorem bounded_sphere_phase_integrable_p2 {d : ℕ}
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

namespace RotatedRootSymbols
variable {m j L : ℕ} {F : Finset PolicyDescriptor}
  {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} {A : ℝ}

theorem integration (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            rotatedInverseAmplitude m T
              (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w
          ∂sphereMeasure (m+3) ∂μ.prod ν =
      ∑ a : RootInverseIndex m j F, ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ) *
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
          (spatialEndpointFamily μ M s ((H.left a).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star ((H.right a).value Q ρ profile N σ J i S U x w))) r := by
  let b := fun a : RootInverseIndex m j F => (H.left a).value Q ρ profile N σ J i S U
  let c := fun a : RootInverseIndex m j F => (H.right a).value Q ρ profile N σ J i S U
  let α := fun a : RootInverseIndex m j F => ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ)
  let Z := fun (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₁ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  let C₂ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  have hC₁ : 0 ≤ C₁ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : RootInverseIndex m j F) : Measurable (Function.uncurry (b a)) :=
    (H.left a).value_measurable Q ρ profile N σ J i S U
  have hc (a : RootInverseIndex m j F) : Measurable (Function.uncurry (c a)) :=
    (H.right a).value_measurable Q ρ profile N σ J i S U
  have hbB (a : RootInverseIndex m j F) (x) (w) : ‖b a x w‖ ≤ C₁ :=
    (H.left a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hcC (a : RootInverseIndex m j F) (x) (w) : ‖c a x w‖ ≤ C₂ :=
    (H.right a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hi (a : RootInverseIndex m j F) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₁ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable_p2 (b a) (c a) (hb a) (hc a) hC₁ (hbB a) (hcC a) r z
  have he (z : Space (m+3) × Space (m+3)) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            rotatedInverseAmplitude m T
              (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w
          ∂sphereMeasure (m+3)) = ∑ a : RootInverseIndex m j F, α a*Z a z := by
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          rotatedInverseAmplitude m T
            (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w) =
        fun w : Sphere (m+3) => ∑ a : RootInverseIndex m j F, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [H.expansion hA Q ρ profile N σ J i S hU]
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
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun a _ => (hi a).const_mul (α a)),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  have hsep' := spatial_inverse_sphere_separation δ W hδ hW j hs μ ν hsep M P
    (b a) (fun x w => star (c a x w)) (hb a) (continuous_star.measurable.comp (hc a))
    hC₁ (hbB a) (fun x w => (norm_star _).le.trans (hcC a x w)) r
  simp only [star_star] at hsep'
  calc
    _ = α a*((M⁻¹*P⁻¹) • ∫ z, Z a z ∂μ.prod ν) := by
      simp only [Complex.real_smul]; ring
    _ = _ := by rw [hsep']; rfl

theorem original_term_integrable (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (rotatedScaledInverseTerm m j T s r
      (descriptorPairAmplitude Q ρ profile N σ J i F S)) (μ.prod ν) := by
  let b := fun a : RootInverseIndex m j F => (H.left a).value Q ρ profile N σ J i S U
  let c := fun a : RootInverseIndex m j F => (H.right a).value Q ρ profile N σ J i S U
  let α := fun a : RootInverseIndex m j F => ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ)
  let Z := fun (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₀ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : RootInverseIndex m j F) : Measurable (Function.uncurry (b a)) :=
    (H.left a).value_measurable Q ρ profile N σ J i S U
  have hc (a : RootInverseIndex m j F) : Measurable (Function.uncurry (c a)) :=
    (H.right a).value_measurable Q ρ profile N σ J i S U
  have hbB (a : RootInverseIndex m j F) (x) (w) : ‖b a x w‖ ≤ C₀ :=
    (H.left a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hcC (a : RootInverseIndex m j F) (x) (w) : ‖c a x w‖ ≤ C₀ :=
    (H.right a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hi (a : RootInverseIndex m j F) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      hsep (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₀ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable_p2 (b a) (c a) (hb a) (hc a) hC₀ (hbB a) (hcC a) r z
  have he : rotatedScaledInverseTerm m j T s r
      (descriptorPairAmplitude Q ρ profile N σ J i F S) =
      fun z => ∑ a : RootInverseIndex m j F, α a*Z a z := by
    funext z
    unfold rotatedScaledInverseTerm
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          rotatedInverseAmplitude m T
            (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w) =
        fun w : Sphere (m+3) => ∑ a : RootInverseIndex m j F, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [H.expansion hA Q ρ profile N σ J i S hU]
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

end RotatedRootSymbols

theorem rotated_inverse_jet_integrable {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (fun z : Space (m+3) × Space (m+3) =>
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2)) (μ.prod ν) := by
  let V := descriptorPairAmplitude Q ρ profile N σ J i F S
  have hi (j : Fin (k+1)) : Integrable (rotatedScaledInverseTerm m j.val T s r V) (μ.prod ν) :=
    (H j).original_term_integrable (hA j) Q ρ profile N σ J i S hF hU δ hδ s μ ν hsep r
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1),
      (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
        rotatedScaledInverseTerm m j T s r V z) (μ.prod ν) := by
    apply integrable_finsetSum
    intro j hj
    exact (hi ⟨j,Finset.mem_range.mp hj⟩).const_mul _
  apply hs.congr
  filter_upwards with z
  exact (rotatedScaledWeightedInverseSum_eq_terms m k T s r V z).symm

theorem rotated_inverse_jet_integration {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (M P r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν) =
      ∑ j : Fin (k+1), (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j.val)⁻¹ : ℝ) : ℂ)*
        ((M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
          rotatedScaledInverseTerm m j.val T s r
            (descriptorPairAmplitude Q ρ profile N σ J i F S) z ∂μ.prod ν) := by
  let V := descriptorPairAmplitude Q ρ profile N σ J i F S
  have hi (j : Fin (k+1)) : Integrable (rotatedScaledInverseTerm m j.val T s r V) (μ.prod ν) :=
    (H j).original_term_integrable (hA j) Q ρ profile N σ J i S hF hU δ hδ s μ ν hsep r
  change (M⁻¹*P⁻¹) • (∫ z, rotatedScaledWeightedInverseSum m k T s r (z.1-z.2) (V z.1 z.2) ∂μ.prod ν) = _
  simp_rw [rotatedScaledWeightedInverseSum_eq_terms,← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul _),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,← mul_smul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RotatedInverseShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full rotated inverse bounded by the original descriptor state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)


theorem rotated_inverse_family_shell_integrable {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    Integrable (fun r => ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
      U δ W hδ hW s μ ν M P a v r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  unfold rotatedInverseNormalizedSum
  let C₀ (z : RootInverseFamilyIndex m k F) :=
    (descriptorJetBound (m+3) (2*z.1.val))^(2*z.1.val)*U⁻¹
  have hC₀ (z : RootInverseFamilyIndex m k F) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_sum_integrable (ι := RootInverseFamilyIndex m k F) Finset.univ a v Ψ δ W hδ hW (fun (z : RootInverseFamilyIndex m k F) => z.1.val)
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily ν P s
      (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable μ M s _
      (((H z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((H z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : RootInverseFamilyIndex m k F) => C₀ z*μ.real univ/M) (fun (z : RootInverseFamilyIndex m k F) => C₀ z*ν.real univ/P)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le μ hM s _
      (((H z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((H z.1).right z.2).value_norm_le Q ρ profile N σ J i S hF hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ))
    (fun z => (|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))
  · intro z _
    fun_prop
  · intro z _
    positivity
  · filter_upwards [hregime] with r hr
    intro z _
    have hp : ((2:ℝ)^(v-a))^(((m+2:ℕ):ℝ)/2) =
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    rw [← hp]
    exact rotated_root_normalized_coefficient_le m z.1.val F N σ U (A z.1) hE hFE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2


theorem rotated_inverse_family_shell_le {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (RootInverseFamilyIndex m k F) : ℝ)*
        ∑ z : RootInverseFamilyIndex m k F,
          ((|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))^2*
            ((spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2*
              jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ) := by
  unfold rotatedInverseNormalizedSum
  let C₀ (z : RootInverseFamilyIndex m k F) :=
    (descriptorJetBound (m+3) (2*z.1.val))^(2*z.1.val)*U⁻¹
  have hC₀ (z : RootInverseFamilyIndex m k F) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_le (ι := RootInverseFamilyIndex m k F) Finset.univ a v Ψ δ W hδ hW (fun (z : RootInverseFamilyIndex m k F) => z.1.val)
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily ν P s
      (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable μ M s _
      (((H z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((H z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : RootInverseFamilyIndex m k F) => C₀ z*μ.real univ/M) (fun (z : RootInverseFamilyIndex m k F) => C₀ z*ν.real univ/P)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le μ hM s _
      (((H z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((H z.1).right z.2).value_norm_le Q ρ profile N σ J i S hF hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ))
    (fun z => (|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))
    (fun _ => jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ)
  · intro z _
    fun_prop
  · intro z _
    positivity
  · filter_upwards [hregime] with r hr
    intro z _
    have hp : ((2:ℝ)^(v-a))^(((m+2:ℕ):ℝ)/2) =
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    rw [← hp]
    exact rotated_root_normalized_coefficient_le m z.1.val F N σ U (A z.1) hE hFE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2
  · intro z _ ξ
    have hK : 2*z.1.val ≤ 2*k := by have := z.1.isLt; omega
    exact (spatial_endpoint_energy_le_jetStateEnvelope Q ρ profile N σ J i S hF hF hU
      μ ν hM hP s a v Ψ ((H z.1).left z.2) ((H z.1).right z.2) ξ).trans
      (jetStateEnvelope_budget_mono hK le_rfl (by norm_num) le_rfl Q ρ profile N σ J i S
        hF hF hU μ ν hM hP a v Ψ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial cost of the actual root inverse family -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_rotated_root_shell_cost (m k : ℕ) (A : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset PolicyDescriptor),
      rotatedInverseShellCost m k F A U δ W hδ hW ≤
        C*((1+2*F.card*(m+3):ℕ):ℝ)^(4*k) := by
  let c : Fin (k+1) → ℝ := fun j => MaskJetExpansion.inverseMultiplicity (m+2) j.val
  let b : Fin (k+1) → ℝ := fun j =>
    ((|U*A j| *|U|)*4^(((m+2:ℕ):ℝ)/2))^2*
      (spatialFourierCost (d := m+3) δ W hδ hW j.val)^2
  let C₁ : ℝ := ∑ j, c j
  let C₂ : ℝ := ∑ j, b j
  have hc (j) : 0 ≤ c j := Nat.cast_nonneg _
  have hb (j) : 0 ≤ b j := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg (fun j _ => hc j)
  have hC₂ : 0 ≤ C₂ := Finset.sum_nonneg (fun j _ => hb j)
  refine ⟨C₁^2*C₂,mul_nonneg (sq_nonneg _) hC₂,?_⟩
  intro F
  let I := RootInverseFamilyIndex m k F
  let Q : ℝ := ((1+2*F.card*(m+3):ℕ):ℝ)
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast Nat.le_add_right 1 _
  have hcard : (Fintype.card I : ℝ) ≤ C₁*Q^(2*k) := by
    have he : (Fintype.card I : ℝ) = ∑ j : Fin (k+1), c j*Q^(2*j.val) := by
      simp only [I,RootInverseFamilyIndex,Fintype.card_sigma,card_rootInverseIndex,
        Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,c,Q]
    rw [he]
    dsimp only [C₁]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hc j)
    exact pow_le_pow_right₀ hQ (by have := j.isLt; omega)
  have hsum : (∑ z : I, b z.1) ≤ (Fintype.card I:ℝ)*C₂ := by
    calc
      _ ≤ ∑ _z : I, C₂ := Finset.sum_le_sum (fun z _ =>
        Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ z.1))
      _ = _ := by simp
  have hcost : rotatedInverseShellCost m k F A U δ W hδ hW ≤
      (Fintype.card I:ℝ)^2*C₂ := by
    change (Fintype.card I:ℝ)*(∑ z : I, b z.1) ≤ _
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)).trans_eq (by ring)
  apply hcost.trans
  calc
    _ ≤ (C₁*Q^(2*k))^2*C₂ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hC₂
    _ = (C₁^2*C₂)*Q^(4*k) := by
      rw [mul_pow,← pow_mul]
      have he : 2*k*2 = 4*k := by omega
      rw [he]
      ring

theorem eventual_rotated_root_shell_cost (m k : ℕ) (A : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (F : Finset PolicyDescriptor),
      F.card ≤ (N+1)^3 →
      rotatedInverseShellCost m k F A U δ W hδ hW ≤ ((2:ℝ)^N)^ε := by
  obtain ⟨C,hC,hbound⟩ := exists_rotated_root_shell_cost m k A U δ W hδ hW
  let H : ℝ := 1+4*(m+3:ℕ)
  obtain ⟨N₁,hN₁⟩ := PlanarFalconer.fixed_polynomial_subpower (12*k) (half_pos hε)
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed (half_pos hε) (C*H^(4*k))
  refine ⟨max N₁ N₂,?_⟩
  intro N hN F hF
  have hx : (1:ℝ) ≤ (N:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hX : (1:ℝ) ≤ ((N:ℝ)+1)^3 := one_le_pow₀ hx
  have hFc : (F.card:ℝ) ≤ ((N:ℝ)+1)^3 := by exact_mod_cast hF
  have hM : (0:ℝ) ≤ (m+3:ℕ) := Nat.cast_nonneg _
  have hQ : ((1+2*F.card*(m+3):ℕ):ℝ) ≤ H*((N:ℝ)+1)^3 := by
    dsimp [H]
    push_cast at hM ⊢
    calc
      _ ≤ 1+2*((N:ℝ)+1)^3*((m:ℝ)+3) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hX)]
  have hp : ((1+2*F.card*(m+3):ℕ):ℝ)^(4*k) ≤
      H^(4*k)*((N:ℝ)+1)^(12*k) := by
    calc
      _ ≤ (H*((N:ℝ)+1)^3)^(4*k) := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
      _ = _ := by rw [mul_pow,← pow_mul]; congr 2; omega
  calc
    _ ≤ C*((1+2*F.card*(m+3):ℕ):ℝ)^(4*k) := hbound F
    _ ≤ (C*H^(4*k))*((N:ℝ)+1)^(12*k) := by
      convert mul_le_mul_of_nonneg_left hp hC using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ (C*H^(4*k))*(4*(N:ℝ)+1)^(12*k) := by
      gcongr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ ((2:ℝ)^N)^(ε/2)*((2:ℝ)^N)^(ε/2) :=
      mul_le_mul (hN₂ N ((le_max_right _ _).trans hN))
        (hN₁ N ((le_max_left _ _).trans hN)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarErrorBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the scalar shell's fixed cost and squared remainder

The shell width costs at most one power of R. Selecting the stationary
accuracy before scale therefore absorbs the square and the fixed constants.
-/

namespace Falconer

theorem eventual_scalar_shell_error_budget (T : ℝ) {C W : ℝ}
    (_hC : 0 ≤ C) (hW : 0 ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q ε : ℝ, q ≤ N → 0 ≤ ε →
      ε ≤ C*((2:ℝ)^N)^(-((T+2)/2)) →
      2*(2:ℝ)^q*ε^2*W ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by norm_num : (0:ℝ) < 1) (2*C^2*W)
  refine ⟨N₀,?_⟩
  intro N hN q ε hq hε hbound
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hqR : (2:ℝ)^q ≤ R := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq
  have hconst : 2*C^2*W ≤ R := by simpa only [Real.rpow_one] using hN₀ N hN
  have he : ε^2 ≤ C^2*R^(-(T+2)) := by
    have hpow := pow_le_pow_left₀ hε hbound 2
    convert hpow using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_pow,← Real.rpow_mul_natCast hR.le]
    congr 2
    ring
  calc
    _ ≤ 2*R*(C^2*R^(-(T+2)))*W := by gcongr
    _ = (2*C^2*W)*R*R^(-(T+2)) := by ring
    _ ≤ R*R*R^(-(T+2)) := by gcongr
    _ = R^(-T) := by
      rw [← sq,← Real.rpow_two,← Real.rpow_add hR]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedDescriptorFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One normalized descriptor inverse family for every large scale

The operator, its finite index set, and all constants are chosen before the
scale label. Every original descriptor remains in the support condition.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem equal_scale_product_derivatives {d K : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (B C : Space d → ℂ) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hb : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k B x‖ ≤ D^k)
    (hc : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k C x‖ ≤ D^k) :
    ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k (fun z => B z*C z) x‖ ≤ (2 : ℝ)^K*D^k := by
  classical
  let f : Fin 2 → Space d → ℂ := fun i => if i = 0 then B else C
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ContDiff ℝ ∞ (f i) := by
    intro i _
    fin_cases i
    · simpa [f] using hB
    · simpa [f] using hC
  intro k hk x
  have hfb : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ l ≤ K,
      ‖iteratedFDeriv ℝ l (f i) x‖ ≤ D^l := by
    intro i _ l hl
    fin_cases i
    · simpa [f] using hb l hl x
    · simpa [f] using hc l hl x
  have h := ambient_mask_product_derivatives Finset.univ f hD K x hf hfb k hk
  have hprod : (fun z => ∏ i : Fin 2, f i z) = fun z => B z*C z := by
    funext z
    simp [Fin.prod_univ_two,f]
  rw [hprod] at h
  have htwo : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  rw [htwo,mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (pow_nonneg hD _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorPairDerivativeScale
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform derivatives of the actual two-endpoint amplitude

The finite-order product loss is fixed before scale, classes, lists and
points. This supplies the derivative premise of the masked inverse remainder.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_descriptor_pair_derivatives (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q : DyadicCube d) (ρ : Measure (Space d)) (f : ℝ → ℝ) (J i L : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      B.card ≤ (N+1)^P →
      (∀ b ∈ B, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x y k, k ≤ K → ∀ w : Space d,
        ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ f N σ J i B S x y) w‖ ≤
          (2:ℝ)^K*(descriptorDerivativeScale N σ L)^k := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_global_scale d K P hσ
  refine ⟨N₀,?_⟩
  intro N hN Q ρ f J i L B S hB hL hsep x y k hk w
  have hs (z : Space d) : ContDiff ℝ ∞ (fun v =>
      (descriptorAmbientProduct Q ρ f N σ J i B S z v : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S z)
  have hb (z : Space d) : ∀ l ≤ K, ∀ v,
      ‖iteratedFDeriv ℝ l (fun u => (descriptorAmbientProduct Q ρ f N σ J i B S z u : ℂ)) v‖ ≤
        (descriptorDerivativeScale N σ L)^l := by
    intro l hl v
    exact hN₀ N hN Q ρ f J i L B S hB hL hsep z v l hl
  exact equal_scale_product_derivatives
    (zero_le_one.trans (descriptorDerivativeScale_ge_one N hσ.le L))
    _ _ (hs x) (hs y) (hb x) (hb y) k hk w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_LocalizedScalarShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar shell comparison from the actual localized square integral

No global bound on the oscillatory expression is used. The positive cutoff
dominates the target shell, so integrability under its density gives target
shell integrability and the same exact dimensional normalization.
-/

namespace Falconer
open Set MeasureTheory

private theorem source_shell_weighted_integrable (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (g : ℝ → ℝ) (hg : Integrable g (PlanarFalconer.sourceAngularShellMeasure v Ψ)) :
    Integrable (fun r => Ψ (r/(2:ℝ)^v)*g r) := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hd : Measurable (fun r : ℝ => ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)) := by
    fun_prop
  have hi := (integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  have he (r : ℝ) : (ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)).toReal =
      Ψ (r/(2:ℝ)^v)/(2:ℝ)^v := ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)
  simp only [he,smul_eq_mul] at hi
  have hm := hi.const_mul ((2:ℝ)^v)
  have hm' : IntegrableOn (fun r => Ψ (r/(2:ℝ)^v)*g r) (Ioi (0:ℝ)) := by
    have heq : (fun r => (2:ℝ)^v*((Ψ (r/(2:ℝ)^v)/(2:ℝ)^v)*g r)) =
        fun r => Ψ (r/(2:ℝ)^v)*g r := by
      funext r
      field_simp [hR.ne']
    rw [heq] at hm
    exact hm
  apply (hm'.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact indicator_of_mem hr _
  · rw [indicator_of_notMem hr]
    have hz := hzero (r/(2:ℝ)^v)
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp only [hz,zero_mul]

theorem localized_dyadic_shell_domination (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ)) :
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        (2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hwi := source_shell_weighted_integrable v Ψ hΨ hpos hzero
    (fun r => ‖F r‖^2) hi
  let T := Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))
  have hb (r : ℝ) : T.indicator (fun r => ‖F r‖^2) r ≤
      Ψ (r/(2:ℝ)^v)*‖F r‖^2 := by
    by_cases hr : r ∈ T
    · rw [indicator_of_mem hr]
      have he₁ : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by
        rw [Real.rpow_sub (by norm_num)]; norm_num
      have he₂ : (2:ℝ)^(v+1) = 2*(2:ℝ)^v := by
        rw [Real.rpow_add (by norm_num)]; norm_num; ring
      have hh : r/(2:ℝ)^v ∈ Icc (1/2:ℝ) 2 := by
        constructor
        · apply (le_div_iff₀ hR).mpr
          change (2:ℝ)^(v-1) ≤ r ∧ r ≤ (2:ℝ)^(v+1) at hr
          rw [he₁] at hr
          linarith [hr.1]
        · apply (div_le_iff₀ hR).mpr
          exact hr.2.trans_eq he₂
      exact le_mul_of_one_le_left (sq_nonneg _) (hone _ hh)
    · rw [indicator_of_notMem hr]
      exact mul_nonneg (hpos _) (sq_nonneg _)
  have hfi : Integrable (T.indicator (fun r => ‖F r‖^2)) := by
    apply hwi.mono' ((hF.norm.pow_const 2).indicator measurableSet_Icc).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) r)]
    exact hb r
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mp hfi,?_⟩
  rw [PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero,
    smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,
    ← integral_indicator measurableSet_Icc]
  exact integral_mono hfi hwi hb

theorem localized_scalar_shell_from_angular_energy (d : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x) (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    {H : ℝ} (hH : (2:ℝ)^((d:ℝ)*(v-a))*
      (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ H) :
    IntegrableOn (fun r => ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2)
      (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2) ≤ H := by
  have hdom := localized_dyadic_shell_domination v Ψ hΨ hpos hzero hone F hF hi
  have hp : 0 ≤ (2:ℝ)^((v-a)*((d:ℝ)-1)/2) := by positivity
  have he : (fun r => ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2) =
      fun r => ((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*‖F r‖^2 := by
    funext r
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,mul_pow]
  rw [he]
  refine ⟨hdom.1.const_mul _,?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
        ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdom.2 (sq_nonneg _)) (by positivity)
    _ = (2:ℝ)^((d:ℝ)*(v-a))*
        (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
      rw [show (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
          ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) =
          ((2:ℝ)^(-a)*(2:ℝ)^v*((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2)*
            (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) by ring,
        scalar_angular_shell_normalization]
    _ ≤ H := hH

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ScalarShellError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a bounded stationary error through a finite scalar shell

The comparison uses the original scalar functions and a pointwise remainder
bound. Square integrability of the approximating function supplies all the
integrability needed for the final error estimate.
-/

namespace Falconer
open Set MeasureTheory

theorem norm_sq_le_of_norm_sub_le {z w : ℂ} {ε : ℝ}
    (h : ‖z-w‖ ≤ ε) : ‖z‖^2 ≤ 2*‖w‖^2+2*ε^2 := by
  have hzw : ‖z‖ ≤ ‖w‖+ε := by
    calc
      ‖z‖ = ‖(z-w)+w‖ := by congr 1; ring
      _ ≤ ‖z-w‖+‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖+ε := by linarith
  have hs := pow_le_pow_left₀ (norm_nonneg z) hzw 2
  nlinarith [sq_nonneg (‖w‖-ε)]

theorem scalar_shell_error_transfer {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F G : α → ℂ)
    (hF : Measurable F) (hG : Integrable (fun x => ‖G x‖^2) μ)
    {ε P H : ℝ} (hP : 0 ≤ P)
    (herr : ∀ᵐ x ∂μ, ‖F x-G x‖ ≤ ε)
    (hH : P*(∫ x, ‖G x‖^2 ∂μ) ≤ H) :
    Integrable (fun x => ‖F x‖^2) μ ∧
      P*(∫ x, ‖F x‖^2 ∂μ) ≤ 2*H+2*P*ε^2*μ.real univ := by
  have hb : ∀ᵐ x ∂μ, ‖F x‖^2 ≤ 2*‖G x‖^2+2*ε^2 :=
    herr.mono fun x hx => norm_sq_le_of_norm_sub_le hx
  have hupper : Integrable (fun x => 2*‖G x‖^2+2*ε^2) μ :=
    (hG.const_mul 2).add (integrable_const _)
  have hFi : Integrable (fun x => ‖F x‖^2) μ := by
    apply hupper.mono' (hF.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with x hx
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  refine ⟨hFi,?_⟩
  calc
    _ ≤ P*(∫ x, 2*‖G x‖^2+2*ε^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hFi hupper hb) hP
    _ = 2*(P*(∫ x, ‖G x‖^2 ∂μ))+2*P*ε^2*μ.real univ := by
      rw [integral_add (hG.const_mul 2) (integrable_const _),integral_const_mul,
        integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := by linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInverseTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the stationary inverse estimate to the actual scalar transform

The angular normalization is removed exactly. A uniform pointwise error
costs only the relative shell length 2^(v-a), before its fixed negative
power is selected.
-/

namespace Falconer
open Set MeasureTheory

theorem scalar_shell_of_stationary_approximation (d : ℕ) (a v : ℝ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (F G : ℝ → ℂ) (hF : Measurable F)
    (hG : Integrable (fun r => ‖G r‖^2) (PlanarFalconer.sourceAngularShellMeasure v Ψ))
    {ε H : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r-(((2:ℝ)^((v-a)*((d:ℝ)-1)/2):ℝ):ℂ)*G r‖ ≤ ε)
    (hH : (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖G r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ H) :
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        2*H+2*(2:ℝ)^(v-a)*ε^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  let C : ℝ := (2:ℝ)^((v-a)*((d:ℝ)-1)/2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCc : (C:ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let F₀ : ℝ → ℂ := fun r => F r/(C:ℂ)
  have hF₀ : Measurable F₀ := hF.div_const _
  have herr₀ : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F₀ r-G r‖ ≤ ε/C := by
    filter_upwards [herr] with r hr
    have he : F₀ r-G r = (F r-(C:ℂ)*G r)/(C:ℂ) := by
      dsimp [F₀]
      field_simp [hCc]
    rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
    exact div_le_div_of_nonneg_right hr hC.le
  obtain ⟨hF₀i,hF₀bound⟩ := scalar_shell_error_transfer
    (PlanarFalconer.sourceAngularShellMeasure v Ψ) F₀ G hF₀ hG
    (show 0 ≤ (2:ℝ)^((d:ℝ)*(v-a)) by positivity) herr₀ hH
  obtain ⟨hFi,hbound⟩ := localized_scalar_shell_from_angular_energy d a v Ψ
    hΨ hpos hzero hone F₀ hF₀ hF₀i hF₀bound
  have hrestore (r : ℝ) : (((2:ℝ)^((v-a)*((d:ℝ)-1)/2):ℝ):ℂ)*F₀ r = F r := by
    change (C:ℂ)*(F r/(C:ℂ)) = F r
    exact mul_div_cancel₀ (F r) hCc
  simp_rw [hrestore] at hFi hbound
  refine ⟨hFi,hbound.trans_eq ?_⟩
  have htwo : (2:ℝ)^(-a)*(2:ℝ)^v = (2:ℝ)^(v-a) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hscale : (2:ℝ)^((d:ℝ)*(v-a)) = (2:ℝ)^(v-a)*C^2 := by
    rw [← scalar_angular_shell_normalization d a v,htwo]
  rw [hscale,div_pow]
  field_simp [hC.ne']

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseScalar
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar Fourier transfer for the rotated inverse on the original laws -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem rotated_inverse_normalized_sum_eq {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P a v r : ℝ) :
    ((M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν)) /
      (((2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) : ℝ) : ℂ) =
      rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r := by
  rw [rotated_inverse_jet_integration k A H hA Q ρ profile N σ J i S hF hU δ hδ s μ ν (hsep.mono fun _ hz => hz.1) M P r,Finset.sum_div]
  unfold rotatedInverseNormalizedSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rotatedScaledInverseTerm]
  rw [(H j).integration (hA j) Q ρ profile N σ J i S hF hU
      δ W hδ hW hs μ ν hsep M P r,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.ofReal_div,Complex.ofReal_mul]
  ring


theorem scalar_shell_of_rotated_inverse {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (Qhat : ℝ → ℂ) (hQhat : Measurable Qhat) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖Qhat r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
        rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
          (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν)‖ ≤ ε) :
    IntegrableOn (fun r => ‖Qhat r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖Qhat r‖^2) ≤
        2*(rotatedInverseShellCost m k F A U δ W hδ hW *
          jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hi := rotated_inverse_family_shell_integrable k A H Q ρ profile N σ J i S
    hF hU hE hFE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb := rotated_inverse_family_shell_le k A H Q ρ profile N σ J i S
    hF hU hE hFE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb' : (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      rotatedInverseShellCost m k F A U δ W hδ hW *
        jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ := by
    apply hb.trans_eq
    unfold rotatedInverseShellCost
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  apply scalar_shell_of_stationary_approximation (m+3) a v Ψ hΨ hpos hzero hone Qhat
    (rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
      U δ W hδ hW s μ ν M P a v) hQhat hi _ hb'
  filter_upwards [herr] with r hr
  rw [← rotated_inverse_normalized_sum_eq k A H hA Q ρ profile N σ J i S
    hF hU δ W hδ hW hs μ ν hsep M P a v r]
  have he : (v-a)*(((m+3:ℕ):ℝ)-1)/2 = (v-a)*(((m+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  rw [he,mul_div_cancel₀ _ (by exact_mod_cast
    (ne_of_gt (show 0 < (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) by positivity)))]
  exact hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_MaskedDistanceBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the original masked distance measure

Here `m` is the unit-interval regularized profile. Descriptor predicates
receive its depth parametrization `u ↦ m (u/N)`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem descriptorPairWeight_bounds (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (z : Space d × Space d)
    (hz : L ≤ dist z.1 z.2*(2:ℝ)^a) :
    0 ≤ descriptorPairWeight w₀ Q ρ m N σ J i a B S z ∧
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z ≤ L^(-(((d:ℝ)-1)/2)) := by
  have h₁ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.1 (normalizeToSphere w₀ (z.1-z.2))
  have h₂ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.2 (normalizeToSphere w₀ (z.1-z.2))
  have hd' : (1:ℝ) ≤ d := Nat.one_le_cast.mpr hd
  have hh : -(((d:ℝ)-1)/2) ≤ 0 := by linarith
  have hr : 0 ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2)) :=
    (Real.rpow_pos_of_pos (hL.trans_le hz) _).le
  constructor
  · exact mul_nonneg (mul_nonneg hr h₁.1) h₂.1
  · apply (mul_le_of_le_one_right (mul_nonneg hr h₁.1) h₂.2).trans
    exact (mul_le_of_le_one_right hr h₁.2).trans (Real.rpow_le_rpow_of_nonpos hL hz hh)

 theorem maskedCellDistance_finite (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i a : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      L ≤ dist z.1 z.2*(2:ℝ)^a) :
    IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) := by
  let π := (ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)
  have hbound : ∀ᵐ z ∂π,
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * descriptorPairWeight w₀ Q ρ m N σ J i a B S z) ≤
        ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * L^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (descriptorPairWeight_bounds w₀ Q ρ m N σ J i a B S hcover hd hL z hz).2 (sq_nonneg _))
  let := finite_withDensity_of_bounded π _ ENNReal.ofReal_lt_top hbound
  unfold maskedCellDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_RotatedMaskedJetShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked distance shell in the recursive jet class

The inverse family is constructed from the zero-jet root, with constants
chosen before the masks, scale, and endpoint measures. The only analytic
inputs are the published gnomonic formula and quadratic stationary phase.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_rotated_masked_jet_shell_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
    ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
      ∃ A : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧
      ∀ R E δ W C : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C →
      ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)) (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (F : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ F, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a ∧ dist z.1 z.2*(2:ℝ)^a ≤ W) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (descriptorPairAmplitude Q ρ (fun u => profile (u/N)) N σ J i F S x y) w‖ ≤ C*E^l) →
      ∀ U : ℝ, 0 < U → ∀ (v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*((2:ℝ)^a)⁻¹ ∧ E^2 ≤ r*((2:ℝ)^a)⁻¹ ∧
          r*((2:ℝ)^a)⁻¹ ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
          1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      (2:ℝ)^(-(a:ℝ)) *
          (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
            ‖charFun (maskedCellDistance w₀ Q ρ profile N σ J i a F S X Y) r‖^2) ≤
        2*(rotatedInverseShellCost n k F A U δ W hδ hW *
          jetStateEnvelope (n+1) (2*k) L 1 F F Q ρ (fun u => profile (u/N)) N σ J i S U
            (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
            (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ) +
        2*(2:ℝ)^(v-a)*
          (|(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
            ((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C*R^(-Z))*
              ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  obtain ⟨k,A₀,hA₀,hrem⟩ := exists_rotated_masked_fourier_inverse_order hgnomonic hquadratic n (Z := Z) hκ
  refine ⟨k,A₀,hA₀,?_⟩
  intro L
  choose A hA hfamily using fun j : Fin (k+1) => exists_rotatedRootSymbols n j.val L
  refine ⟨A,hA,?_⟩
  intro R E δ W C hR hE hER hδ hW hC T w₀ Q ρ _ profile N σ J i a F S X Y
    hcover hseparated hradius hsep hnear hderiv U hU v Ψ hΨ hpos hzero hone _ hregime hfreq
  let family (j : Fin (k+1)) : RotatedRootSymbols n j.val L F T (A j) :=
    Classical.choice (hfamily j F T)
  have hM : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hsep' : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      δ ≤ dist z.1 z.2/((2:ℝ)^a)⁻¹ ∧ dist z.1 z.2/((2:ℝ)^a)⁻¹ ≤ W := by
    simpa only [div_inv_eq_mul] using hsep
  have hInt (r : ℝ) : Integrable (fun z : Space (n+3) × Space (n+3) =>
      rotatedScaledWeightedInverseSum n k T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
        (descriptorPairAmplitude Q ρ (fun u => profile (u/N)) N σ J i F S z.1 z.2))
      ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) := by
    exact rotated_inverse_jet_integrable k A family (fun j => zero_lt_one.trans_le (hA j))
      Q ρ (fun u => profile (u/N)) N σ J i S hseparated hU δ hδ
      ((2:ℝ)^a)⁻¹ (ρ.restrict X.carrier) (ρ.restrict Y.carrier) (hsep'.mono fun _ hz => hz.1) r
  let := maskedCellDistance_finite w₀ Q ρ profile N σ J i a F S hcover (by omega)
    hδ X Y (hsep.mono fun _ hz => hz.1)
  have hscalar := scalar_shell_of_rotated_inverse k A family
    (fun j => zero_lt_one.trans_le (hA j))
    Q ρ (fun u => profile (u/N)) N σ J i S hseparated hU hE
    hradius δ W hδ hW (by positivity) (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
    hsep' hM hM a v Ψ hΨ hpos hzero hone hregime
    (charFun (maskedCellDistance w₀ Q ρ profile N σ J i a F S X Y)) measurable_charFun
    (ε := |(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
      (δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C*R^(-Z)*
        ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ))
  have hb := hscalar (by
    filter_upwards [hfreq] with r hr
    rw [norm_sub_rev]
    exact hrem T R E r δ hR hE hER hδ w₀ Q ρ profile N σ J i a F S X Y hcover
      (hsep.mono fun _ hz => hz.1) hnear hr C hC hderiv (hInt r))
  exact hb.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialFreezing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CellNorthFrame
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One angular frame for all pairs in separated original cells -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem separated_cells_north_frame (m : ℕ) (P Q : DyadicCube (m+3))
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*(((m+3:ℕ):ℝ)+1)*P.side ≤ ‖P.center-Q.center‖) :
    ∃ T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3),
      ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier,
        ‖T (normalize (x-y))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
  have hs : 0 < 125*(((m+3:ℕ):ℝ)+1)*P.side := by positivity
  have hc : P.center-Q.center ≠ 0 := norm_pos_iff.mp (hs.trans_le hsep)
  let u : Sphere (m+3) := ⟨normalize (P.center-Q.center),by
    rw [Metric.mem_sphere,dist_zero_right,norm_normalize hc]⟩
  refine ⟨northRotation u,?_⟩
  intro x hx y hy
  have hpoints := P.separated_pairs_lower Q hP hQ hsep hx hy
  have hxy : x-y ≠ 0 := norm_pos_iff.mp
    ((show 0 < 100*(((m+3:ℕ):ℝ)+1)*P.side by positivity).trans_le hpoints)
  have hx' := P.dist_le hP.le (P.center_mem hP) hx
  have hy' := Q.dist_le (by rw [hQ]; exact hP.le) hy
    (Q.center_mem (by rw [hQ]; exact hP))
  rw [hQ] at hy'
  have hd : dist (P.center-Q.center) (x-y) ≤ 2*Real.sqrt (m+3:ℕ)*P.side := by
    rw [dist_eq_norm,show (P.center-Q.center)-(x-y) = (P.center-x)+(y-Q.center) by abel]
    exact (norm_add_le _ _).trans (by rw [← dist_eq_norm,← dist_eq_norm]; linarith)
  have hn := normalize_distance_scaled hsep hxy
  have hsmall : dist (normalize (x-y)) (normalize (P.center-Q.center)) ≤ 1/8 := by
    rw [dist_comm] at hn
    have hdim := mul_le_mul_of_nonneg_right (sqrt_dimension_le (m+3)) hP.le
    nlinarith
  rw [← linearIsometryEquiv_normalize_sub,northRotation_cap_norm]
  exact hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfilePairMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pair mass in its exact profile normalization -/

namespace Falconer
open Set MeasureTheory

theorem regularized_pair_model_mass {d : ℕ} (Q : DyadicCube d) (ρ : Measure (Space d))
    {profile : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile)
    {a : ℕ} (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) :
    |(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
      ((ρ.restrict (Q.descendant X).carrier).prod
        (ρ.restrict (Q.descendant Y).carrier)).real univ ≤
      ((2:ℝ)^N)^(2*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have hR : 0 < (2:ℝ)^N := by positivity
  have hM : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hm (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (ρ.restrict (Q.descendant Z).carrier).real univ/profileModelMass profile N a ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam) := by
    rw [measureReal_def,Measure.restrict_apply_univ]
    apply (div_le_iff₀ hM).mpr
    exact (hreg.cell_mass_upper ha Z hZ).trans_eq
      (by rw [profileModelMass,← Real.rpow_add hR]; rfl)
  have hp : ((ρ.restrict (Q.descendant X).carrier).prod
      (ρ.restrict (Q.descendant Y).carrier)).real univ =
      (ρ.restrict (Q.descendant X).carrier).real univ *
        (ρ.restrict (Q.descendant Y).carrier).real univ := by
    simp only [measureReal_def,← univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
  rw [hp,abs_of_pos (mul_pos (inv_pos.mpr hM) (inv_pos.mpr hM))]
  calc
    _ = ((ρ.restrict (Q.descendant X).carrier).real univ/profileModelMass profile N a)*
        ((ρ.restrict (Q.descendant Y).carrier).real univ/profileModelMass profile N a) := by ring
    _ ≤ ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(((d:ℝ)+1)*lam) :=
      mul_le_mul (hm X hX) (hm Y hY) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DescriptorShellRegime
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual source shell satisfies the descriptor stationary regime -/

namespace Falconer
open Set MeasureTheory

theorem source_shell_frequency_bounds (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      (2:ℝ)^v/4 < r ∧ r < 4*(2:ℝ)^v := by
  have hn : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      Ψ (r/(2:ℝ)^v) ≠ 0 := by
    unfold PlanarFalconer.sourceAngularShellMeasure
    apply (ae_withDensity_iff (by fun_prop)).mpr
    filter_upwards with r hr
    intro hz
    apply hr
    simp only [hz,zero_div,ENNReal.ofReal_zero]
  filter_upwards [hn] with r hr
  have h := hsupp _ hr
  constructor
  · have hl := (lt_div_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.1
    linarith
  · exact (div_lt_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.2

theorem eventual_descriptor_source_shell_regime {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        1 ≤ r*(2:ℝ)^(-a) ∧
        (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
        r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a) ∧
        (descriptorDerivativeScale N σ L)^2/(r*(2:ℝ)^(-a)) ≤ ((2:ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := eventual_descriptor_inverse_frequency hσ hσ1
  refine ⟨N₀,?_⟩
  intro N hN L a v hLN hq hL
  filter_upwards [source_shell_frequency_bounds v Ψ hΨ hsupp] with r hr
  obtain ⟨hD,hDu,hΛ,hR⟩ := hN₀ N hN L (v-a) (r*(2:ℝ)^(-a)) hLN hq hL
    (dyadic_shell_frequency_lower hr.1.le)
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  have hsmall : ((2:ℝ)^N)^(-17*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  refine ⟨hD,hDu,hΛ,(div_le_one hΛpos).mp (hR.trans hsmall),?_,hR⟩
  calc
    _ ≤ (4*(2:ℝ)^v)*(2:ℝ)^(-a) :=
      mul_le_mul_of_nonneg_right hr.2.le (by positivity)
    _ = 4*(2:ℝ)^(v-a) := by
      rw [mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 2

theorem eventually_separated_inverse_frequency {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D r s t : ℝ, 1 ≤ D → 0 < s → δ ≤ t/s →
      0 < r*s → D^2/(r*s) ≤ ((2:ℝ)^N)^(-17*σ) →
      1 ≤ r*t ∧ D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ δ⁻¹
  refine ⟨N₀,?_⟩
  intro N hN D r s t hD hs ht hΛ hratio
  have hr : 0 < r := (mul_pos_iff_of_pos_right hs).mp hΛ
  have hst : δ*s ≤ t := (le_div_iff₀ hs).mp ht
  have hδΛ : 0 < (r*s)*δ := mul_pos hΛ hδ
  have hlower : (r*s)*δ ≤ r*t := by nlinarith [mul_le_mul_of_nonneg_left hst hr.le]
  have hrt : 0 < r*t := hδΛ.trans_le hlower
  have hbound : D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
    calc
      _ ≤ D^2/((r*s)*δ) := div_le_div_of_nonneg_left (sq_nonneg _) hδΛ hlower
      _ = δ⁻¹*(D^2/(r*s)) := by ring
      _ ≤ δ⁻¹*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hδ.le)
      _ ≤ ((2:ℝ)^N)^σ*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
      _ = ((2:ℝ)^N)^(-16*σ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
  have hsmall : ((2:ℝ)^N)^(-16*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  exact ⟨(one_le_pow₀ hD).trans ((div_le_one hrt).mp (hbound.trans hsmall)),hbound⟩


theorem eventual_descriptor_pair_shell_regime {d : ℕ} {σ δ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ (μ ν : Measure (Space d)),
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/(2:ℝ)^(-a)) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        (0 < r*(2:ℝ)^(-a) ∧
          (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
          r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a)) ∧
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧
          (descriptorDerivativeScale N σ L)^2/(r*dist z.1 z.2) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₁,hN₁⟩ := eventual_descriptor_source_shell_regime hσ hσ1 Ψ hΨ hsupp
  obtain ⟨N₂,hN₂⟩ := eventually_separated_inverse_frequency hσ hδ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN L a v hLN hq hL μ ν hsep
  filter_upwards [hN₁ N ((le_max_left _ _).trans hN) L a v hLN hq hL] with r hr
  obtain ⟨hD,hDu,hΛ,hDΛ,hΛu,hratio⟩ := hr
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  refine ⟨hD,hDu,⟨hΛpos,hDΛ,hΛu⟩,?_⟩
  filter_upwards [hsep] with z hz
  exact hN₂ N ((le_max_right _ _).trans hN) _ r ((2:ℝ)^(-a)) (dist z.1 z.2)
    hD (by positivity) hz hΛpos hratio

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyScalarConversion
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform conversion of the actual positive high shell

The scale hypotheses are those supplied by the high-prefix geometry.
The original pair mass, finite inverse cost, and squared remainder are
paid before the converted energy enters the policy graph recurrence.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_policy_scalar_conversion_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (lam T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
    (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.Z = Z → N₀ ≤ P.N →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a →
      (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N →
      ∀ w₀ : Sphere (m+3),
      (2:ℝ)^(-(P.a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
          ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
            P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
      ((2:ℝ)^P.N)^ε*P.envelope K L Ψ+((2:ℝ)^P.N)^(-T) := by
  let β : ℝ := 2*((m+3:ℕ)+1)*lam
  let accuracy : ℝ := β+(T+2)/2
  obtain ⟨k,A₀,hA₀,horder⟩ := exists_rotated_masked_jet_shell_order hgnomonic hquadratic m
    (κ := 16*σ) (Z := accuracy) (by positivity)
  let order := 2*(k+1)+(m+2)+1
  let C : ℝ := (2:ℝ)^order
  let Cerr : ℝ := δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr,C]; positivity
  obtain ⟨Nder,hder⟩ := uniform_descriptor_pair_derivatives (m+3) order 3 hσ
  obtain ⟨Nfreq,hfreq⟩ := eventual_descriptor_pair_shell_regime (d := m+3) hσ hσ1 hδ Ψ hΨ hsupp
  obtain ⟨Nrad,hrad⟩ := Regularization.fixed_constant_absorbed hσ 8
  obtain ⟨Ntwo,htwo⟩ := Regularization.fixed_constant_absorbed (half_pos hε) 2
  obtain ⟨Nerr,herr⟩ := eventual_scalar_shell_error_budget T hCerr
    (show 0 ≤ 4*V from mul_nonneg (by norm_num) hV)
  refine ⟨max (2*k) minJet,le_max_right _ _,?_⟩
  intro L Z hZ
  obtain ⟨A,hA,hshell⟩ := horder L
  obtain ⟨Ncost,hcost⟩ := eventual_rotated_root_shell_cost m k A Z δ W hδ hW (half_pos hε)
  refine ⟨max (max Nder Nfreq) (max (max Nrad Ntwo) (max Nerr Ncost)),?_⟩
  intro P hσP hlam hZP hN hcover hsep hcenter hgap hlength w₀
  let := P.regular.probability
  obtain ⟨e,he⟩ := separated_cells_north_frame m (P.Q.descendant P.X) (P.Q.descendant P.Y)
    (P.Q.descendant_side_pos (by rw [P.unit]; norm_num) P.X)
    (by rw [P.Q.descendant_side,P.Q.descendant_side,P.X_length,P.Y_length]) hcenter
  have hnear : ∀ᵐ z : Space (m+3) × Space (m+3)
      ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod (P.ρ.restrict (P.Q.descendant P.Y).carrier),
      ‖e (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (P.Q.descendant P.X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
    exact he z.1 hx z.2 hy
  have hNd : Nder ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNf : Nfreq ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNr : Nrad ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hNt : Ntwo ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hNe : Nerr ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNc : Ncost ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have htN : P.t ≤ P.N := P.base_right.trans P.base_N
  have haN : P.a ≤ P.N := by
    have hp : 0 ≤ 20*P.σ*(P.N:ℝ) := by rw [hσP]; positivity
    have hat : (P.a:ℝ) ≤ P.t := by linarith
    exact (Nat.cast_le.mp hat).trans htN
  have hsp : ∀ r, 4 < r → Ψ r = 0 := by
    intro r hr
    by_contra hn
    exact (not_lt_of_ge hr.le) (hsupp r hn).2
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hV hΨV hsp
  let E := descriptorDerivativeScale P.N P.σ P.longest
  have hE : 1 ≤ E := descriptorDerivativeScale_ge_one P.N (by simpa [hσP] using hσ.le) _
  have hEupper : E ≤ ((2:ℝ)^P.N)^2 := descriptorDerivativeScale_le_square P.N P.longest
    (by simpa [hσP] using hσ.le) (by simpa [hσP] using hσ1) P.longest_le_N
  have hradius : ∀ b ∈ P.list, (descriptorMaskRadius P.N P.σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)).trans
    change 8*max 1 _ ≤ ((2:ℝ)^P.N)^P.σ*max 1 _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [hσP] using hrad P.N hNr
  have hsep' : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
      (P.ρ.restrict (P.Q.descendant P.Y).carrier), δ ≤ dist z.1 z.2/(2:ℝ)^(-(P.a:ℝ)) := by
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_inv_eq_mul]
      using hsep.mono (fun _ hz => hz.1)
  have hfreqP := hfreq P.N hNf P.longest P.a P.t P.longest_le_N
    (by simpa only [hσP] using hgap) (by simpa only [hσP] using hlength)
    (P.ρ.restrict (P.Q.descendant P.X).carrier) (P.ρ.restrict (P.Q.descendant P.Y).carrier) hsep'
  have hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ,
      0 < r*((2:ℝ)^P.a)⁻¹ ∧ E^2 ≤ r*((2:ℝ)^P.a)⁻¹ ∧
        r*((2:ℝ)^P.a)⁻¹ ≤ 4*(2:ℝ)^((P.t:ℝ)-P.a) := by
    simpa only [E,hσP,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
      using hfreqP.mono (fun _ hr => hr.2.2.1)
  have hf : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ,
      ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ ((2:ℝ)^P.N)^(-(16*σ)) := by
    simpa only [E,hσP,neg_mul] using hfreqP.mono (fun _ hr => hr.2.2.2)
  have hd := hder P.N hNd P.Q P.ρ (fun u => P.profile (u/P.N)) P.J P.i P.longest
    P.list P.masks P.list_card (fun b hb => Finset.le_sup hb)
    (by simpa only [PolicyJetData.list,hσP] using P.separated)
  have hd' : ∀ x y l, l ≤ 2*(k+1)+(m+2)+1 → ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ l (descriptorPairAmplitude P.Q P.ρ (fun u => P.profile (u/P.N))
        P.N P.σ P.J P.i P.list P.masks x y) w‖ ≤ C*E^l := by
    simpa only [order,C,E,hσP] using fun x y l hl (w : Sphere (m+3)) => hd x y l hl w
  have hb := hshell ((2:ℝ)^P.N) E δ W C (one_le_pow₀ (by norm_num)) hE hEupper hδ hW
    (one_le_pow₀ (by norm_num)) e w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list P.masks
    (P.Q.descendant P.X) (P.Q.descendant P.Y) hcover P.separated hradius hsep hnear hd'
    Z hZ P.t Ψ hΨ hpos hzero hone hregime hf
  let η : ℝ := |(profileModelMass P.profile P.N P.a)⁻¹*(profileModelMass P.profile P.N P.a)⁻¹| *
    ((δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C*((2:ℝ)^P.N)^(-accuracy))*
      ((P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier)).real univ)
  have hη : 0 ≤ η := by dsimp [η,C]; positivity
  have hm := regularized_pair_model_mass P.Q P.ρ P.regular haN P.X P.Y P.X_length P.Y_length
  have hηbound : η ≤ Cerr*((2:ℝ)^P.N)^(-((T+2)/2)) := by
    calc
      _ = Cerr*(|(profileModelMass P.profile P.N P.a)⁻¹*(profileModelMass P.profile P.N P.a)⁻¹| *
          ((P.ρ.restrict (P.Q.descendant P.X).carrier).prod
            (P.ρ.restrict (P.Q.descendant P.Y).carrier)).real univ)*((2:ℝ)^P.N)^(-accuracy) := by
        dsimp [η,Cerr]; ring
      _ ≤ Cerr*((2:ℝ)^P.N)^β*((2:ℝ)^P.N)^(-accuracy) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hCerr
        simpa only [hlam,β,Nat.cast_add,Nat.cast_ofNat] using hm
      _ = _ := by rw [mul_assoc,← Real.rpow_add (by positivity)]; dsimp [accuracy]; congr 2; ring
  have he : 2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2*
      (PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ).real univ ≤ ((2:ℝ)^P.N)^(-T) := by
    apply (mul_le_mul_of_nonneg_left
      (PlanarFalconer.sourceAngularShellMeasure_real_mass_le (P.t:ℝ) Ψ hV hΨV hsp)
      (by positivity : 0 ≤ 2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2)).trans
    exact herr P.N hNe _ η (by have hh : (P.t:ℝ) ≤ P.N := Nat.cast_le.mpr htN; linarith [Nat.cast_nonneg (α := ℝ) P.a]) hη hηbound
  have hcoeff : 2*rotatedInverseShellCost m k P.list A Z δ W hδ hW ≤ ((2:ℝ)^P.N)^ε := by
    calc
      _ ≤ ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(ε/2) :=
        mul_le_mul (htwo P.N hNt) (hcost P.N hNc P.list P.list_card)
          (by unfold rotatedInverseShellCost; positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hM : 0 < profileModelMass P.profile P.N P.a := by unfold profileModelMass; positivity
  have henv : 0 ≤ P.envelope (2*k) L Ψ :=
    le_csSup (jetStateValues_bddAbove P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i
      P.masks P.separated P.separated P.Z_pos _ _ hM hM P.a P.t Ψ) (Or.inl rfl)
  rw [← hZP] at hb
  change _ ≤ 2*(_*P.envelope (2*k) L Ψ)+2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2*_ at hb
  rw [← hZP] at hcoeff
  have hmain : 2*(rotatedInverseShellCost m k P.list A P.Z δ W hδ hW *
      P.envelope (2*k) L Ψ) ≤ ((2:ℝ)^P.N)^ε*P.envelope (2*k) L Ψ := by
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff henv]
  have hbase := hb.trans (add_le_add hmain he)
  have hmono : P.envelope (2*k) L Ψ ≤ P.envelope (max (2*k) minJet) L Ψ :=
    jetStateEnvelope_budget_mono (le_max_left _ _) le_rfl (by norm_num) le_rfl
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks
      P.separated P.separated P.Z_pos _ _ hM hM P.a P.t Ψ
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmono (show 0 ≤ ((2:ℝ)^P.N)^ε by positivity)) le_rfl)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_policy_scalar_conversion_oai := @OAI.Falconer.exists_policy_scalar_conversion_oai
