-- Prove2me | solution 1 for OAI.Falconer.scalar_shell_of_two_profile_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:31:55.349869+00:00
-- url     : https://prove2.me/submissions/800737e4-dd74-40fd-9506-3be57908cbda

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedInverseFactors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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

end Falconer.MaskJetIndex

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

theorem seed_inverse_radius_cancel (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (a : ((seed k).inverse m j).index) :
    (∏ i, (r i)^(k i).order) *
      (∏ i, (r i)⁻¹^((((seed k).inverse m j).term a).jet i).order) =
    ∏ i, (r i)⁻¹^(((((seed k).inverse m j).term a).jet i).order-(k i).order) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact radius_power_cancel (hr i) ((seed_ordersExtend k).inverse j a i)

theorem seed_inverse_radius_le (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D)
    (hscale : ∀ i, (r i)⁻¹ ≤ D) (a : ((seed k).inverse m j).index) :
    (∏ i, (r i)^(k i).order) *
      (∏ i, (r i)⁻¹^((((seed k).inverse m j).term a).jet i).order) ≤ D^(2*j) := by
  rw [seed_inverse_radius_cancel m j k r (fun i => (hr i).ne') a]
  calc
    _ ≤ ∏ i, D^(((((seed k).inverse m j).term a).jet i).order-(k i).order) := by
      apply Finset.prod_le_prod (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)
      intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hr i).le) (hscale i) _
    _ = D^(∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ D^(2*j) := pow_le_pow_right₀ hD (seed_inverse_added_order m j k a)

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

theorem seededRadiusWeight_nonneg (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ((seed k).inverse m j).index) :
    0 ≤ seededRadiusWeight m j k r a :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)

theorem seededRadiusWeight_le (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D)
    (hscale : ∀ i, (r i)⁻¹ ≤ D) (a : ((seed k).inverse m j).index) :
    seededRadiusWeight m j k r a ≤ D^(2*j) := by
  rw [seededRadiusWeight,← seed_inverse_radius_cancel m j k r (fun i => (hr i).ne') a]
  exact seed_inverse_radius_le m j k r hr hD hscale a

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

end MaskJetExpansion
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
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
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

theorem descriptorInverseWeight_le
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (hD : 0 < D) (j N : ℕ) (σ : ℝ) {E : ℝ} (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    descriptorInverseWeight f g j N σ a ≤ E^(2*j) := by
  apply MaskJetExpansion.seededRadiusWeight_le m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) (descriptorInverseRadius_pos f g hD N σ) hE
  intro l
  rcases l with l | l <;> rcases l with l | b
  · simpa only [descriptorInverseRadius,Sum.elim_inl,DescriptorJetSymbol.seedRadius,inv_inv]
      using hDE
  · exact hF b b.property
  · simpa only [descriptorInverseRadius,Sum.elim_inr,DescriptorJetSymbol.seedRadius,
      Sum.elim_inl,inv_inv] using hDE
  · exact hG b b.property

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

theorem descriptorInverseWeight_nonneg
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (hD : 0 < D)
    (j N : ℕ) (σ : ℝ) (a : DescriptorInverseIndex f g j) :
    0 ≤ descriptorInverseWeight f g j N σ a :=
  MaskJetExpansion.seededRadiusWeight_nonneg m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) (descriptorInverseRadius_pos f g hD N σ) a

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseClassIntegration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair integration of the exact inverse symbol family

The finite factors are the actual output symbols. The original endpoint
measures, both normalizing masses, and every descriptor remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem coefficient_abs_le (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (N : ℕ) (σ Af Ag U V : ℝ) {E : ℝ}
    (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : DescriptorInverseIndex f g j) :
    |T.coefficient N σ Af Ag U V a| ≤
      E^(2*j) * |U*A| * |V*B| * |Af⁻¹| * |Ag⁻¹| := by
  calc
    _ = descriptorInverseWeight f g j N σ a * |U*A| * |V*B| * |Af⁻¹| * |Ag⁻¹| := by
      simp only [coefficient,abs_mul,
        abs_of_nonneg (descriptorInverseWeight_nonneg f g hD j N σ a)]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (descriptorInverseWeight_le f g hD j N σ hE hDE hF hG a) (abs_nonneg (U*A)))
          (abs_nonneg (V*B))) (abs_nonneg (Af⁻¹))) (abs_nonneg (Ag⁻¹))

end DescriptorInverseSymbols
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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetCoefficient
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The radial inverse power pays only the newly added jets -/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

theorem normalized_coefficient_le (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (N : ℕ) (σ Af Ag U : ℝ) {E Λ V h : ℝ}
    (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hΛ : 0 < Λ) (hV : 0 < V) (hh : 0 ≤ h)
    (hEΛ : E^2 ≤ Λ) (hΛV : Λ ≤ 4*V) (a : DescriptorInverseIndex f g j) :
    ‖((Λ^h*(Λ^j)⁻¹/(V^h) : ℝ) : ℂ)*
      (T.coefficient N σ Af Ag U U a : ℂ)‖ ≤
      (|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|)*4^h := by
  have hγ : 0 ≤ Λ^h*(Λ^j)⁻¹/(V^h) := by positivity
  have hc := T.coefficient_abs_le hD N σ Af Ag U U hE hDE hF hG a
  have hr := normalized_stationary_coefficient_le
    (p := 2*j) (q := 0) (j := j) (by omega) hΛ hE hV hh hEΛ hΛV
  simp only [add_zero] at hr
  have hr' : Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h) ≤ (4:ℝ)^h :=
    (le_abs_self _).trans hr
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hγ]
  calc
    _ ≤ (Λ^h*(Λ^j)⁻¹/(V^h))*(E^(2*j)*|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|) :=
      mul_le_mul_of_nonneg_left hc hγ
    _ = (|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|)*(Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)

end DescriptorInverseSymbols
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

namespace DescriptorJetSymbol

theorem relax_value {n K K' L L' : ℕ} {F : Finset PolicyDescriptor} {D D' : ℝ}
    (f : DescriptorJetSymbol n K L F D) (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    (f.relax hK hL hD hDD').value Q ρ m N σ J i S A = f.value Q ρ m N σ J i S A := rfl

end DescriptorJetSymbol

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_TwoProfileInverseIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-profile original-pair integration of the exact inverse family

The finite factors are the actual output symbols. The original endpoint
measures, both normalizing masses, and every descriptor remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

private theorem bounded_sphere_phase_integrable_p3 {d : ℕ}
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
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem two_profile_integration (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3)))
    (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            localInverseAmplitude m
              (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
                g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w
          ∂sphereMeasure (m+3) ∂μ.prod ν =
      ∑ a : DescriptorInverseIndex f g j, (T.coefficient N σ Af Ag U V a : ℂ) *
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
          (spatialEndpointFamily μ M s ((T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U))
          (spatialEndpointFamily ν P s
            (fun x w => star ((T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ V x w))) r := by
  let b := fun a : DescriptorInverseIndex f g j => (T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U
  let c := fun a : DescriptorInverseIndex f g j => (T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ V
  let α := fun a : DescriptorInverseIndex f g j => (T.coefficient N σ Af Ag U V a : ℂ)
  let Z := fun (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₁ := (descriptorJetBound (m+3) (KL+2*j))^(KL+2*j)*U⁻¹
  let C₂ := (descriptorJetBound (m+3) (KR+2*j))^(KR+2*j)*V⁻¹
  have hC₁ : 0 ≤ C₁ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (b a)) :=
    (T.left a).value_measurable Q₁ ρ₁ profile₁ N σ J i S₁ U
  have hc (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (c a)) :=
    (T.right a).value_measurable Q₂ ρ₂ profile₂ N σ J i S₂ V
  have hbB (a : DescriptorInverseIndex f g j) (x) (w) : ‖b a x w‖ ≤ C₁ :=
    (T.left a).value_norm_le Q₁ ρ₁ profile₁ N σ J i S₁ hF hU x w
  have hcC (a : DescriptorInverseIndex f g j) (x) (w) : ‖c a x w‖ ≤ C₂ :=
    (T.right a).value_norm_le Q₂ ρ₂ profile₂ N σ J i S₂ hG hV x w
  have hi (a : DescriptorInverseIndex f g j) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₁ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable_p3 (b a) (c a) (hb a) (hc a) hC₁ (hbB a) (hcC a) r z
  have he (z : Space (m+3) × Space (m+3)) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            localInverseAmplitude m
              (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
                g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w
          ∂sphereMeasure (m+3)) = ∑ a : DescriptorInverseIndex f g j, α a*Z a z := by
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
              g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w) =
        fun w : Sphere (m+3) => ∑ a : DescriptorInverseIndex f g j, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [T.two_profile_expansion hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ Af Ag hU hV]
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

theorem two_profile_scaled_inverse_integration {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
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
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (M P r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν) =
      ∑ j : Fin (k+1), (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j.val)⁻¹ : ℝ) : ℂ)*
        (T j).twoProfilePairIntegral Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ Af Ag s μ ν M P r := by
  let V := fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
    g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z
  have hi (j : Fin (k+1)) : Integrable (scaledInverseTerm m j.val s r V) (μ.prod ν) :=
    (T j).two_profile_original_term_integrable hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
      Af Ag hU δ hδ s μ ν hsep r
  change (M⁻¹*P⁻¹) • (∫ z, scaledWeightedInverseSum m k s r (z.1-z.2) (V z.1 z.2) ∂μ.prod ν) = _
  simp_rw [scaledWeightedInverseSum_eq_terms,← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul _),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,← mul_smul_comm]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_TwoProfileInverseShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite two-profile inverse family controlled by actual angular energies -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem two_profile_inverse_family_shell_integrable {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    Integrable (fun r => ‖twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
      Af Ag U δ W hδ hW s μ ν M P a v r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  unfold twoProfileInverseNormalizedSum
  let C₀ (z : DescriptorInverseFamilyIndex f g k) :=
    (descriptorJetBound (m+3) (K+2*z.1.val))^(K+2*z.1.val)*U⁻¹
  have hC₀ (z : DescriptorInverseFamilyIndex f g k) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_sum_integrable (ι := DescriptorInverseFamilyIndex f g k) Finset.univ a v Ψ δ W hδ hW (fun (z : DescriptorInverseFamilyIndex f g k) => z.1.val)
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily μ M s (((T z.1).left z.2).value Q₁ ρ₁ profile₁ N σ J i S₁ U))
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily ν P s
      (fun x w => star (((T z.1).right z.2).value Q₂ ρ₂ profile₂ N σ J i S₂ U x w)))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable μ M s _
      (((T z.1).left z.2).value_measurable Q₁ ρ₁ profile₁ N σ J i S₁ U))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((T z.1).right z.2).value_measurable Q₂ ρ₂ profile₂ N σ J i S₂ U)))
    (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*μ.real univ/M) (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*ν.real univ/P)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le μ hM s _
      (((T z.1).left z.2).value_norm_le Q₁ ρ₁ profile₁ N σ J i S₁ hF hU))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((T z.1).right z.2).value_norm_le Q₂ ρ₂ profile₂ N σ J i S₂ hG hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ))
    (fun z => (|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))
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
    exact (T z.1).normalized_coefficient_le (h := (((m+2:ℕ):ℝ)/2)) hD N σ Af Ag U hE hDE hFE hGE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2

theorem two_profile_inverse_family_shell_le {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (energy : ℝ)
    (henergy : ∀ (u : DescriptorJetSymbol (m+1) (K+2*k) R F D)
      (w : DescriptorJetSymbol (m+1) (K+2*k) R G D),
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
        (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
        Af Ag U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (DescriptorInverseFamilyIndex f g k) : ℝ)*
        ∑ z : DescriptorInverseFamilyIndex f g k,
          ((|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
            ((spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2*
              energy) := by
  unfold twoProfileInverseNormalizedSum
  let C₀ (z : DescriptorInverseFamilyIndex f g k) :=
    (descriptorJetBound (m+3) (K+2*z.1.val))^(K+2*z.1.val)*U⁻¹
  have hC₀ (z : DescriptorInverseFamilyIndex f g k) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_le (ι := DescriptorInverseFamilyIndex f g k) Finset.univ a v Ψ δ W hδ hW (fun (z : DescriptorInverseFamilyIndex f g k) => z.1.val)
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily μ M s (((T z.1).left z.2).value Q₁ ρ₁ profile₁ N σ J i S₁ U))
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily ν P s
      (fun x w => star (((T z.1).right z.2).value Q₂ ρ₂ profile₂ N σ J i S₂ U x w)))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable μ M s _
      (((T z.1).left z.2).value_measurable Q₁ ρ₁ profile₁ N σ J i S₁ U))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((T z.1).right z.2).value_measurable Q₂ ρ₂ profile₂ N σ J i S₂ U)))
    (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*μ.real univ/M) (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*ν.real univ/P)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le μ hM s _
      (((T z.1).left z.2).value_norm_le Q₁ ρ₁ profile₁ N σ J i S₁ hF hU))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((T z.1).right z.2).value_norm_le Q₂ ρ₂ profile₂ N σ J i S₂ hG hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ))
    (fun z => (|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))
    (fun _ => energy)
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
    exact (T z.1).normalized_coefficient_le (h := (((m+2:ℕ):ℝ)/2)) hD N σ Af Ag U hE hDE hFE hGE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2
  · intro z _ ξ
    have hK : K+2*z.1.val ≤ K+2*k := by have := z.1.isLt; omega
    have hb := henergy
      ((((T z.1).left z.2).spatialFourier s ξ).relax hK le_rfl hD.le le_rfl)
      ((((T z.1).right z.2).conj.spatialFourier s ξ).relax hK le_rfl hD.le le_rfl)
    simp only [DescriptorJetSymbol.relax_value] at hb
    have hf : (((T z.1).left z.2).spatialFourier s ξ).value Q₁ ρ₁ profile₁ N σ J i S₁ U =
        fun x w => spatialFourierPhase s ξ x*((T z.1).left z.2).value Q₁ ρ₁ profile₁ N σ J i S₁ U x w := by
      funext x w
      exact DescriptorJetSymbol.spatialFourier_value _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have hg : (((T z.1).right z.2).conj.spatialFourier s ξ).value Q₂ ρ₂ profile₂ N σ J i S₂ U =
        fun x w => spatialFourierPhase s ξ x*star (((T z.1).right z.2).value Q₂ ρ₂ profile₂ N σ J i S₂ U x w) := by
      funext x w
      rw [DescriptorJetSymbol.spatialFourier_value,DescriptorJetSymbol.conj_value]
    rw [hf,hg] at hb
    exact hb

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TwoProfileInverseScalar
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning the exact inverse jet shell to the scalar Fourier integral -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem two_profile_inverse_normalized_sum_eq {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
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
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P a v r : ℝ) :
    ((M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)) /
      (((2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) : ℝ) : ℂ) =
      twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
        Af Ag U δ W hδ hW s μ ν M P a v r := by
  rw [two_profile_scaled_inverse_integration k R A B T hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
    Af Ag hU δ hδ s μ ν (hsep.mono fun _ hz => hz.1) M P r,Finset.sum_div]
  unfold twoProfileInverseNormalizedSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [DescriptorInverseSymbols.twoProfilePairIntegral,
    (T j).two_profile_integration hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG Af Ag hU hU
      δ W hδ hW hs μ ν hsep M P r,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.ofReal_div,Complex.ofReal_mul]
  ring

theorem scalar_shell_of_two_profile_inverse_oai {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (energy : ℝ)
    (henergy : ∀ (u : DescriptorJetSymbol (m+1) (K+2*k) R F D)
      (w : DescriptorJetSymbol (m+1) (K+2*k) R G D),
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
        (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy)
    (H : ℝ → ℂ) (hH : Measurable H) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖H r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
        scaledWeightedInverseSum m k s r (z.1-z.2)
          (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
            g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)‖ ≤ ε) :
    IntegrableOn (fun r => ‖H r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖H r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
          energy) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hi := two_profile_inverse_family_shell_integrable k R A B T hD Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU hE hDE hFE hGE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb := two_profile_inverse_family_shell_le k R A B T hD Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU hE hDE hFE hGE δ W hδ hW s μ ν hM hP a v Ψ hregime energy henergy
  have hb' : (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
        Af Ag U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
        energy := by
    apply hb.trans_eq
    unfold descriptorInverseShellCost
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  apply scalar_shell_of_stationary_approximation (m+3) a v Ψ hΨ hpos hzero hone H
    (twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
      Af Ag U δ W hδ hW s μ ν M P a v) hH hi _ hb'
  filter_upwards [herr] with r hr
  rw [← two_profile_inverse_normalized_sum_eq k R A B T hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU δ W hδ hW hs μ ν hsep M P a v r]
  have he : (v-a)*(((m+3:ℕ):ℝ)-1)/2 = (v-a)*(((m+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  rw [he,mul_div_cancel₀ _ (by exact_mod_cast
    (ne_of_gt (show 0 < (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) by positivity)))]
  exact hr

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.scalar_shell_of_two_profile_inverse_oai := @OAI.Falconer.scalar_shell_of_two_profile_inverse_oai
