-- Prove2me | solution 1 for OAI.Falconer.exists_rotated_masked_fourier_inverse_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:21:44.931982+00:00
-- url     : https://prove2.me/submissions/ab9ff862-294a-4c4e-a338-8c1a182cb20f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_sphere_stationary_expansion

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

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem verticalDirections_norm {n : ℕ} (i : Fin n) :
    ‖(verticalDirections n i : P × Space n)‖ ≤ 1 := by
  simp [verticalDirections, Prod.norm_def]

end Parameters

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

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

theorem anchoredMask_measurable {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (hF : ∀ p, Measurable (F p)) :
    Measurable (Function.uncurry (anchoredMask Q n F)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((hF p).comp measurable_snd).ite
    ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

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

theorem anchoredBufferedMask_measurable {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (U : List (Fin d → Bool) → Set (Sphere d)) :
    Measurable (Function.uncurry (anchoredBufferedMask Q g δ hδ S U)) := by
  apply anchoredMask_measurable
  intro p
  exact (capCutoffAmbient_contDiff hδ S (U p)).continuous.measurable.comp continuous_subtype_val.measurable

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

theorem descriptorMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) : Measurable (Function.uncurry (descriptorMask Q ρ m N σ J i b S)) :=
  anchoredBufferedMask_measurable Q _ (descriptorMaskRadius_pos N σ b) S _

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

theorem descriptorAmbientMask_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientMask Q ρ m N σ J i b S x w = descriptorMask Q ρ m N σ J i b S x w := rfl

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

theorem descriptorProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorMask_measurable Q ρ m N σ J i b (S b))

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedLowpass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive lowpass comparison for the actual masked distance law

The comparison is made between positive measures before taking Fourier
transforms. All old masks remain in the weighted distance pushforward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem descriptorPairWeight_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (descriptorPairWeight w₀ Q ρ m N σ J i a B S) := by
  have hw := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  exact ((measurable_fst.dist measurable_snd).mul_const _).pow_const _ |>.mul
    ((descriptorProduct_measurable Q ρ (fun u => m (u/N)) N σ J i B S).comp (measurable_fst.prodMk hw)) |>.mul
    ((descriptorProduct_measurable Q ρ (fun u => m (u/N)) N σ J i B S).comp (measurable_snd.prodMk hw))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskedFourier
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier transform of the original masked pair law

The pair measure is unchanged; the distance weight and every old descriptor
mask stay inside its integral. This is the input to stationary inversion.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem descriptorPairWeight_nonneg (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (z : Space d × Space d) :
    0 ≤ descriptorPairWeight w₀ Q ρ m N σ J i a B S z := by
  exact mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg dist_nonneg (by positivity)) _)
    (descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover _ _).1)
    (descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover _ _).1

theorem integral_maskedCellDistance (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube d) (F : ℝ → ℂ)
    (hF : AEStronglyMeasurable F (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)) :
    (∫ s, F s ∂maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) =
      ∫ z, ((profileModelMass m N a)⁻¹^2 *
        descriptorPairWeight w₀ Q ρ m N σ J i a B S z) • F (dist z.1 z.2)
        ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [maskedCellDistance,integral_map (by fun_prop) hF]
  have hw : Measurable (fun z : Space d × Space d => ENNReal.ofReal
      ((profileModelMass m N a)⁻¹^2 * descriptorPairWeight w₀ Q ρ m N σ J i a B S z)) :=
    (measurable_const.mul (descriptorPairWeight_measurable w₀ Q ρ m N σ J i a B S)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
    (descriptorPairWeight_nonneg w₀ Q ρ m N σ J i a B S hcover z))]

theorem maskedCellDistance_fourier (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube d) (r : ℝ) :
    charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r =
      ∫ z, (((profileModelMass m N a)⁻¹^2 *
        descriptorPairWeight w₀ Q ρ m N σ J i a B S z : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((r * dist z.1 z.2 : ℝ) : ℂ))
        ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [charFun_apply_real,integral_maskedCellDistance w₀ Q ρ m N σ J i a B S hcover]
  · apply integral_congr_ae
    filter_upwards with z
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring_nf
  · fun_prop

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

 theorem descriptorAmbientProduct_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientProduct Q ρ m N σ J i B S x w = descriptorProduct Q ρ m N σ J i B S x w := by
  simp only [descriptorAmbientProduct,descriptorProduct,descriptorAmbientMask_sphere]

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorScaledKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked distance law as a cell-scaled stationary target

The unit profile is evaluated at depth divided by N in the descriptor
amplitude. Both masks and the original pair law remain in this identity.
-/

namespace Falconer
open Set MeasureTheory

theorem descriptorPairAmplitude_measurable {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (fun p : (Space d × Space d) × Space d =>
      descriptorPairAmplitude Q ρ f N σ J i B S p.1.1 p.1.2 p.2) := by
  have hm := descriptorAmbientProduct_measurable Q ρ f N σ J i B S
  exact (Complex.measurable_ofReal.comp (hm.comp (measurable_fst.fst.prodMk measurable_snd))).mul
    (Complex.measurable_ofReal.comp (hm.comp (measurable_fst.snd.prodMk measurable_snd)))

theorem maskedCellDistance_fourier_scaled_kernel (n : ℕ) (w₀ : Sphere (n+3))
    (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i a : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
    (hcover : ∀ b ∈ B, ∀ w : Sphere (n+3),
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube (n+3))
    (hne : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z.1-z.2 ≠ 0)
    (r : ℝ) :
    charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r =
      ((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
        ∫ z, scaledDistanceKernel n ((2:ℝ)^a)⁻¹ r
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S) z
          ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [maskedCellDistance_fourier w₀ Q ρ m N σ J i a B S hcover X Y r,← integral_smul]
  apply integral_congr_ae
  filter_upwards [hne] with z hz
  have hw : NormedSpace.normalize (z.1-z.2) =
      (normalizeToSphere w₀ (z.1-z.2) : Space (n+3)) :=
    (normalizeToSphere_coe_of_ne w₀ hz).symm
  have hexp : -((((n+3:ℕ):ℝ)-1)/2) = -(((n+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  simp only [scaledDistanceKernel,descriptorPairAmplitude,descriptorPairWeight,hw,
    descriptorAmbientProduct_sphere,div_inv_eq_mul,hexp,Complex.real_smul,
    Complex.ofReal_mul]
  push_cast
  ring

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

theorem descriptorPairAmplitude_norm_le (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x y w : Space d) :
    ‖descriptorPairAmplitude Q ρ f N σ J i B S x y w‖ ≤ 1 := by
  have hx := descriptorAmbientProduct_global_bounds Q ρ f N σ J i B S x w
  have hy := descriptorAmbientProduct_global_bounds Q ρ f N σ J i B S y w
  simp only [descriptorPairAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hx.1,abs_of_nonneg hy.1]
  exact (mul_le_mul hx.2 hy.2 hy.1 (by norm_num)).trans_eq (one_mul 1)

theorem descriptorPairAmplitude_contDiff (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x y : Space d) :
    ContDiff ℝ ∞ (descriptorPairAmplitude Q ρ f N σ J i B S x y) :=
  (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S x)).mul
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S y))

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

 theorem exists_rotated_scaled_weighted_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ E : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (z : Space (m+3)), z ≠ 0 →
      ‖T (normalize z)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ s r : ℝ, 0 < s → 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖rotatedScaledWeightedInverseSum m J T s r z B -
          (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        (‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-E) := by
  obtain ⟨J,A,hA,hi⟩ := exists_scaled_weighted_inverse_order hgnomonic hquadratic m (T := E) hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR T z hz hnear B hB C hC hderiv s r hs hfreq hratio
  have hTz : T z ≠ 0 := by
    intro h
    exact hz (T.injective (h.trans T.map_zero.symm))
  have hb : ∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (B ∘ T.symm) w‖ ≤ C*D^j := by
    intro j hj w
    rw [T.symm.norm_iteratedFDeriv_comp_right]
    exact hderiv j hj (sphereMap T.symm w)
  have he := hi R D hR hD hDR (T z) hTz
    (by simpa only [linearIsometryEquiv_normalize] using hnear)
    (B ∘ T.symm) (hB.comp T.symm.contDiff) C hC hb s r hs
    (by simpa only [T.norm_map] using hfreq) (by simpa only [T.norm_map] using hratio)
  simpa only [rotatedScaledWeightedInverseSum,T.norm_map,linearIsometryEquiv_normalize,
    Function.comp_apply,T.symm_apply_apply] using he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseRemainder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rotated stationary remainder on the original pair measure -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

theorem exists_integrated_rotated_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ E : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)), ∀ R D s r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < s → 0 < δ →
      ∀ (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ,
      Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) => B p.1.1 p.1.2 p.2) →
      (∀ x y, ContDiff ℝ ∞ (B x y)) →
      ∀ C : ℝ, 0 ≤ C → (∀ x y w, ‖B x y w‖ ≤ C) →
      (∀ x y k, k ≤ 2*(J+1)+(m+2)+1 → ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (B x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (m+3) × Space (m+3) =>
        rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2)) (μ.prod ν) →
      ∀ M P : ℝ,
      ‖(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
          rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2) ∂μ.prod ν) -
        (M⁻¹*P⁻¹) • (∫ z, scaledDistanceKernel m s r B z ∂μ.prod ν)‖ ≤
      |M⁻¹*P⁻¹| *((δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-E))*(μ.prod ν).real univ) := by
  obtain ⟨J,A,hA,hi⟩ := exists_rotated_scaled_weighted_inverse_order hgnomonic hquadratic m (E := E) hκ
  refine ⟨J,A,hA,?_⟩
  intro T R D s r δ hR hD hDR hs hδ μ ν _ _ hsep hnear hfreq B hBm hBs C hC hbound hderiv hInt M P
  have ht := scaledDistanceKernel_integrable m s r δ hδ μ ν hsep B hBm hbound
  have he : ∀ᵐ z ∂μ.prod ν,
      ‖rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2) -
        scaledDistanceKernel m s r B z‖ ≤ δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-E) := by
    filter_upwards [hsep,hnear,hfreq] with z hz hn hf
    have hdist : 0 < dist z.1 z.2 := (div_pos_iff_of_pos_right hs).mp (hδ.trans_le hz)
    have hzne : z.1-z.2 ≠ 0 := by
      intro h
      exact (ne_of_gt hdist) (by rw [sub_eq_zero.mp h,dist_self])
    have hnorm : ‖z.1-z.2‖ = dist z.1 z.2 := rfl
    have hh := hi R D hR hD hDR T (z.1-z.2) hzne hn (B z.1 z.2) (hBs _ _)
      C hC (hderiv _ _) s r hs (by simpa only [hnorm] using hf.1)
      (by simpa only [hnorm] using hf.2)
    simp only [hnorm] at hh
    change ‖rotatedScaledWeightedInverseSum m J T s r (z.1-z.2) (B z.1 z.2) -
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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedMaskedRemainder
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary remainder for the actual masked distance Fourier transform

This is the original masked law, with its original model mass and its
cell-scale distance weight. The integrability premise is supplied by the
finite separated inverse integration theorem.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem exists_rotated_masked_fourier_inverse_order_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
    ∃ K : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)), ∀ R D r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < δ →
      ∀ (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ B, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ C : ℝ, 1 ≤ C →
      (∀ x y k, k ≤ 2*(K+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (n+3) × Space (n+3) =>
        rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2))
        ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) →
      ‖((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
          (∫ z : Space (n+3) × Space (n+3),
            rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
              (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2)
            ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) -
        charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖ ≤
      |(profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹| *
        ((δ^(-(((n+2:ℕ):ℝ)/2))*A*C*R^(-Z))*
          ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ) := by
  obtain ⟨K,A,hA,hbound⟩ := exists_integrated_rotated_inverse_order hgnomonic hquadratic n (E := Z) hκ
  refine ⟨K,A,hA,?_⟩
  intro T R D r δ hR hD hDR hδ w₀ Q ρ _ m N σ J i a B S X Y hcover hsep hnear hfreq C hC hderiv hInt
  have hs : 0 < ((2:ℝ)^a)⁻¹ := by positivity
  have hsep' : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      δ ≤ dist z.1 z.2/((2:ℝ)^a)⁻¹ := by
    simpa only [div_inv_eq_mul] using hsep
  have hne : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z.1-z.2 ≠ 0 := by
    filter_upwards [hsep] with z hz
    have hd : 0 < dist z.1 z.2 :=
      (mul_pos_iff_of_pos_right (show 0 < (2:ℝ)^a by positivity)).mp (hδ.trans_le hz)
    exact sub_ne_zero.mpr (dist_pos.mp hd)
  rw [maskedCellDistance_fourier_scaled_kernel n w₀ Q ρ m N σ J i a B S hcover X Y hne]
  exact hbound T R D ((2:ℝ)^a)⁻¹ r δ hR hD hDR hs hδ
    (ρ.restrict X.carrier) (ρ.restrict Y.carrier) hsep' hnear hfreq
    (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S)
    (descriptorPairAmplitude_measurable Q ρ (fun u => m (u/N)) N σ J i B S)
    (descriptorPairAmplitude_contDiff Q ρ (fun u => m (u/N)) N σ J i B S)
    C (zero_le_one.trans hC)
    (fun x y w => (descriptorPairAmplitude_norm_le Q ρ (fun u => m (u/N)) N σ J i B S x y w).trans hC)
    hderiv hInt (profileModelMass m N a) (profileModelMass m N a)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_rotated_masked_fourier_inverse_order_oai := @OAI.Falconer.exists_rotated_masked_fourier_inverse_order_oai
