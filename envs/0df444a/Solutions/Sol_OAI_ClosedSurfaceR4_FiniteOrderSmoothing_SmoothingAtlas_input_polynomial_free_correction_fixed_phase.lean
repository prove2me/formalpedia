-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:47:37.879411+00:00
-- url     : https://prove2.me/submissions/3aac5790-a139-4018-8176-b9fdddfef342

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_global_polynomial_mean
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_mode_polynomial_quadratic
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_input_cancellation_all_profiles
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_target_profiles
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_seed_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

lemma phase_add (θ ψ : ℝ) : phase (θ + ψ) = phase θ * phase ψ := by
  simp only [phase, ofReal_add, add_mul, Complex.exp_add]

lemma phase_conj (θ : ℝ) : star (phase θ) = phase (-θ) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ofReal_neg]
  congr 1
  ring

lemma phase_sub (θ ψ : ℝ) : phase (θ - ψ) = phase θ * star (phase ψ) := by
  rw [phase_conj, ← phase_add, sub_eq_add_neg]

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma real_product (a b : ℂ) : a.re * b.re = ((a * star b).re + (a * b).re) / 2 := by
  simp only [Complex.star_def, mul_re, conj_re, conj_im]
  ring

lemma mode_product (θ ψ : ℝ) (a b : ℂ) :
    (phase θ * a).re * (phase ψ * b).re =
      ((phase (θ - ψ) * (a * star b)).re + (phase (θ + ψ) * (a * b)).re) / 2 := by
  rw [real_product, phase_sub, phase_add]
  simp only [Complex.star_def, map_mul]
  congr 2 <;> congr 1 <;> ring



theorem realMode_dot {n : ℕ} (θ ψ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode ψ B =
      ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
        (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2 := by
  unfold realMode realPart dotProduct conjugate
  simp only [Pi.smul_apply, smul_eq_mul, mode_product, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]




theorem realMode_self_phase {n : ℕ} (θ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode θ B =
      (A ⬝ᵥ conjugate B).re / 2 + (phase (2 * θ) * (A ⬝ᵥ B)).re / 2 := by
  rw [realMode_dot, sub_self, phase_zero, one_mul]
  have h : θ + θ = 2 * θ := by ring
  rw [h, add_div]



lemma phase_comp_hasFDerivAt {φ : Base → ℝ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (τ : ℝ) :
    HasFDerivAt (fun q => phase (φ q / τ))
      (phase (φ p / τ) • ((I / (τ : ℂ)) • (Complex.ofRealCLM.comp (fderiv ℝ φ p)))) p := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (I / (τ : ℂ))).cexp
  have he (q : Base) : phase (φ q / τ) = Complex.exp (I / (τ : ℂ) * (φ q : ℂ)) := by
    simp only [phase, ofReal_div]
    congr 1
    ring
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, he] using h

lemma derivative_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (displacement τ φ Z) p v =
      realMode (φ p / τ) (derivativeAmplitude τ φ Z v p) := by
  have hc := ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)
  have hr := (realPartCLM n).hasFDerivAt.comp p hc
  simp only [Function.comp_def] at hr
  rw [show displacement τ φ Z = fun q => realPartCLM n (phase (φ q / τ) • Z q) from rfl,
    hr.fderiv]
  ext i
  simp only [realPartCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    Complex.reCLM_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    realMode, realPart, derivativeAmplitude]
  congr 1
  ring




theorem finite_phase_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (A B : ι → CVec n) :
    (∑ i, realMode (θ i) (A i)) ⬝ᵥ (∑ i, realMode (θ i) (B i)) =
      (∑ i, zeroPair (A i) (B i)) + (∑ i, doublePair (θ i) (A i) (B i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
  simp only [sum_dotProduct, dotProduct_sum]
  have hi (i : ι) :
      ∑ j, realMode (θ i) (A i) ⬝ᵥ realMode (θ j) (B j) =
        zeroPair (A i) (B i) + doublePair (θ i) (A i) (B i) +
          ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), realMode_self_phase]
    simp only [realMode_dot, crossPair, zeroPair, doublePair]
    ring
  rw [Finset.sum_comm]
  simp only [hi, Finset.sum_add_distrib]

lemma differentiableAt_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    DifferentiableAt ℝ (displacement τ φ Z) p :=
  ((realPartCLM n).hasFDerivAt.comp p
    ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)).differentiableAt



theorem quadraticMetric_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) {φ : ι → Base → ℝ} {Z : ι → Base → CVec n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p)
    (v w : Base) :
    quadraticMetric (sumDisplacement τ φ Z) v w p = meanMetric τ φ Z v w p +
      (∑ i, doublePair (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
        (derivativeAmplitude τ (φ i) (Z i) w p)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        crossPair (φ i p / τ) (φ j p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
          (derivativeAmplitude τ (φ j) (Z j) w p) := by
  have hd (v : Base) : fderiv ℝ (sumDisplacement τ φ Z) p v =
      ∑ i, realMode (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p) := by
    unfold sumDisplacement
    rw [fderiv_fun_sum (fun i _ => differentiableAt_displacement (hφ i) (hZ i) τ)]
    simp only [sum_apply, derivative_displacement (hφ _) (hZ _)]
  rw [quadraticMetric, hd v, hd w, finite_phase_expansion]
  rfl


end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude conjugate displacement
  doublePair crossPair realMode sumDisplacement quadraticMetric quadraticMetric_expansion
  differentiableAt_displacement)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)


lemma displacement_doubleTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ)
    (Z : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => 2 * φ q) (phaseDoubleTensor τ φ Z) p i =
      doublePair (φ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ φ Z (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseDoubleTensor, Pi.smul_apply, smul_eq_mul,
    ← mul_div_assoc, Complex.div_ofNat_re, doublePair]

lemma displacement_crossTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ)
    (Z W : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => φ q - ψ q) (phaseMinusTensor τ φ ψ Z W) p i +
      displacement τ (fun q => φ q + ψ q) (phasePlusTensor τ φ ψ Z W) p i =
      crossPair (φ p / τ) (ψ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ ψ W (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseMinusTensor, phasePlusTensor,
    Pi.smul_apply, smul_eq_mul, sub_div, add_div,
    ← mul_div_assoc, Complex.div_ofNat_re, crossPair]



lemma realMetric_sumDisplacement {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → Base → ℝ} {Z : ι → SmallModes.Field n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p) (τ : ℝ) :
    realMetricTensor (sumDisplacement τ φ Z) p = zeroPhaseSum τ φ Z p +
      nonzeroPhaseSum τ φ Z p := by
  ext k
  rw [realMetricTensor_apply]
  change quadraticMetric (sumDisplacement τ φ Z) (firstDirection k) (secondDirection k) p = _
  rw [quadraticMetric_expansion τ hφ hZ]
  simp only [zeroPhaseSum, nonzeroPhaseSum, phaseZeroTensor, QuadraticMean.meanMetric, Pi.add_apply, Finset.sum_apply,
    displacement_doubleTensor, displacement_crossTensor]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate displacement sumDisplacement)



lemma nonzeroPhaseSum_eq_quadraticFamily {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Field n) :
    nonzeroPhaseSum τ φ Z = fun p => ∑ l : QuadraticLabel ι,
      displacement τ (quadraticPhase φ l) (quadraticAmplitude τ φ Z l) p := by
  funext p
  unfold nonzeroPhaseSum
  rw [Fintype.sum_sum_type]
  dsimp only [quadraticPhase, quadraticAmplitude]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j : {j : ι // j ≠ i},
        (displacement τ (fun q => φ i q - φ j q) (phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)) p +
        displacement τ (fun q => φ i q + φ j q) (phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)) p) :=
      Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_bool]
      rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma quadraticPhase_smooth {ι : Type*} {φ : ι → Base → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∀ l : QuadraticLabel ι, ContDiff ℝ ∞ (quadraticPhase φ l) := by
  intro l
  rcases l with i | ⟨i, j, b⟩
  · exact contDiff_const.mul (hφ i)
  · cases b
    · exact (hφ i).add (hφ j)
    · exact (hφ i).sub (hφ j)




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CombinedQuadraticExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full quadratic expansion: the metric and polynomial remainders
share one finite family of doubled and mixed nonzero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma displacement_add (τ : ℝ) (φ : SmallModes.Base → ℝ) (A B : SmallModes.Tensor) :
    QuadraticMean.displacement τ φ (A + B) =
      QuadraticMean.displacement τ φ A + QuadraticMean.displacement τ φ B := by
  funext p i
  simp only [QuadraticMean.displacement, QuadraticMean.realMode, QuadraticMean.realPart,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Complex.add_re]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasRestore
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A displacement supported on an atlas weight's compact support is
restored exactly in that chart; the outer cutoff introduces no jet error. -/
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma mem_weight_support_of_plane (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (h : planeCoordinateIsometry (chart (i : M) p) ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) : p ∈ tsupport (A.weight i) := by
  obtain ⟨y,hy,he⟩ := h
  have hyEq : y = chart (i : M) p := planeCoordinateIsometry.injective he
  subst y
  obtain ⟨q,hq,hqp⟩ := hy
  have hqEq : q = p := (chart (i : M)).injOn (A.weight_support i hq) hp hqp
  rwa [hqEq] at hq

lemma restore_plane_on_source (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) p =
      f (planeCoordinateIsometry (chart (i : M) p)) := by
  rw [restore,indicator_of_mem hp]
  change A.outer i p • f (planeCoordinateIsometry (chart (i : M) p)) = _
  by_cases hz : f (planeCoordinateIsometry (chart (i : M) p)) = 0
  · rw [hz,smul_zero]
  · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hf (subset_tsupport f hz))),one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported restoration commutes with all local derivatives, including
its actual manifold differential, and preserves the original atlas support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_plane_tsupport (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    tsupport (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) ⊆
      tsupport (A.weight i) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · apply A.mem_weight_support_of_plane i hs
    apply hf
    apply subset_tsupport f
    intro hz
    apply hp
    rw [A.restore_plane_on_source i f hf hs,hz]
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_smul {n : ℕ} (θ a : ℝ) (Z : Fin n → ℂ) :
    realMode θ (a • Z) = a • realMode θ Z := by
  change realPartCLM n (QuadraticMean.phase θ • (a • Z)) =
    a • realPartCLM n (QuadraticMean.phase θ • Z)
  rw [smul_comm, map_smul]

lemma realMode_zero {n : ℕ} (θ : ℝ) : realMode θ (0 : Fin n → ℂ) = 0 := by
  change realPartCLM n (QuadraticMean.phase θ • (0 : Fin n → ℂ)) = 0
  rw [smul_zero,map_zero]

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_displacement {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin n → ℂ)
    (hZ : tsupport Z ⊆ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    restore (i : M) (A.outer i) (QuadraticMean.displacement τ φ Z ∘ planeCoordinateIsometry) =
      surfaceMode τ (restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry))
        (restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,surfaceMode,
      QuadraticMean.displacement]
    by_cases hz : Z (planeCoordinateIsometry (chart (i : M) p)) = 0
    · simp only [hz,realMode_zero,smul_zero]
    · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hZ (subset_tsupport Z hz))),
        one_smul,one_smul,one_smul]
  · simp only [restore,indicator_of_notMem hp,surfaceMode,realMode_zero]

lemma vectorChartRead_mode_on_support {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin n → ℂ) {x : JetPolynomial.Base}
    (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i (surfaceMode τ φ Z) x =
      realMode (A.vectorChartRead i φ x/τ) (A.vectorChartRead i Z x) := by
  rw [A.vectorChartRead_on_support i _ hx,A.vectorChartRead_on_support i _ hx,
    A.vectorChartRead_on_support i _ hx]
  rfl

lemma vectorChartRead_mode_jets {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      iteratedFDeriv ℝ m (fun y =>
        realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    isOpen_univ (subset_univ _) (A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).contDiffOn
    ((realMode_contDiff τ).comp ((A.vectorChartRead_smooth i hφ).prodMk
      (A.vectorChartRead_smooth i hZ))).contDiffOn
    (fun y hy => A.vectorChartRead_mode_on_support i τ φ Z (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma coordinateAmplitude_support {K : TopologicalSpace.Compacts JetPolynomial.Base}
    (Z : SupportedField (F := Fin 4 → ℂ) K) :
    tsupport (coordinateAmplitude Z) ⊆ (modeSupport K : Set SmallModes.Base) :=
  (pushSupported planeCoordinateIsometry K Z).tsupport_subset

variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

omit [CompactSpace M] in
lemma freeGlobalAmplitude_smooth
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) :
    ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (A.freeGlobalAmplitude d hρ δ q u i j) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff

theorem atlas_free_global_modes
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.atlasFreeOscillation d hρ δ q u = ∑ i : A.centers, ∑ j : Fin 3,
      surfaceMode τ (A.freeGlobalPhase d i j) (A.freeGlobalAmplitude d hρ δ q u i j) := by
  classical
  unfold atlasFreeOscillation vectorPlaneRestore
  apply Finset.sum_congr rfl
  intro i _
  have he : (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)) ∘ planeCoordinateIsometry =
      ∑ j : Fin 3, (QuadraticMean.displacement τ (coordinatePhase ((d i).phase j))
        (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) ∘
          planeCoordinateIsometry := by
    funext x
    simp only [chartedFreeSum,QuadraticMean.sumDisplacement,Function.comp_apply,Finset.sum_apply]
  rw [he]
  have hsum (f : Fin 3 → JetPolynomial.Base → RealModes.RVec 4) :
      restore (i : M) (A.outer i) (∑ j, f j) = ∑ j, restore (i : M) (A.outer i) (f j) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [restore,hp,Finset.smul_sum]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := (coordinateAmplitude_support
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))).trans (hK i j)
  simpa only [freeGlobalPhase,freeGlobalAmplitude,coordinatePhase,coordinateAmplitude,
    Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using A.restore_displacement i τ (coordinatePhase ((d i).phase j))
      (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))) hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasAmplitudeSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual global free amplitudes retain the original geometric supports. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma freeGlobalAmplitude_tsupport
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (i : A.centers) (j : Fin 3) :
    tsupport (A.freeGlobalAmplitude d hρ δ q u i j) ⊆ tsupport (A.weight i) := by
  have hs := (coordinateAmplitude_support
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))).trans (hK i j)
  have hh := A.restore_plane_tsupport i
    (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))) hs
  simpa only [freeGlobalAmplitude,coordinateAmplitude,Function.comp_def,
    LinearIsometryEquiv.symm_apply_apply] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalModeDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart differentials of global oscillatory modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  ext v : 1
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_mode_jets i τ hφ hZ 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorPlaneRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  let f := fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)
  have hf : ContDiff ℝ ∞ f := (realMode_contDiff τ).comp
    ((A.vectorChartRead_smooth i hφ).prodMk (A.vectorChartRead_smooth i hZ))
  change fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm) _ =
    fderiv ℝ (f ∘ planeCoordinateIsometry.symm) _
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).differentiable
      (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    fderiv_comp _ (hf.differentiable (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    LinearIsometryEquiv.symm_apply_apply,A.vectorChartRead_mode_fderiv i τ hφ hZ hy]

omit [CompactSpace M] in
lemma vectorPlaneRead_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (i : A.centers)
    (L : V →L[ℝ] W) (F : M → V) :
    A.vectorPlaneRead i (L ∘ F) = L ∘ A.vectorPlaneRead i F := by
  funext x
  change localize (i : M) (A.outer i) (L ∘ F) (planeCoordinateIsometry.symm x) =
    L (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x))
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [localize,hx,map_smul]

omit [CompactSpace M] in
lemma vectorPlaneRead_sum {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] (i : A.centers) (F : ι → M → V) :
    A.vectorPlaneRead i (∑ j, F j) = ∑ j, A.vectorPlaneRead i (F j) := by
  funext x
  simpa only [vectorPlaneRead,vectorChartRead,Function.comp_apply,Finset.sum_apply] using
    congrFun (localize_sum Finset.univ (i : M) (A.outer i) F) (planeCoordinateIsometry.symm x)

lemma vectorPlaneRead_modes_fderiv {ι : Type*} [Fintype ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      fderiv ℝ (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
  classical
  rw [A.vectorPlaneRead_sum]
  change fderiv ℝ (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) x =
    fderiv ℝ (fun y => ∑ j, QuadraticMean.displacement τ (A.vectorPlaneRead i (φ j))
      (A.vectorPlaneRead i (Z j)) y) x
  have he : (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) =
      fun y => ∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j)) y := by
    funext y
    exact Finset.sum_apply _ _ _
  have hloc (j : ι) : DifferentiableAt ℝ (QuadraticMean.displacement τ
      (A.vectorPlaneRead i (φ j)) (A.vectorPlaneRead i (Z j))) x :=
    ((realMode_contDiff τ).comp ((A.vectorPlaneRead_smooth i (hφ j)).prodMk
      (A.vectorPlaneRead_smooth i (hZ j)))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  rw [he,fderiv_fun_sum (fun j _ =>
    (A.vectorPlaneRead_smooth i (surfaceMode_smooth τ (hφ j) (hZ j))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x),
    fderiv_fun_sum (fun j _ => hloc j)]
  apply Finset.sum_congr rfl
  intro j _
  exact A.vectorPlaneRead_mode_fderiv i τ (hφ j) (hZ j) hx

lemma vectorPlaneRead_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x +
      RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x := by
  classical
  have hd := A.vectorPlaneRead_modes_fderiv i τ φ Z hφ hZ hx
  have he : RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.realMetricTensor (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
    ext k
    simp only [RealModes.realMetricTensor_apply, RealModes.realMetric,SmallModes.coordDeriv,hd]
  rw [he]
  exact RealModes.realMetric_sumDisplacement
    (fun j => (A.vectorPlaneRead_smooth i (hφ j)).differentiable (by simp) x)
    (fun j => (A.vectorPlaneRead_smooth i (hZ j)).differentiable (by simp) x) τ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalQuadraticModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global quadratic phase expansion, retaining all cross-chart interactions. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalModeMetricDualAdd
local instance globalModeMetricFiberNormed_r003fb4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance globalModeMetricFiberSpace_r003fb4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance globalModeMetricDualSmul_r003fb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance globalModeMetricSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalModeMetricSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem global_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    inducedTensor (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) +
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) := by
  classical
  let U : M → RealModes.RVec 4 := ∑ j, surfaceMode τ (φ j) (Z j)
  have hU : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ U := by
    have hh := ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [U,Finset.sum_apply]
  have he (i : A.centers) :
      spaceCoordinates ∘ A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) = A.vectorPlaneRead i U := by
    have hr : A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) =
        spaceCoordinates.symm ∘ A.vectorPlaneRead i U :=
      A.vectorPlaneRead_clm i spaceCoordinates.symm.toContinuousLinearMap U
    rw [hr]
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [← A.metric_from_chart_reads (spaceCoordinates.symm.contDiff.contMDiff.comp hU)]
  simp_rw [he]
  rw [← A.tensorPlaneRestore_add]
  congr 1
  funext i x
  by_cases hw : A.planeWeight i x = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.add_apply,zero_add]
  · have hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      (A.supportedPlaneWeight i).tsupport_subset (subset_tsupport (A.planeWeight i) hw)
    rw [A.vectorPlaneRead_modes_metric i τ φ Z hφ hZ hx,smul_add]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasQuadraticTargets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported quadratic targets for the global phase expansion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasQuadraticTargetsFiberNormed_r003fb4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticTargetsFiberSpace_r003fb4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasQuadraticTargetsDualAdd_r003fb4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsDualSmul_r003fb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance atlasQuadraticTargetsSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticTargetsSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma globalQuadraticPhase_smooth (φ : ι → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    ContDiff ℝ ∞ (A.globalQuadraticPhase φ k l) :=
  (RealModes.quadraticPhase_smooth (fun a => A.vectorPlaneRead_smooth k (hφ a)) l).comp
    planeCoordinateIsometry.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticOverlapSupports
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance overlapTargetsFiberNormed_r003fb4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_r003fb4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_r003fb4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r003fb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance overlapTargetsSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma quadraticOverlapCompact_subset (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    (A.quadraticOverlapCompact S hS k l : Set JetPolynomial.Base) ⊆ A.chartWeightCompact k := by
  rintro x ⟨p,hp,rfl⟩
  exact ⟨p,hp.1,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCombinedModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.combinedModesDualAdd
local instance combinedModesFiberNormed_r003fb4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance combinedModesFiberSpace_r003fb4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance combinedModesDualSmul_r003fb4_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance combinedModesSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance combinedModesSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem globalPolynomialQuadraticTarget_expansion {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
      QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
        (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        (RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x +
         ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
            (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
              (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x)) := by
  congr 1
  funext i x
  rw [RealModes.nonzeroPhaseSum_eq_quadraticFamily,← Finset.sum_add_distrib,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hp : coordinatePhase (A.globalQuadraticPhase φ i l) =
      RealModes.quadraticPhase (fun j => A.vectorPlaneRead i (φ j)) l := by
    funext y
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      planeCoordinateIsometry.apply_symm_apply]
  rw [hp]
  change QuadraticMean.realMode _ ((A.planeWeight i x)^2 • (_ + _)) = _
  rw [realMode_smul]
  change (A.planeWeight i x)^2 • QuadraticMean.displacement τ _
    (combinedQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x = _
  rw [combinedQuadraticCoefficient,displacement_add]
  rfl

theorem global_modes_full_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    let W := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
    inducedTensor W + A.atlasPolynomialQuadratic P ε F W =
      A.globalPolynomialQuadraticMean Q F ε τ φ Z +
      A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
        QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
          (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x) := by
  dsimp only
  rw [A.global_modes_metric τ φ Z hφ hZ,
    A.atlas_mode_polynomial_quadratic P Q hrep F hF ε τ φ Z hφ hZ,
    A.globalPolynomialQuadraticTarget_expansion Q hQ F hF ε τ φ Z hφ hZ]
  have hm : A.globalPolynomialQuadraticMean Q F ε τ φ Z =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) +
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
          (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x) := by
    rw [← A.tensorPlaneRestore_add]
    unfold globalPolynomialQuadraticMean
    congr 1
    funext i x
    exact smul_add _ _ _
  rw [hm]
  have ha (f g : A.centers → SmallModes.Base → Tensor) :
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • (f i x + g i x)) =
        A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • f i x) +
        A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • g i x) := by
    rw [← A.tensorPlaneRestore_add]
    congr 1
    funext i x
    exact smul_add _ _ _
  rw [ha]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialAmplitudeBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on every chart reading of the actual complex amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampReadPolynomialFiberSpace
local instance ampReadPolynomialDualAdd_r003fb4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampReadPolynomialDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampReadPolynomialFiberNormed
local instance ampReadPolynomialSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance ampReadPolynomialSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_polynomial_atlas_amplitude_reads
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → (∀ i, τ/s+ε/τ^tensorLoss (P i) ≤ 1) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      ∀ k i j, WeightedEstimates.WeightedBound univ s m (B*(δ*τ))
        (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u i j)) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B hB hb using fun (i : A.centers) (j : Fin 3) =>
    uniform_charted_seed_bound (R := R) (p i j) hρ q m (C' i)
  choose E hE he using fun k i : A.centers =>
    A.localize_outer_restore_bound (V := Fin 4 → ℂ) k i m
  let Q := fun a : A.centers × A.centers × Fin 3 => E a.1 a.2.1 * B a.2.1 a.2.2
  have hQ (a) : 0 ≤ Q a := mul_nonneg (hE a.1 a.2.1) (zero_le_one.trans (hB a.2.1 a.2.2))
  have htotal : 0 ≤ ∑ a, Q a := Finset.sum_nonneg (fun a _ => hQ a)
  refine ⟨1+∑ a, Q a,by linarith,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hsmall δ hδ u hu hball hbu k i j
  have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
    (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m) (Finset.mem_univ i)
  have hlocal := (hread i u s C hs hs1 hC hu (fun k => (hbu k).mono_order horder)).mono_const
    (le_max_right 1 (D i*C))
  have hseed := hb i j ((d i).data j) (hd i j) hτ hs hτs hs1 hε (hsmall i) δ hδ
    (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
    (A.tensorPlaneRead_smooth i hu) (hball i) hlocal
  have hout := he k i ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)) s
    (B i j*(δ*τ)) hs hs1 (mul_nonneg (zero_le_one.trans (hB i j)) (mul_nonneg hδ hτ.le))
    (((d i).data j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff hseed
  have hplane := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k (A.freeGlobalAmplitude_smooth d hρ δ q u i j)) hout
  change WeightedEstimates.WeightedBound univ s m (E k i*(B i j*(δ*τ)))
    (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u i j)) at hplane
  apply hplane.mono_const
  have ht : E k i*B i j ≤ ∑ a, Q a :=
    Finset.single_le_sum (fun a _ => hQ a) (Finset.mem_univ (k,i,j))
  calc
    E k i*(B i j*(δ*τ)) = (E k i*B i j)*(δ*τ) := by ring
    _ ≤ (1+∑ a, Q a)*(δ*τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hδ hτ.le)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialQuadraticCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform cancellation of the actual quadratic oscillations at a nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialQuadDualAdd
local instance inputPolynomialQuadFiberNormed_r003fb4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPolynomialQuadFiberSpace_r003fb4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance inputPolynomialQuadDualSmul_r003fb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialQuadSectionNormed
local instance inputPolynomialQuadSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem input_global_polynomial_quadratic_cancellation_all_profiles
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (φ i))
    (S : ι → Set M) (hS : ∀ i, IsClosed (S i))
    (hImm : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) x))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P a : ℕ → ℝ),
      (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ a m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ δ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 < δ →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (Z : ι → M → Fin 4 → ℂ) (_hZ : ∀ i, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z i)),
        (∀ i, tsupport (Z i) ⊆ S i) →
        (∀ k i m, WeightedEstimates.WeightedBound univ s (m+1) (a m*(δ*τ)) (A.vectorPlaneRead k (Z i))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2*η^(q+1)*Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            (inducedTensor (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b))+
              A.atlasPolynomialQuadratic Pol ε G
                (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b)) -
              A.globalPolynomialQuadraticMean Q G ε τ φ Z))) := by
  classical
  obtain ⟨ρ,hρ,hall⟩ := A.atlas_polynomial_input_cancellation_all_profiles Pol Q hQ hlin F hF
    (A.globalQuadraticPhase φ) (A.globalQuadraticPhase_smooth φ hφ)
    (A.quadraticOverlapCompact S hS)
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    hImm hgood U hU KU hUK
    (fun k l => (A.quadraticOverlapCompact_subset S hS k l).trans (hweight k))
  refine ⟨ρ,hρ,?_⟩
  intro P a hP ha q
  obtain ⟨T,hT,ht⟩ := A.atlas_polynomial_target_profiles Q hQ φ hφ U hU KU hUK hweight P a hP ha
  obtain ⟨C,D,hC,hD,hcancel⟩ := hall P hP q
  let N := fun k => PolynomialSolveData.inputOrder (P := Q k) q
  let Cv := fun m => ∑ k : A.centers, ∑ l, C k l m*T k (N k m)
  let Ct := fun m => ∑ k : A.centers, ∑ l, D k l m*T k (N k m)
  have hCv (m) : 0 ≤ Cv m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hC k l m) (hT k (N k m))
  have hCt (m) : 0 ≤ Ct m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hD k l m) (hT k (N k m))
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ δ ε η s hτ hs hτs hs1 hδ hε hε1 hη hη1 hsmall hp Z hZ hSZ hz
  let target := A.globalPolynomialQuadraticTargetRestricted Q hQ G hG ε τ φ Z hφ hZ S hS hSZ
  have htarget (k l m) : supportedWeightedSeminorm
      (modeSupport (A.quadraticOverlapCompact S hS k l)) s m (target k l) ≤ T k m*δ^2 := by
    apply supportedSeminorm_le_of_weightedBound hs (mul_nonneg (hT k m) (sq_nonneg δ))
    exact ht G hG Z hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1
      (fun i => (hsmall i).trans hη1) hp (fun i b m => (hz i b m).mono_order (Nat.le_succ m)) k m l
  obtain ⟨W,hW,hsize,hres⟩ := hcancel G hG B hB hBρ hb τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hp target
  have hsum (E : (k : A.centers) → RealModes.QuadraticLabel ι → ℝ)
      (hE : ∀ k l, 0 ≤ E k l) (m : ℕ) :
      (∑ k : A.centers, ∑ l, E k l*supportedWeightedSeminorm
        (modeSupport (A.quadraticOverlapCompact S hS k l)) s (N k m) (target k l)) ≤
      δ^2*∑ k : A.centers, ∑ l, E k l*T k (N k m) := by
    calc
      _ ≤ ∑ k : A.centers, ∑ l, E k l*(T k (N k m)*δ^2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (htarget k l (N k m)) (hE k l)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    exact (hsize m k).mono_const (hsum (fun k l => C k l m) (fun k l => hC k l m) m)
  · intro m k
    have hh := (hres m k).mono_const
      (mul_le_mul_of_nonneg_left (hsum (fun k l => D k l m) (fun k l => hD k l m) m)
        (pow_nonneg hη _))
    have he : η^(q+1)*(δ^2*Ct m) = δ^2*η^(q+1)*Ct m := by ring
    rw [he] at hh
    have hsplit : inducedTensor (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b))+
        A.atlasPolynomialQuadratic Pol ε G (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b)) -
        A.globalPolynomialQuadraticMean Q G ε τ φ Z =
        A.tensorPlaneRestore (fun k x => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ k l))
            (target k l) x) := by
      rw [A.global_modes_full_quadratic Pol Q hQ hquad G hG ε τ φ Z hφ hZ]
      exact add_sub_cancel_left _ _
    rw [hsplit]
    exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialFreeCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct a forced correction uniformly for nearby maps from their input norms. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialFreeQuadraticDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialFreeQuadraticDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialFreeQuadraticFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPolynomialFreeQuadraticFiberSpace
local instance inputPolynomialFreeQuadraticSectionNormed_r003fb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPolynomialFreeQuadraticSectionSpace_r003fb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem input_polynomial_free_correction_fixed_phase_oai
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : A.centers × Fin 3 → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          φ k l)) x))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (q : ℕ),
    ∃ Cv Ct : ℕ → ℝ,
      (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
      ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 < δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2 * Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2 * η^(q+1) * Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            (inducedTensor (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) +
              A.atlasPolynomialQuadratic Pol ε G (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) -
              A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))))) := by
  classical
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_global_polynomial_quadratic_cancellation_all_profiles Pol Q hQ hquad hlin F hF φ hφ
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
    (fun a => isClosed_tsupport (A.weight a.1)) hImm hgood U hU KU hUK hweight
  refine ⟨ρ₀,hρ₀,?_⟩
  intro p ρ R hρ r reference D hD C hC q
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := Q i) q (m+1))
  choose a ha hamp using fun m =>
    A.uniform_polynomial_atlas_amplitude_reads p hρ r reference q (m+1) (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := hall D a hD
    (fun m => zero_le_one.trans (ha m)) q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb ε τ s d hfit hphase hdG hτ hs hτs hs1 hε hε1 η hη hη1 hsmall hd hK δ hδ u hu hball hbu
  let Z := fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2
  have hZ (a) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a) :=
    A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2
  have hsp (a) : tsupport (Z a) ⊆ tsupport (A.weight a.1) :=
    A.freeGlobalAmplitude_tsupport d hρ δ q u hK a.1 a.2
  have hreads (k a₀ m) : WeightedEstimates.WeightedBound univ s (m+1)
      (a m*(δ*τ)) (A.vectorPlaneRead k (Z a₀)) :=
    hamp m d hfit hτ hs hτs hs1 hε (fun i => (hsmall i).trans hη1) δ hδ.le u hu hball (hbu (N m)) k a₀.1 a₀.2
  obtain ⟨W,hW,hsize,hres⟩ := hcorr G hG B hB hBρ hb τ δ ε η s hτ hs hτs hs1 hδ hε hε1 hη hη1 hsmall hd Z hZ hsp hreads
  have hph (i : A.centers) (j : Fin 3) : A.freeGlobalPhase d i j = φ (i,j) := hphase (i,j)
  have hmode : (∑ a : A.centers × Fin 3, surfaceMode τ (φ a) (Z a)) =
      A.atlasFreeOscillation d hρ δ q u := by
    rw [Fintype.sum_prod_type]
    simpa only [Z,hph] using (A.atlas_free_global_modes d hρ δ q u hK).symm
  have hmean : A.globalPolynomialQuadraticMean Q G ε τ φ Z =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) := by
    have hh := A.atlas_global_polynomial_mean Pol Q hquad G hG d hdG hρ δ q u hK
    simpa only [hphase,Z] using hh
  refine ⟨W,hW,hsize,?_⟩
  intro m
  simpa only [hmode,hmean] using hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase_oai.{u_1}
