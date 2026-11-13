-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:53.183899+00:00
-- url     : https://prove2.me/submissions/fef76850-bc00-4306-bc33-f2669a951caa

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_nonempty
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exact_metric_with_property
import Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_choose_three_avoiding

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

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



lemma finite_bad_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0) :
    Set.Finite {t : ℝ | secondQuadratic B (-t, 1) = 0} := by
  classical
  have hex : ∃ j i, B j i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hB (funext fun j => funext fun i => hn j i)
  obtain ⟨j, i, hji⟩ := hex
  let p : ℝ[X] := C (B 0 i) * X ^ 2 - C (2 * B 1 i) * X + C (B 2 i)
  have hp : p ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : ℝ[X] => P.coeff 0) hz
    have h1 := congrArg (fun P : ℝ[X] => P.coeff 1) hz
    have h2 := congrArg (fun P : ℝ[X] => P.coeff 2) hz
    simp [p, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow] at h0 h1 h2
    fin_cases j <;> simp_all
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  have hi := congrFun ht i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    neg_sq, one_pow, mul_one, one_mul] at hi
  change p.eval t = 0
  simp only [p, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  nlinarith [hi]

lemma finite_affine_preimage {T : Set ℝ} (hT : T.Finite) {a b : ℝ} (ha : a ≠ 0) :
    ( (fun t : ℝ => a * t + b) ⁻¹' T).Finite := by
  apply hT.preimage
  intro x hx y hy he
  exact mul_left_cancel₀ ha (by linarith)



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PositiveBasis
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

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean
open Set


lemma basisCoefficient_apply (t u v : ℝ) (H : PhaseMean.Tensor) :
    basisCoefficient t u v H = (H 2 - (u + v) * H 1 + u * v * H 0) / ((t - u) * (t - v)) := by
  simp only [basisCoefficient, smul_apply, add_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma covectorSquare_smul (w : ℝ) (ξ : Base) :
    covectorSquare (w • ξ) = w ^ 2 • covectorSquare ξ := by
  ext i
  fin_cases i <;> simp [covectorSquare, smul_eq_mul] <;> ring



lemma three_slope_decomposition {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≠ t₁)
    (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) (H : PhaseMean.Tensor) :
    basisCoefficient t₀ t₁ t₂ H • covectorSquare (1, t₀) +
      basisCoefficient t₁ t₀ t₂ H • covectorSquare (1, t₁) +
      basisCoefficient t₂ t₀ t₁ H • covectorSquare (1, t₂) = H := by
  have h10 : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₁.symm
  have h20 : t₂ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₂.symm
  have h21 : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h01 : t₀ - t₁ ≠ 0 := sub_ne_zero.mpr h₀₁
  have h02 : t₀ - t₂ ≠ 0 := sub_ne_zero.mpr h₀₂
  have h12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h₁₂
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, basisCoefficient_apply, covectorSquare] <;>
    field_simp [h10, h20, h21, h01, h02, h12] <;> ring



lemma normalized_numerators_positive {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (h₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (h₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < 1 + x₁*x₂ ∧ 1 + x₀*x₂ < 0 ∧ 0 < 1 + x₀*x₁ := by
  have hx₂ : 0 < x₂ := by linarith [h₂.1]
  have hx₀ : 0 < -x₀ := by linarith [h₀.2]
  have hp₁ := mul_pos (show 0 < x₁ + 1/4 by linarith [h₁.1]) hx₂
  have hp₂ := mul_pos (show 0 < -x₀ - 2 by linarith [h₀.2]) hx₂
  have hp₃ := mul_pos (show 0 < 1/4 - x₁ by linarith [h₁.2]) hx₀
  constructor
  · nlinarith [h₂.2]
  constructor
  · nlinarith [h₂.1]
  · nlinarith [h₀.1]

lemma positive_center_parameters {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    (hdet : 0 < H 0 * H 2 - (H 1) ^ 2) :
    ∃ β r : ℝ, 0 < r ∧ H 1 = H 0 * β ∧ H 2 = H 0 * (β ^ 2 + r ^ 2) := by
  let β := H 1 / H 0
  let D := H 2 / H 0 - β ^ 2
  have hD : 0 < D := by
    have he : D = (H 0 * H 2 - (H 1) ^ 2) / (H 0) ^ 2 := by
      dsimp [D, β]
      field_simp
    rw [he]
    exact div_pos hdet (sq_pos_of_pos h₀)
  refine ⟨β, Real.sqrt D, Real.sqrt_pos.2 hD, ?_, ?_⟩
  · dsimp [β]
    field_simp
  · rw [Real.sq_sqrt hD.le]
    dsimp [D]
    field_simp
    ring

lemma shifted_numerator (H : PhaseMean.Tensor) {β r : ℝ}
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2)) (u v : ℝ) :
    H 2 - ((β + r*u) + (β + r*v)) * H 1 + (β + r*u)*(β + r*v)*H 0 =
      H 0 * r ^ 2 * (1 + u*v) := by
  rw [h₁, h₂]
  ring

lemma shifted_basis_positive {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    {β r x₀ x₁ x₂ : ℝ} (hr : 0 < r)
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2))
    (hx₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (hx₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (hx₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < basisCoefficient (β+r*x₀) (β+r*x₁) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₁) (β+r*x₀) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₂) (β+r*x₀) (β+r*x₁) H := by
  have hnum := normalized_numerators_positive hx₀ hx₁ hx₂
  have h01 : β+r*x₀ < β+r*x₁ := by nlinarith [hx₀.2, hx₁.1]
  have h12 : β+r*x₁ < β+r*x₂ := by nlinarith [hx₁.2, hx₂.1]
  have hp : 0 < H 0 * r ^ 2 := mul_pos h₀ (sq_pos_of_pos hr)
  simp only [basisCoefficient_apply, shifted_numerator H h₁ h₂]
  refine ⟨div_pos (mul_pos hp hnum.1) (mul_pos_of_neg_of_neg (sub_neg.mpr h01)
    (sub_neg.mpr (h01.trans h12))), ?_, ?_⟩
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hnum.2.1)
      (mul_neg_of_pos_of_neg (sub_pos.mpr h01) (sub_neg.mpr h12))
  · exact div_pos (mul_pos hp hnum.2.2)
      (mul_pos (sub_pos.mpr (h01.trans h12)) (sub_pos.mpr h12))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_weighted {n : ℕ} {B : Fin 3 → RVec n} {t w : ℝ}
    (hw : w ≠ 0) (ht : secondQuadratic B (-t, 1) ≠ 0) : Good B (w, w*t) := by
  constructor
  · intro hz
    exact hw (congrArg Prod.fst hz)
  · have he : (-(w*t), w) = w • (-t, (1 : ℝ)) := by
      ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) ht



theorem positive_good_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H : PhaseMean.Tensor} (h₀ : 0 < H 0) (hdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ t₀ t₁ t₂ : ℝ, t₀ < t₁ ∧ t₁ < t₂ ∧
      0 < basisCoefficient t₀ t₁ t₂ H ∧ 0 < basisCoefficient t₁ t₀ t₂ H ∧
      0 < basisCoefficient t₂ t₀ t₁ H ∧
      secondQuadratic B (-t₀, 1) ≠ 0 ∧ secondQuadratic B (-t₁, 1) ≠ 0 ∧
      secondQuadratic B (-t₂, 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 2*t₁)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₁-t₀), 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 4*t₂)/5), 1) ≠ 0 ∧
      secondQuadratic B (-((4*t₂-t₀)/3), 1) ≠ 0 ∧
      secondQuadratic B (-((t₁ + 2*t₂)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₂-t₁), 1) ≠ 0 := by
  obtain ⟨β, r, hr, h₁, h₂⟩ := positive_center_parameters h₀ hdet
  let T : Set ℝ := (fun x : ℝ => r*x + β) ⁻¹' {t : ℝ | secondQuadratic B (-t, 1) = 0}
  have hT : T.Finite := finite_affine_preimage (finite_bad_slopes hB) hr.ne'
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hn₀, hn₁, hn₂, hn₃, hn₄, hn₅, hn₆, hn₇, hn₈⟩ :=
    choose_three_avoiding hT (show (-3 : ℝ) < -2 by norm_num)
      (show (-(1/4) : ℝ) < 1/4 by norm_num) (show (2 : ℝ) < 3 by norm_num)
  have hn : ∀ {x : ℝ}, x ∉ T → secondQuadratic B (-(β+r*x), 1) ≠ 0 := by
    intro x hx
    simpa only [T, mem_preimage, mem_ofPred_eq, add_comm] using hx
  have hpos := shifted_basis_positive h₀ hr h₁ h₂ hx₀ hx₁ hx₂
  refine ⟨β+r*x₀, β+r*x₁, β+r*x₂, ?_, ?_, hpos.1, hpos.2.1, hpos.2.2,
    hn hn₀, hn hn₁, hn hn₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hx₀.2, hx₁.1]
  · nlinarith [hx₁.2, hx₂.1]
  · convert hn hn₃ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₄ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₅ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₆ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₇ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₈ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_neg {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} (h : Good B ξ) : Good B (-ξ) := by
  constructor
  · exact neg_ne_zero.mpr h.1
  · have he : (-(-ξ).2, (-ξ).1) = (-1 : ℝ) • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    simpa using h.2



theorem positive_good_phase_data {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H₀ : PhaseMean.Tensor} (h₀ : 0 < H₀ 0) (hdet : 0 < H₀ 0 * H₀ 2 - (H₀ 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ),
      (∀ H, ∑ i : Fin 3, Q i H • covectorSquare (ξ i) = H) ∧
      (∀ i, 0 < Q i H₀) ∧ (∀ i, Good B (ξ i)) ∧
      (∀ i j, i ≠ j → Good B (ξ i + ξ j) ∧ Good B (ξ i - ξ j)) := by
  obtain ⟨t₀, t₁, t₂, h01, h12, hp₀, hp₁, hp₂, hg₀, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆, hg₇, hg₈⟩ :=
    positive_good_slopes hB h₀ hdet
  let ξ : Fin 3 → Base := ![(1, t₀), (2, 2*t₁), (4, 4*t₂)]
  let Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ :=
    ![basisCoefficient t₀ t₁ t₂, (1/4 : ℝ) • basisCoefficient t₁ t₀ t₂,
      (1/16 : ℝ) • basisCoefficient t₂ t₀ t₁]
  have hξ₁ : ξ 1 = (2 : ℝ) • (1, t₁) := by ext <;> simp [ξ]
  have hξ₂ : ξ 2 = (4 : ℝ) • (1, t₂) := by ext <;> simp [ξ]
  have h03 : Good B (ξ 0 + ξ 1) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₃ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h04 : Good B (ξ 1 - ξ 0) := by
    convert good_weighted (B := B) (w := 1) (by norm_num) hg₄ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ]
    ring
  have h05 : Good B (ξ 0 + ξ 2) := by
    convert good_weighted (B := B) (w := 5) (by norm_num) hg₅ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h06 : Good B (ξ 2 - ξ 0) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₆ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h07 : Good B (ξ 1 + ξ 2) := by
    convert good_weighted (B := B) (w := 6) (by norm_num) hg₇ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h08 : Good B (ξ 2 - ξ 1) := by
    convert good_weighted (B := B) (w := 2) (by norm_num) hg₈ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  refine ⟨ξ, Q, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [Fin.sum_univ_three, hξ₁, hξ₂, covectorSquare_smul, covectorSquare_smul]
    convert three_slope_decomposition h01.ne (h01.trans h12).ne h12.ne H using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    simp [Q, ξ, Pi.smul_apply, smul_smul, smul_eq_mul]
    ring
  · intro i
    fin_cases i <;> simp [Q]
    · exact hp₀
    · positivity
    · positivity
  · intro i
    fin_cases i
    · simpa [ξ] using good_weighted (w := 1) (by norm_num) hg₀
    · simpa [ξ] using good_weighted (w := 2) (by norm_num) hg₁
    · simpa [ξ] using good_weighted (w := 4) (by norm_num) hg₂
  · intro i j hij
    have h40 := good_neg h04
    have h60 := good_neg h06
    have h80 := good_neg h08
    simp only [neg_sub] at h40 h60 h80
    fin_cases i <;> fin_cases j <;> simp_all [add_comm]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (w p : Base) :
    coordDeriv w (F ∘ φ) p = fderiv ℝ F (φ p) (coordDeriv w φ p) := by
  simp only [coordDeriv,fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ φ)) p =
      coordDeriv (fderiv ℝ φ p v) (coordDeriv (fderiv ℝ φ p w) F) (φ p) +
      fderiv ℝ F (φ p) (coordDeriv v (coordDeriv w φ) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := ((hDF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (φ p)).hasFDerivAt.comp p
    ((hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt
  have hD2 := ((contDiffAt_coordDeriv (p := p) hφ.contDiffAt w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ F ∘ φ) q (coordDeriv w φ q)) = coordDeriv w (F ∘ φ) := by
    funext q
    exact (coordDeriv_comp_smooth hF hφ w q).symm
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  rw [real_second_coordDeriv ((hDF.differentiable (by simp)) (φ p))]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm] using heval

lemma realNormalPart_fderiv {F : RField 4} (p v : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (fderiv ℝ F p v) = 0 := by
  change realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v F p) = 0
  conv_lhs => arg 3; rw [coordDeriv_eq_basis F v p]
  have hl := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hl.map_add,hl.map_smul,hl.map_smul,realNormalPart_self_left _ _ hD,
    realNormalPart_self_right _ _ hD,smul_zero,smul_zero,add_zero]



lemma realSecondForm_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ,
    second_coordDeriv_comp_smooth hF hφ]
  change realNormalPart (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) _ = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    realNormalPart_change_basis _ _ _ _ _ _ _ hD hdet]
  rw [(realNormalPart_linear _ _).map_add,realNormalPart_fderiv _ _ hD,add_zero]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

lemma rotated_pullCovector (A : Base →L[ℝ] Base) (ξ : Base) :
    A (-(pullCovector A ξ).2,(pullCovector A ξ).1) = coordDet A • (-ξ.2,ξ.1) := by
  rw [linear_apply_basis]
  ext <;> simp [pullCovector,coordDet,Prod.smul_mk] <;> ring

lemma phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1) =
      (coordDet (fderiv ℝ φ p))^2 •
        secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1) := by
  rw [← realSecondForm_quadratic (hF.comp hφ),realSecondForm_comp_smooth hF hφ _ _ _ hD hdet,
    rotated_pullCovector,realSecondForm_quadratic hF,secondQuadratic_smul]

lemma norm_phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ =
      (coordDet (fderiv ℝ φ p))^2 *
        ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by
  rw [phase_length_comp_smooth hF hφ ξ p hD hdet,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_realSecondForm_le {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    ‖realSecondForm F v w p‖ ≤ 4*‖realSecondTensor F p‖*‖v‖*‖w‖ := by
  have h11 : |v.1*w.1| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_fst_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h22 : |v.2*w.2| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_snd_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h12 : |v.1*w.2+v.2*w.1| ≤ 2*‖v‖*‖w‖ := by
    have ha : |v.1*w.2| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_snd_le w)
        (abs_nonneg _) (norm_nonneg _)
    have hb : |v.2*w.1| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_fst_le w)
        (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (v.1*w.2) (v.2*w.1)]
  rw [realSecondForm_bilinear hF]
  calc
    _ ≤ (‖(v.1*w.1) • realSecondTensor F p 0‖+
        ‖(v.1*w.2+v.2*w.1) • realSecondTensor F p 1‖)+
        ‖(v.2*w.2) • realSecondTensor F p 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖*‖w‖*‖realSecondTensor F p‖+
        (2*‖v‖*‖w‖)*‖realSecondTensor F p‖)+‖v‖*‖w‖*‖realSecondTensor F p‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm _ 0
      · exact norm_le_pi_norm _ 1
      · exact norm_le_pi_norm _ 2
    _ = _ := by ring

lemma norm_realSecondTensor_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤
      4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  have hbound (v : Base) (hv : ‖v‖ = 1) : ‖fderiv ℝ φ p v‖ ≤ ‖fderiv ℝ φ p‖ := by
    simpa only [hv,mul_one] using (fderiv ℝ φ p).le_opNorm v
  have hx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have hb (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖realSecondForm (F ∘ φ) v w p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
    rw [realSecondForm_comp_smooth hF hφ _ _ _ hD hdet]
    calc
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p v‖*‖fderiv ℝ φ p w‖ :=
        norm_realSecondForm_le hF _ _ _
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖*‖fderiv ℝ φ p‖ := by
        gcongr
        · exact hbound v hv
        · exact hbound w hw
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact hb dx dx hx hx
  · exact hb dx dy hx hy
  · exact hb dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma continuous_coordDet : Continuous coordDet := by
  unfold coordDet
  fun_prop

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



theorem compact_chart_jacobian_bounds {φ ψ : Base → Base} {U V K : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ p ∈ K, d ≤ |coordDet (fderiv ℝ φ p)| ∧ ‖fderiv ℝ φ p‖ ≤ C := by
  have hD : ContinuousOn (fderiv ℝ φ) K :=
    (hφ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hd : ContinuousOn (fun p => |coordDet (fderiv ℝ φ p)|) K :=
    (continuous_coordDet.comp_continuousOn hD).abs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hD
  by_cases hn : K.Nonempty
  · obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hn hd
    refine ⟨|coordDet (fderiv ℝ φ p)|,|C|+1,abs_pos.mpr ?_,by positivity,?_⟩
    · exact coordDet_fderiv_ne_zero_of_local_inverse hU hV hφ hψ hmap hinv (hKU hp)
    · intro q hq
      exact ⟨hm hq,(hC q hq).trans (by linarith [le_abs_self C])⟩
  · exact ⟨1,1,zero_lt_one,zero_lt_one,fun p hp => False.elim (hn ⟨p,hp⟩)⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem smooth_extension_near {F : M → V} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ F U) {p : M} (hp : p ∈ U) :
    ∃ G : M → V, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ U ∧ G =ᶠ[𝓝 p] F := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hU.mem_nhds hp)
  let G : M → V := fun q => b q • F q
  have hs : tsupport G ⊆ tsupport b := tsupport_smul_subset_left _ _
  refine ⟨G, ?_, ?_, hs.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro q hq
    exact b.contMDiffAt.smul ((hF q (hb (hs hq))).contMDiffAt
      (hU.mem_nhds (hb (hs hq))))
  · exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hs
  · filter_upwards [b.eventuallyEq_one] with q hq
    simp only [G, hq, Pi.one_apply, one_smul]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma coordDeriv_eventuallyEq {n : ℕ} {F G : RField n} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v : Base) : coordDeriv v F =ᶠ[𝓝 p] coordDeriv v G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v) hq

lemma realSecondForm_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    (fun q => realSecondForm F v w q) =ᶠ[𝓝 p] (fun q => realSecondForm G v w q) := by
  filter_upwards [coordDeriv_eventuallyEq h dx, coordDeriv_eventuallyEq h dy,
    coordDeriv_eventuallyEq (coordDeriv_eventuallyEq h w) v] with q hx hy hxy
  simp only [realSecondForm, hx, hy, hxy]

lemma realSecondTensor_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) : realSecondTensor F =ᶠ[𝓝 p] realSecondTensor G := by
  filter_upwards [realSecondForm_eventuallyEq h dx dx, realSecondForm_eventuallyEq h dx dy,
    realSecondForm_eventuallyEq h dy dy] with q hxx hxy hyy
  ext i
  fin_cases i <;> simp [realSecondTensor, hxx, hxy, hyy]




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPatches
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma chartCoordinates_center (p : M) : chartCoordinates p p = coordinateCenter p := by
  simp [chartCoordinates,coordinateCenter,planeModel]




end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateChart_apply (p q : M) : coordinateChart p q = chartCoordinates p q := rfl

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



theorem coordinateTransition_compact_bounds (q p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ (coordinateTransition q p).source) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ x ∈ K, d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)| ∧
        ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ C := by
  let e := coordinateTransition q p
  exact compact_chart_jacobian_bounds e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun x hx => e.left_inv hx) hK hKs

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LengthMargins
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma good_of_direction_length_pos {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    (h : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖) : Good B ξ := by
  refine ⟨?_, norm_pos_iff.mp h⟩
  intro hξ
  simp [hξ,secondQuadratic] at h





end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma norm_pullCovector_le (A : Base →L[ℝ] Base) (ξ : Base) :
    ‖pullCovector A ξ‖ ≤ 2*‖A‖*‖ξ‖ := by
  have hd : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have he : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have bound (v : Base) (hv : ‖v‖ = 1) : |ξ.1*(A v).1+ξ.2*(A v).2| ≤ 2*‖A‖*‖ξ‖ := by
    have hA : ‖A v‖ ≤ ‖A‖ := by simpa only [hv,mul_one] using A.le_opNorm v
    have h1 : |ξ.1*(A v).1| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le ξ)
        ((show |(A v).1| ≤ ‖A v‖ by simpa using norm_fst_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    have h2 : |ξ.2*(A v).2| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le ξ)
        ((show |(A v).2| ≤ ‖A v‖ by simpa using norm_snd_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (ξ.1*(A v).1) (ξ.2*(A v).2)]
  change max ‖ξ.1*(A dx).1+ξ.2*(A dx).2‖ ‖ξ.1*(A dy).1+ξ.2*(A dy).2‖ ≤ _
  simpa only [Real.norm_eq_abs,max_le_iff] using And.intro (bound dx hd) (bound dy he)




theorem quantitative_chart_phase_margin {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  have hdet0 : coordDet (fderiv ℝ φ p) ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  have hsq : d^2 ≤ (coordDet (fderiv ℝ φ p))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hd.le hdet 2
  have hbc : ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*C ^ 2 := by
    apply (norm_realSecondTensor_comp_smooth hF hφ p hD hdet0).trans
    gcongr
  have hlength := norm_phase_length_comp_smooth hF hφ ξ p hD hdet0
  have hbound : d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    calc
      _ ≤ d^2*ε/(4*C ^ 2)*(4*‖realSecondTensor F (φ p)‖*C ^ 2) := by gcongr
      _ = d^2*(ε*‖realSecondTensor F (φ p)‖) := by field_simp
      _ ≤ d^2*‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hpos : 0 < ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    exact mul_pos (sq_pos_of_ne_zero hdet0) ((mul_pos hε (norm_pos_iff.mpr hB)).trans_le hmargin)
  refine ⟨(norm_pullCovector_le _ _).trans ?_,hbound,good_of_direction_length_pos _ _ hpos,?_⟩
  · gcongr
  · intro hz
    simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,norm_zero] at hpos
    exact lt_irrefl 0 hpos

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter




theorem quantitative_chart_phase_margin_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (ξ : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hTG := (realSecondTensor_eventuallyEq heG).eq_of_nhds
  have hTF := (realSecondTensor_eventuallyEq hecomp).eq_of_nhds
  have h := quantitative_chart_phase_margin hG.contDiff hΦ.contDiff ξ p hd hC hε hDG
    (by simpa only [eD] using hdet) (by simpa only [eD] using hA)
    (by simpa only [ep,hTG] using hB) (by simpa only [ep,hTG] using hmargin)
  simpa only [eD,hTF] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q (coordinateTransition q p x) = coordinateMap F p x := by
  change spaceCoordinates (F (coordinateInverse q (coordinateTransition q p x))) =
    spaceCoordinates (F (coordinateInverse p x))
  rw [← coordinateChart_symm_apply, ← coordinateChart_symm_apply]
  change spaceCoordinates (F ((coordinateChart q).symm
    (coordinateChart q ((coordinateChart p).symm x)))) = _
  have hqx : (coordinateChart p).symm x ∈ (coordinateChart q).source := hx.2
  rw [(coordinateChart q).left_inv hqx]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition_eventuallyEq (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q ∘ coordinateTransition q p =ᶠ[𝓝 x] coordinateMap F p := by
  filter_upwards [(coordinateTransition q p).open_source.mem_nhds hx] with y hy
  exact coordinateMap_transition F q p hy




theorem actual_chart_phase_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) (ξ : SmallModes.Base)
    {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
      (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) x‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
        (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
          (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) x)
      (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
    realSecondTensor (coordinateMap F p) x ≠ 0 := by
  have hy : coordinateTransition q p x ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hx.2
  have ht := quantitative_chart_phase_margin_on
    (coordinateTransition q p).open_source (coordinateDomain_open q)
    (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx hy ξ hd hL hε hD hdet hA hB hmargin
  have he := (realSecondTensor_eventuallyEq
    (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds
  simpa only [he] using ht

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes Set Metric

lemma contDiff_gram_pair : ContDiff ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) := by
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma contDiffAt_normalColumns {p : TangentPair} (hp : NormalFrame.gramDet p.1 p.2 ≠ 0) :
    ContDiffAt ℝ ∞ normalColumns p := by
  apply contDiffAt_pi.mpr
  intro i
  unfold normalColumns realNormalPart
  have hd : ContDiffAt ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) p :=
    contDiff_gram_pair.contDiffAt
  have hX : ContDiffAt ℝ ∞ (fun p : TangentPair => p.1) p := contDiff_fst.contDiffAt
  have hY : ContDiffAt ℝ ∞ (fun p : TangentPair => p.2) p := contDiff_snd.contDiffAt
  apply (contDiffAt_const.sub ?_).sub ?_
  · apply ContDiffAt.fun_smul _ hX
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop
  · apply ContDiffAt.fun_smul _ hY
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop

lemma realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    realNormalPart p.1 p.2 W = ∑ i : Fin 4, W i • normalColumns p i := by
  have hlin := realNormalPart_linear p.1 p.2
  have he : W = ∑ i : Fin 4, W i • (Pi.single i 1 : RVec 4) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => arg 3; rw [he]
  change (hlin.mk' _) (∑ i : Fin 4, W i • Pi.single i 1) = _
  simp only [map_sum,map_smul,IsLinearMap.mk'_apply,normalColumns]

lemma norm_realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W‖ ≤ 4 * ‖normalColumns p‖ * ‖W‖ := by
  rw [realNormalPart_columns]
  calc
    _ ≤ ∑ i : Fin 4, ‖W i • normalColumns p i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i) (norm_le_pi_norm (normalColumns p) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp <;> ring

lemma norm_realNormalPart_change (p q : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 W‖ ≤
      4 * ‖normalColumns p - normalColumns q‖ * ‖W‖ := by
  rw [realNormalPart_columns,realNormalPart_columns,← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i : Fin 4, W i • (normalColumns p i-normalColumns q i)‖ := by simp [smul_sub]
    _ ≤ ∑ i : Fin 4, ‖W i • (normalColumns p i-normalColumns q i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p-normalColumns q‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i)
        (norm_le_pi_norm (normalColumns p-normalColumns q) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp <;> ring



theorem compact_normal_projection_bounds (R c : ℝ) (hc : 0 < c) :
    ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧ ∀ (p q : TangentPair),
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
      ‖q‖ ≤ R → c ≤ NormalFrame.gramDet q.1 q.2 → ∀ W Z : RVec 4,
      ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 Z‖ ≤
        L * ‖p-q‖ * ‖W‖ + D * ‖W-Z‖ := by
  let K : Set TangentPair := closedBall 0 R ∩ {p | c ≤ NormalFrame.gramDet p.1 p.2}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const contDiff_gram_pair.continuous)
  have hne (p : TangentPair) (hp : p ∈ K) : NormalFrame.gramDet p.1 p.2 ≠ 0 :=
    (hc.trans_le hp.2).ne'
  have hloc : LocallyLipschitzOn K normalColumns := by
    intro p hp
    obtain ⟨L,U,hU,hL⟩ := ((contDiffAt_normalColumns (hne p hp)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).exists_lipschitzOnWith
    exact ⟨L,U,Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hU) (fun _ h => h),hL⟩
  obtain ⟨L,hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hcont : ContinuousOn normalColumns K := fun p hp =>
    (contDiffAt_normalColumns (hne p hp)).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨4*(L:ℝ),4*max D 0,by positivity,by positivity,?_⟩
  intro p q hp hpD hq hqD W Z
  have hpK : p ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hp,hpD⟩
  have hqK : q ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,hqD⟩
  have hcols : ‖normalColumns p-normalColumns q‖ ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul p hpK q hqK
  have hdecomp : realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z =
      (realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W) +
        realNormalPart q.1 q.2 (W-Z) := by
    rw [(realNormalPart_linear q.1 q.2).map_sub]
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W‖ +
        ‖realNormalPart q.1 q.2 (W-Z)‖ := norm_add_le _ _
    _ ≤ 4*‖normalColumns p-normalColumns q‖*‖W‖ + 4*‖normalColumns q‖*‖W-Z‖ :=
      add_le_add (norm_realNormalPart_change p q W) (norm_realNormalPart_columns q (W-Z))
    _ ≤ (4*(L:ℝ))*‖p-q‖*‖W‖ + (4*max D 0)*‖W-Z‖ := by
      have hcq := (hD q hqK).trans (le_max_left D 0)
      nlinarith [mul_le_mul_of_nonneg_right hcols (show 0 ≤ 4*‖W‖ by positivity),
        mul_le_mul_of_nonneg_right hcq (show 0 ≤ 4*‖W-Z‖ by positivity)]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes Set Metric



theorem uniform_gram_neighborhood (R c : ℝ) (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ p q : TangentPair,
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ η →
      ‖q‖ ≤ R+1 ∧ c/2 ≤ NormalFrame.gramDet q.1 q.2 := by
  obtain ⟨L,hL⟩ := contDiff_gram_pair.contDiffOn.exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) (convex_closedBall (0 : TangentPair) (R+1))
    (isCompact_closedBall _ _)
  let η : ℝ := min 1 (c/(2*((L:ℝ)+1)))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨η,hη,min_le_left _ _,fun p q hp hpD hpq => ?_⟩
  have hq : ‖q‖ ≤ R+1 := by
    calc ‖q‖ ≤ ‖p‖+‖q-p‖ := norm_le_insert' q p
         _ = ‖p‖+‖p-q‖ := by rw [norm_sub_rev q p]
         _ ≤ R+1 := add_le_add hp (hpq.trans (min_le_left _ _))
  have hpK : p ∈ closedBall 0 (R+1) := by
    rw [mem_closedBall,dist_zero_right]
    linarith
  have hqK : q ∈ closedBall 0 (R+1) := by simpa only [mem_closedBall,dist_zero_right] using hq
  have hl : |NormalFrame.gramDet p.1 p.2-NormalFrame.gramDet q.1 q.2| ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hL.dist_le_mul p hpK q hqK
  have hηc : (L:ℝ)*η ≤ c/2 := by
    have hmin : η ≤ c/(2*((L:ℝ)+1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hmin
    nlinarith [hη.le]
  refine ⟨hq,?_⟩
  have hdiff := (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hpq L.coe_nonneg))
  linarith



theorem uniform_normal_projection_stability (R c : ℝ) (hc : 0 < c) :
    ∃ η L D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ D ∧
      ∀ p q : TangentPair, ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
        ‖p-q‖ ≤ η → ∀ W Z : RVec 4,
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤
          L*‖p-q‖*‖W‖+D*‖W-Z‖ := by
  obtain ⟨η,hη,hη1,hηb⟩ := uniform_gram_neighborhood R c hc
  obtain ⟨L,D,hL,hD,hb⟩ := compact_normal_projection_bounds (R+1) (c/2) (half_pos hc)
  refine ⟨η,L,D,hη,hη1,hL,hD,fun p q hp hpD hpq W Z => ?_⟩
  obtain ⟨hq,hqD⟩ := hηb p q hp hpD hpq
  exact hb p q (by linarith) (by linarith) hq hqD W Z




theorem normal_projection_z4_stability (R c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (p q : TangentPair) (W Z : RVec 4), ‖p‖ ≤ R →
        c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ z^4 →
        ‖W‖ ≤ A/z^2 → ‖W-Z‖ ≤ z^4 →
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤ C*z^2 := by
  obtain ⟨η,L,D,hη,_,hL,hD,hb⟩ := uniform_normal_projection_stability R c hc
  refine ⟨η,L*A+D,hη,by positivity,fun z hz hz1 hzη p q W Z hp hpD hpq hW hWZ => ?_⟩
  have hh := hb p q hp hpD (hpq.trans hzη) W Z
  have hz42 : z^4 ≤ z^2 := pow_le_pow_of_le_one hz.le hz1 (by norm_num : 2 ≤ 4)
  calc
    _ ≤ L*‖p-q‖*‖W‖+D*‖W-Z‖ := hh
    _ ≤ L*z^4*(A/z^2)+D*z^4 := by gcongr
    _ ≤ L*z^4*(A/z^2)+D*z^2 := by gcongr
    _ = (L*A+D)*z^2 := by field_simp [hz.ne']

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set

lemma realSecondTensor_eq_projection (F : RField 4) (p : Base) (i : Fin 3) :
    realSecondTensor F p i =
      realNormalPart (firstJetPair F p).1 (firstJetPair F p).2 (secondJetTriple F p i) := by
  fin_cases i <;> rfl





theorem secondTensor_z4_stability (R c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (F G : RField 4) (p : Base), ‖firstJetPair F p‖ ≤ R →
      c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 →
      ‖firstJetPair F p-firstJetPair G p‖ ≤ z^4 →
      ‖secondJetTriple F p‖ ≤ A/z^2 →
      ‖secondJetTriple F p-secondJetTriple G p‖ ≤ z^4 →
      ‖realSecondTensor F p-realSecondTensor G p‖ ≤ C*z^2 := by
  obtain ⟨η,C,hη,hC,hb⟩ := normal_projection_z4_stability R c hc A hA
  refine ⟨η,C,hη,hC,fun z hz hz1 hzη F G p hp hpD hpq hH hHG => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply,realSecondTensor_eq_projection]
  exact hb z hz hz1 hzη _ _ _ _ hp hpD hpq
    ((norm_le_pi_norm _ i).trans hH) ((norm_le_pi_norm _ i).trans hHG)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DirectionStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set

lemma WeightedBound.convex_variation {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {s A : ℝ} {f : E → G} (hs : 0 < s)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s 1 A f)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x-f y‖ ≤ (A/s)*‖x-y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (hf.differentiableOn (by simp)) _ hconv hy hx
  intro p hp
  have hh := hb.deriv_le hs (show 1 ≤ 1 by rfl) hp
  simpa only [norm_iteratedFDerivWithin_one (𝕜 := ℝ) f (hU.uniqueDiffOn p hp),pow_one] using hh

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates Set

lemma weighted_coordinate_second_jet {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hb : WeightedBound U z 3 A F) {v w : Base} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    WeightedBound U z 1 (A/z^2) (coordDeriv v (coordDeriv w F)) := by
  have h1 : WeightedBound U z 2 (A/z) (coordDeriv w F) := by
    have hh := hb.directional hU hz hF w
    simp only [hw,one_mul] at hh
    exact hh.congr (fun p hp => rfl)
  have h2 := h1.directional hU hz (contDiffOn_coordDeriv_vector hU hF w) v
  simp only [hv,one_mul,div_div,← pow_two] at h2
  exact h2.congr (fun p hp => rfl)

lemma coordinate_jets_variation {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hA : 0 ≤ A) (hb : WeightedBound U z 3 A F) {x y : Base} (hx : x ∈ U) (hy : y ∈ U) :
    ‖firstJetPair F x-firstJetPair F y‖ ≤ (A/z^2)*‖x-y‖ ∧
    ‖secondJetTriple F x‖ ≤ A/z^2 ∧
    ‖secondJetTriple F x-secondJetTriple F y‖ ≤ (A/z^3)*‖x-y‖ := by
  have hdx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hdy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have h1 (v : Base) (hv : ‖v‖ = 1) :
      ‖coordDeriv v F x-coordDeriv v F y‖ ≤ (A/z^2)*‖x-y‖ := by
    have hh : WeightedBound U z 1 (A/z) (coordDeriv v F) := by
      have hh := (hb.mono_order (by omega : 2 ≤ 3)).directional hU hz hF v
      simp only [hv,one_mul] at hh
      exact hh.congr (fun p hp => rfl)
    simpa only [div_div,pow_two] using hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU hF v) hx hy
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) x‖ ≤ A/z^2 ∧
      ‖coordDeriv v (coordDeriv w F) x-coordDeriv v (coordDeriv w F) y‖ ≤ (A/z^3)*‖x-y‖ := by
    have hh := weighted_coordinate_second_jet hU hF hz hb hv hw
    refine ⟨hh.norm_le hx,?_⟩
    have hvw := hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU (contDiffOn_coordDeriv_vector hU hF w) v) hx hy
    simpa only [div_div,← pow_succ] using hvw
  refine ⟨?_,?_,?_⟩
  · change max ‖coordDeriv dx F x-coordDeriv dx F y‖ ‖coordDeriv dy F x-coordDeriv dy F y‖ ≤ _
    exact max_le (h1 dx hdx) (h1 dy hdy)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).1
    · exact (h2 dx dy hdx hdy).1
    · exact (h2 dy dy hdy hdy).1
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).2
    · exact (h2 dx dy hdx hdy).2
    · exact (h2 dy dy hdy hdy).2




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

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
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

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GoodSmoothingAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

omit [IsManifold planeModel ∞ M] in
lemma planeCoordinateIsometry_chart (p x : M) :
    planeCoordinateIsometry (chart p x) = planeCoordinates (chartAt Plane p x) := rfl

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_chart_symm (F : M → Space) (p : M) (x : SmallModes.Base) :
    coordinateMap F p x = spaceCoordinates (F ((chart p).symm (planeCoordinateIsometry.symm x))) := rfl

variable [T2Space M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [T2Space M] [CompactSpace M] in
/-- Locally constant outer cutoffs identify the entire coordinate germ on
the original weight support, and hence every derivative used by the phases. -/
lemma vectorPlaneRead_eventually_coordinateMap
    (F : M → Space) (i : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))] coordinateMap F (i : M) := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (i : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support i hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (i : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (i : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (i : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer i (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (i : M)).target :=
    ((chart (i : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (i : M)).map_source hpS)
  filter_upwards [ho,htarget] with z hz htgt
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm z)) = _
  rw [localize,indicator_of_mem htgt]
  change spaceCoordinates (A.outer i (inv z)^2 • F (inv z)) = _
  rw [hz,one_pow,one_smul]
  exact (coordinateMap_chart_symm F (i : M) z).symm

end SmoothingAtlas

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasImmersionGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local good-phase geometry in any covering chart gives the intrinsic
immersion and nonzero second-form hypotheses for the next primitive. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma nonzero_secondForm_of_chart_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    (hp : p ∈ (coordinateChart q).source)
    (hI : Function.Injective (fderiv ℝ (coordinateMap F q) (coordinateChart q p)))
    {ξ : SmallModes.Base}
    (hg : Good (realSecondTensor (coordinateMap F q) (coordinateChart q p)) ξ) :
    ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0 := by
  let B := realSecondTensor (coordinateMap F q) (coordinateChart q p)
  have hB : B ≠ 0 := by
    intro h
    exact hg.2 (by simp only [B,h,secondQuadratic,Pi.zero_apply,smul_zero,add_zero])
  have hbn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hqn : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖ := norm_pos_iff.mpr hg.2
  let ε := ‖secondQuadratic B (-ξ.2,ξ.1)‖/‖B‖
  have hε : 0 < ε := div_pos hqn hbn
  have hm : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ :=
    le_of_eq (div_mul_cancel₀ _ hbn.ne')
  have hpp : p ∈ (coordinateChart p).source := by
    rw [coordinateChart_source]
    exact mem_chart_source Plane p
  have hx : coordinateCenter p ∈ (coordinateTransition q p).source := by
    have hh := coordinateTransition_mem_chart q p hpp hp
    simpa only [coordinateChart_apply,chartCoordinates_center] using hh
  obtain ⟨d,C,hd,hC,hbound⟩ := coordinateTransition_compact_bounds q p
    (isCompact_singleton (x := coordinateCenter p)) (singleton_subset_iff.mpr hx)
  have hb := hbound (coordinateCenter p) (mem_singleton _)
  have he : coordinateTransition q p (coordinateCenter p) = coordinateChart q p := by
    have hh := coordinateTransition_apply_chart q p hpp
    simpa only [coordinateChart_apply,chartCoordinates_center] using hh
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ (coordinateMap F q) (coordinateChart q p)) hI
  have ht := actual_chart_phase_margin hF q p hx ξ hd hC hε
    (by simpa only [he,coordDeriv] using hD) hb.1 hb.2
    (by simpa only [he] using hB) (by simpa only [he] using hm)
  have hn : realSecondTensor (coordinateMap F p) (coordinateCenter p) ≠ 0 := ht.2.2.2
  by_contra! hzero
  apply hn
  funext i
  fin_cases i
  · exact hzero dx dx
  · exact hzero dx dy
  · exact hzero dy dy

namespace FiniteOrderSmoothing.SmoothingAtlas
open JetPolynomial
variable [CompactSpace M] (A : SmoothingAtlas M)

lemma immersion_of_planeRead_injective (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ tsupport (A.weight i))
    (hI : Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  have hread : Function.Injective (fderiv ℝ (A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) := by
    have he := (spaceCoordinates.hasFDerivAt.comp (planeCoordinateIsometry (chart (i : M) p))
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp)
        (planeCoordinateIsometry (chart (i : M) p))).hasFDerivAt).fderiv
    rw [he] at hI
    intro v w hv
    apply hI
    exact congrArg spaceCoordinates hv
  change Function.Injective (surfaceDifferential F p)
  rw [A.vectorPlaneRead_differential i hF hp]
  exact hread.comp (planeCoordinateIsometry.injective.comp
    ((chart_mdifferentiable (i : M)).mfderiv_injective (A.weight_support i hp)))

theorem geometry_of_chartwise_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hgeom : ∀ p : M, ∃ i : A.centers, p ∈ tsupport (A.weight i) ∧
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ∧
      ∃ ξ : SmallModes.Base,
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (planeCoordinateIsometry (chart (i : M) p))) ξ) :
    (∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) ∧
    (∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) := by
  constructor
  · intro p
    obtain ⟨i,hp,hi,_⟩ := hgeom p
    exact A.immersion_of_planeRead_injective i hF hp hi
  · intro p
    obtain ⟨i,hp,hi,ξ,hg⟩ := hgeom p
    have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
    have hpoint : coordinateChart (i : M) p = planeCoordinateIsometry (chart (i : M) p) := by
      rw [planeCoordinateIsometry_chart]
      rfl
    have hI : Function.Injective (fderiv ℝ (coordinateMap F (i : M))
        (coordinateChart (i : M) p)) := by
      rw [hpoint,← he.fderiv_eq]
      exact hi
    have hgood : Good (realSecondTensor (coordinateMap F (i : M))
        (coordinateChart (i : M) p)) ξ := by
      rw [hpoint,← (realSecondTensor_eventuallyEq he).eq_of_nhds]
      exact hg
    exact nonzero_secondForm_of_chart_good hF (i : M) p
      (by simpa [coordinateChart_source,chart] using A.weight_support i hp) hI hgood

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed finite smoothing norms control any other fixed finite atlas.
This allows later curve charts to stay fixed as the isometric immersion changes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

omit [CompactSpace M] in
lemma cross_localize_restore (i : B.centers) (j : A.centers) (h : Base → V) :
    localize (i : M) (B.weight i) (restore (j : M) (A.outer j) h) =
      fun x => localize (i : M) (B.weight i) (A.outer j) x •
        h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma cross_localize_restore_bound (i : B.centers) (j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h →
      WeightedEstimates.WeightedBound univ s m C h →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (B.weight i) (restore (j : M) (A.outer j) h)) := by
  let K := (chart (i : M)) '' (tsupport (B.weight i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => B.weight_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (B.weight_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (B.weight_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (B.weight_smooth i) (B.weight_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (B.weight_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro h s C hs hs1 hC hh hb
  rw [A.cross_localize_restore B]
  exact hd h s C hs hs1 hC hh hb

theorem weightedBound_change_atlas (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F → B.WeightedBound s m (D*C) F := by
  classical
  choose D hD hd using fun (i : B.centers) (j : A.centers) =>
    A.cross_localize_restore_bound (V := V) B i j m
  refine ⟨∑ i : B.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)),?_⟩
  intro F s C hs hs1 hC hF hb i
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j*C)
    (fun j => localize (i : M) (B.weight i)
      (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)))
    (fun j _ => (localize_smooth (i : M) (B.weight_smooth i) (B.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn)
    (fun j _ => hd i j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j))
  have he : localize (i : M) (B.weight i) F = fun x => ∑ j : A.centers,
      localize (i : M) (B.weight i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseC2Stability
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The good-phase stability radius uses only the ordinary C2 difference. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

lemma coordDeriv_sub_smooth {F G : RField 4} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (v : Base) :
    coordDeriv v (F-G) = coordDeriv v F - coordDeriv v G := by
  funext p
  simp only [coordDeriv, fderiv_sub (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    (hG.differentiable (by simp) p), sub_apply, Pi.sub_apply]

lemma realTwoJet_sub {F G : RField 4} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    realTwoJet (F-G) = realTwoJet F - realTwoJet G := by
  have hx := coordDeriv_sub_smooth hF hG dx
  have hy := coordDeriv_sub_smooth hF hG dy
  have hxx := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dx)
    (contDiff_real_coordDeriv hG dx) dx
  have hxy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dx
  have hyy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dy
  funext p i
  fin_cases i <;> simp [realTwoJet,hx,hy,hxx,hxy,hyy]

lemma norm_realTwoJet_le {F : RField 4} (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 2 C F) (p : Base) : ‖realTwoJet F p‖ ≤ C := by
  have h1 (v : Base) (hv : ‖v‖ = 1) : WeightedBound univ 1 1 C (coordDeriv v F) := by
    change WeightedBound univ 1 1 C (fun x => fderiv ℝ F x v)
    simpa only [hv,div_one,one_mul] using hb.directional isOpen_univ zero_lt_one hF.contDiffOn v
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) p‖ ≤ C := by
    have hd := (h1 w hw).directional isOpen_univ zero_lt_one
      (contDiff_real_coordDeriv hF w).contDiffOn v
    simpa only [coordDeriv,hv,div_one,one_mul] using hd.norm_le (mem_univ p)
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact (h1 dx hx).norm_le (mem_univ p)
  · exact (h1 dy hy).norm_le (mem_univ p)
  · exact h2 dx dx hx hx
  · exact h2 dx dy hx hy
  · exact h2 dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReadJetBallBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial C2 radius preserves the anchored phase family. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
lemma first_second_jet_difference_bound {F G : RField 4}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 2 C (F-G)) (p : Base) :
    ‖firstJetPair F p-firstJetPair G p‖ ≤ C ∧
      ‖secondJetTriple F p-secondJetTriple G p‖ ≤ C := by
  have hp := norm_realTwoJet_le (hF.sub hG) hC hb p
  change ‖realTwoJet (F-G) p‖ ≤ C at hp
  rw [realTwoJet_sub hF hG] at hp
  have hc (i : Fin 5) : ‖realTwoJet F p i-realTwoJet G p i‖ ≤ C :=
    (norm_le_pi_norm (realTwoJet F p-realTwoJet G p) i).trans hp
  constructor
  · change max ‖coordDeriv dx F p-coordDeriv dx G p‖
      ‖coordDeriv dy F p-coordDeriv dy G p‖ ≤ C
    exact max_le (hc 0) (hc 1)
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    fin_cases i
    · exact hc 2
    · exact hc 3
    · exact hc 4
end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem readJetBall_radius : ∃ D : ℝ, 1 ≤ D ∧
    ∀ z : ℝ, ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 2 (z^4/D) (G-F) → A.ReadJetBall z F G := by
  classical
  choose E hE hread using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let D : ℝ := 1+∑ i : A.centers, L*E i
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg hL (hE i))
    change 1 ≤ 1+∑ i : A.centers, L*E i
    linarith
  have hED (i : A.centers) : L*E i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg hL (hE i)) (Finset.mem_univ i)
    change L*E i ≤ 1+∑ i : A.centers, L*E i
    linarith
  refine ⟨D,hD,?_⟩
  intro z F G hF hG hb
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hρ : 0 ≤ z^4/D := div_nonneg (by positivity : 0 ≤ z^4) hD0.le
  refine ⟨hG,?_⟩
  intro i x _hx
  have hr := (hread i (G-F) 1 (z^4/D) zero_lt_one le_rfl hρ (hG.sub hF) hb).linear
    uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have heq : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i G)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    funext y
    change spaceCoordinates (localize (i : M) (A.outer i) (G-F)
      (planeCoordinateIsometry.symm y)) = _
    simp only [Function.comp_apply,Pi.sub_apply,vectorPlaneRead,vectorChartRead,localize]
    by_cases hy : planeCoordinateIsometry.symm y ∈ (chart (i : M)).target
    · simp only [indicator_of_mem hy,smul_sub,map_sub]
    · simp only [indicator_of_notMem hy,map_zero,sub_self]
  change WeightedEstimates.WeightedBound univ 1 2 (L*(E i*(z^4/D)))
    (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hr
  rw [heq] at hr
  have hsmall : L*(E i*(z^4/D)) ≤ z^4 := by
    calc
      _ = (L*E i)*(z^4/D) := by ring
      _ ≤ D*(z^4/D) := mul_le_mul_of_nonneg_right (hED i) hρ
      _ = z^4 := by field_simp
  have hj := first_second_jet_difference_bound
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG))
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF))
    (by positivity : 0 ≤ z^4) (hr.mono_const hsmall) x
  simpa only [norm_sub_rev] using hj

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformFastNormalMargin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero second-form margin persists at the polynomial C2 radius. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseGeometry

theorem uniform_fast_normal_margin (R c A b : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ s : ℝ, 0 < s → s ≤ η →
    ∀ F G : RField 4, ContDiff ℝ ∞ F → WeightedBound univ s 3 A F → ∀ x : Base,
      ‖firstJetPair F x‖ ≤ R →
      c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      b ≤ ‖realSecondTensor F x‖ →
      ‖firstJetPair F x-firstJetPair G x‖ ≤ s^4 →
      ‖secondJetTriple F x-secondJetTriple G x‖ ≤ s^4 →
      Function.Injective (fderiv ℝ G x) ∧ b/2 ≤ ‖realSecondTensor G x‖ := by
  obtain ⟨ηn,C,hηn,hC,hn⟩ := secondTensor_z4_stability R c A hc hA
  obtain ⟨ηg,hηg,_,hg⟩ := uniform_gram_neighborhood R c hc
  let η := min 1 (min ηn (min ηg (b/(2*(C+1)))))
  have hη : 0 < η := lt_min zero_lt_one (lt_min hηn (lt_min hηg (by positivity)))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro s hs hsη F G hF hFb x hR hcF hbF hdiff hsecond
  have hs1 : s ≤ 1 := hsη.trans (min_le_left _ _)
  have hs4 : s^4 ≤ s := by simpa only [pow_one] using pow_le_pow_of_le_one hs.le hs1 (by norm_num : 1 ≤ 4)
  have hs2 : s^2 ≤ s := by simpa only [pow_one] using pow_le_pow_of_le_one hs.le hs1 (by norm_num : 1 ≤ 2)
  have hsn : s^4 ≤ ηn := hs4.trans (hsη.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsg : s^4 ≤ ηg := hs4.trans (hsη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsb : s ≤ b/(2*(C+1)) := hsη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : C*s^2 ≤ b/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp hsb
    nlinarith [mul_le_mul_of_nonneg_left hs2 hC]
  have hnormjet := (coordinate_jets_variation isOpen_univ (convex_univ : Convex ℝ (univ : Set Base))
    hF.contDiffOn hs hA hFb (mem_univ x) (mem_univ x)).2.1
  have hbound := hn s hs hs1 hsn F G x hR hcF hdiff hnormjet hsecond
  have hgram := (hg _ _ hR hcF (hdiff.trans hsg)).2
  refine ⟨injective_of_gramDet_ne_zero _ ((half_pos hc).trans_le hgram).ne',?_⟩
  have hh := norm_sub_norm_le (realSecondTensor F x) (realSecondTensor G x)
  linarith [hbound.trans hsmall]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasExactGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact limits retain the geometric hypotheses needed for the next primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance crossExactGeometricFastFiberNormed_r5b9d62_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance crossExactGeometricFastFiberSpace_r5b9d62_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance crossExactGeometricFastDualAdd_r5b9d62_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossExactGeometricFastDualSmul_r5b9d62_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance crossExactGeometricFastSectionNormed_r5b9d62_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossExactGeometricFastSectionSpace_r5b9d62_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem exact_geometric_metric_with_property_in_atlas_oai [T2Space M] (B₀ : SmoothingAtlas M) (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c b V₀ : ℝ) (hc : 0 < c) (hb : 0 < b) (hV₀ : 0 ≤ V₀)
    (property : ℝ → (M → Space) → Prop)
    (hfamily : A.GeometricFastFamilyWithProperty g R c b V₀ property)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧
      IsSmoothIsometricImmersion M g G ∧ Nonempty (MetricGoodPhaseData g G) ∧
      B₀.WeightedBound 1 2 (z^8) (G-F) := by
  obtain ⟨B,hB,hall⟩ := A.exact_metric_with_property g houter R c b V₀ hc hb hV₀ property hfamily
  obtain ⟨η,hη,hη1,hnormal⟩ := uniform_fast_normal_margin R c B b hc (zero_le_one.trans hB) hb
  obtain ⟨D,hD,hball⟩ := A.readJetBall_radius
  obtain ⟨E,hE,hchange⟩ := A.weightedBound_change_atlas (V := Space) B₀ 2
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hK : 0 < D+E+1 := by positivity
  obtain ⟨z,hz,hzcap,hz1,F,G,hF,hproperty,hG,hclose,hread,hgeom⟩ :=
    hall (min η ζ) (lt_min hη hζ) (D+E+1) hK
  have hzη := hzcap.trans_le (min_le_left _ _)
  have hzζ := hzcap.trans_le (min_le_right _ _)
  have hcloseA : A.WeightedBound 1 2 (z^8/D) (G-F) := fun i =>
    (hclose i).mono_const (div_le_div_of_nonneg_left (pow_nonneg hz.le _) hDpos (by linarith))
  have hclose' : A.WeightedBound 1 2 ((z^2)^4/D) (G-F) := by
    convert hcloseA using 1 <;> first | rfl | ring
  have hjet := hball (z^2) F G hF hG.1 hclose'
  have hsη : z^2 ≤ η := (show z^2 ≤ z from by
    simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by norm_num : 1 ≤ 2)).trans hzη.le
  have hlocal := fun i x hx => hnormal (z^2) (pow_pos hz 2) hsη
    (spaceCoordinates ∘ A.vectorPlaneRead i F) (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) (hread i) x
    (hgeom i x hx).1 (hgeom i x hx).2.1 (hgeom i x hx).2.2
    (hjet.2 i x hx).1 (hjet.2 i x hx).2
  have hgeometry := A.geometry_of_chartwise_good hG.1 houter (by
    intro p
    obtain ⟨i,hi⟩ : ∃ i : A.centers, A.weight i p ≠ 0 := by
      by_contra! hz
      have hh := A.partition p
      simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
      norm_num at hh
    have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ hi
    have hx : planeCoordinateIsometry (chart (i : M) p) ∈
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
    obtain ⟨hI,hN⟩ := hlocal i _ hx
    have hNZ : realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p)) ≠ 0 :=
      norm_pos_iff.mp ((half_pos hb).trans_le hN)
    obtain ⟨ξ,Q,_,_,hgood,_⟩ := PhaseGeometry.positive_good_phase_data hNZ
      (H₀ := ![(1:ℝ),0,1]) (by simp) (by simp)
    exact ⟨i,hp,hI,ξ 0,hgood 0⟩)
  refine ⟨z,hz,hzζ,hz1,F,G,hF,hproperty,hG,
    MetricGoodPhaseData.nonempty g hG.1 hgeometry.1 hgeometry.2,?_⟩
  have hbclose := hchange (G-F) 1 (z^8/(D+E+1)) zero_lt_one le_rfl
    (div_nonneg (pow_nonneg hz.le _) hK.le) (hG.1.sub hF) hclose
  intro i
  apply (hbclose i).mono_const
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hK).mpr
  nlinarith [pow_nonneg hz.le 8]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas_oai.{u_1}
