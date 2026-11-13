-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:14.662515+00:00
-- url     : https://prove2.me/submissions/4b6fd514-5952-43a4-b21a-1083c298b3d2

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_forced_increment
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_mean_residual
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_trial
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_grid_mean_data

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridIncrementEnvelope
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial envelopes for the full free/forced grid increment. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes

lemma gridInteractionCount_nonneg {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ gridInteractionCount n := by unfold gridInteractionCount; positivity

lemma gridInteractionCount_mono {n N : ℝ} (hn : 0 ≤ n) (h : n ≤ N) :
    gridInteractionCount n ≤ gridInteractionCount N := by
  unfold gridInteractionCount
  gcongr

lemma gridInteractionCount_polynomial {H : ℝ → ℝ} (hH : HasPolynomialBound H) :
    HasPolynomialBound (fun x => gridInteractionCount (H x)) :=
  hH.add ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hH.pow 2))

lemma gridIncrementSize_polynomial (α β : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (hα : ∀ m, HasPolynomialBound (α m)) (hβ : ∀ m, HasPolynomialBound (β m))
    (hH : HasPolynomialBound H) (m : ℕ) :
    HasPolynomialBound (gridIncrementSize α β H m) :=
  ((hα m).mul hH).add ((hβ m).mul (gridInteractionCount_polynomial hH))

lemma gridIncrementError_polynomial (α β γ ζ T : ℕ → ℝ → ℝ) (D : ℕ → ℝ) (H : ℝ → ℝ)
    (hα : ∀ m, HasPolynomialBound (α m)) (hβ : ∀ m, HasPolynomialBound (β m))
    (hγ : ∀ m, HasPolynomialBound (γ m)) (hζ : ∀ m, HasPolynomialBound (ζ m))
    (hT : ∀ m, HasPolynomialBound (T m)) (hD : ∀ m, 0 ≤ D m)
    (hH : HasPolynomialBound H) (m : ℕ) :
    HasPolynomialBound (gridIncrementError α β γ ζ T D H m) := by
  have hN := gridInteractionCount_polynomial hH
  exact ((((hζ m).mul hH).add ((hγ m).mul hN)).add (hT m)).add
    ((polynomialBound_const (hD m)).mul
      ((((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul ((hα (m+1)).mul hH)).mul
        ((hβ (m+1)).mul hN)).add (((hβ (m+1)).mul hN).pow 2)))

lemma gridIncrementSize_bound {a b n N δ τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) :
    (a*n+b*gridInteractionCount n)*(δ*τ) ≤
      (a*N+b*gridInteractionCount N)*(δ*τ) := by
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hδ hτ)
  exact add_le_add (mul_le_mul_of_nonneg_left hnN ha)
    (mul_le_mul_of_nonneg_left (gridInteractionCount_mono hn hnN) hb)

lemma gridIncrementError_bound {a b c d t D n N δ τ η : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η) :
    η*(d*n*(δ*τ)+c*gridInteractionCount n*δ^2)+δ^2*t*η+
      D*(2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2)*(δ^3/τ) ≤
    (d*N+c*gridInteractionCount N+t+
      D*(2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2)) *
      (δ*η+δ^3/τ) := by
  have hN : 0 ≤ N := hn.trans hnN
  have hnq := gridInteractionCount_nonneg hn
  have hNq := gridInteractionCount_nonneg hN
  have hq := gridInteractionCount_mono hn hnN
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have hdt : δ*τ ≤ δ := mul_le_of_le_one_right hδ hτ1
  have hdsq : δ^2 ≤ δ := by nlinarith
  have hdn : d*n ≤ d*N := mul_le_mul_of_nonneg_left hnN hd
  have hcq : c*gridInteractionCount n ≤ c*gridInteractionCount N :=
    mul_le_mul_of_nonneg_left hq hc
  have hfirst : d*n*(δ*τ)+c*gridInteractionCount n*δ^2+δ^2*t ≤
      (d*N+c*gridInteractionCount N+t)*δ := by
    calc
      _ ≤ (d*N)*δ+(c*gridInteractionCount N)*δ+δ*t := by
        apply add_le_add
        · exact add_le_add (mul_le_mul hdn hdt (mul_nonneg hδ hτ.le) (mul_nonneg hd hN))
            (mul_le_mul hcq hdsq (sq_nonneg δ) (mul_nonneg hc hNq))
        · exact mul_le_mul_of_nonneg_right hdsq ht
      _ = _ := by ring
  have han : a*n ≤ a*N := mul_le_mul_of_nonneg_left hnN ha
  have hbn : b*gridInteractionCount n ≤ b*gridInteractionCount N :=
    mul_le_mul_of_nonneg_left hq hb
  have hcubic : 2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2 ≤
      2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2 := by
    gcongr
  let A := d*N+c*gridInteractionCount N+t
  let B := D*(2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2)
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hv : 0 ≤ δ^3/τ := div_nonneg (pow_nonneg hδ 3) hτ.le
  calc
    _ = η*(d*n*(δ*τ)+c*gridInteractionCount n*δ^2+δ^2*t)+
        D*(2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2)*(δ^3/τ) := by ring
    _ ≤ η*(A*δ)+B*(δ^3/τ) := add_le_add
      (mul_le_mul_of_nonneg_left hfirst hη)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcubic hD) hv)
    _ = A*(δ*η)+B*(δ^3/τ) := by ring
    _ ≤ A*(δ*η+δ^3/τ)+B*(δ*η+δ^3/τ) := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hδ hη)) hB)
    _ = _ := by dsimp [A,B] <;> ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseCutoffBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative transport of the actual supported cutoff to a linear
phase chart, including the inverse frequency factor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseGeometry RealModes

lemma phaseCutoffBudget_polynomial (m : ℕ) {C J W : ℝ → ℝ}
    (hC : HasPolynomialBound C) (hJ : HasPolynomialBound J) (hW : HasPolynomialBound W) :
    HasPolynomialBound (fun x => phaseCutoffBudget m (C x) (J x) (W x)) :=
  hW.mul (((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul hC).mul (hJ.pow m))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma cellChartCompact_subset (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    (A.cellChartCompact i a h k : Set JetPolynomial.Base) ⊆ A.chartWeightCompact i :=
  Set.image_mono (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTensorReadBudget
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorReadFiberSpace
local instance polynomialTensorReadDualAdd_r197f7a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorReadDualSmul
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorReadFiberNormed
local instance polynomialTensorReadSectionNormed_r197f7a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialTensorReadSectionSpace_r197f7a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_tensor_read_budget (B : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) :
    ∃ R : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (R m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ R m x ∧ B m x ≤ R m x) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ s : ℝ, 0 < s → s ≤ 1 →
    ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ m, A.TensorWeightedBound s m (B m x) u) →
      ∀ i m, WeightedEstimates.WeightedBound univ s m (R m x) (A.tensorPlaneRead i u) := by
  classical
  choose D hD hread using A.tensorPlaneRead_decode_bound
  let R := fun m x => 1+B m x+D m*B m x
  have hR (m : ℕ) : HasPolynomialBound (R m) :=
    ((polynomialBound_const zero_le_one).add (hB m)).add
      ((polynomialBound_const (zero_le_one.trans (hD m))).mul (hB m))
  have hB0 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ B m x := by
    obtain ⟨_,_,_,hh⟩ := hB m
    exact (hh x hx).1
  refine ⟨R,hR,?_,?_⟩
  · intro m x hx
    have hb := hB0 m x hx
    have hd := zero_le_one.trans (hD m)
    dsimp [R]
    constructor <;> nlinarith
  · intro x hx s hs hs1 u hu hb i m
    have he := A.tensorEncode_bound hu hs (hB0 m x hx) (hb m)
    have hh := hread m i (A.tensorEncode u) s (B m x) hs hs1 (hB0 m x hx)
      (A.tensorEncode_smooth hu) he
    rw [A.tensorDecode_encode] at hh
    apply hh.mono_const
    dsimp [R]
    linarith [hB0 m x hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridAdjustedIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAdjustedIncrementFiberSpace
local instance gridAdjustedIncrementDualAdd_r197f7a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAdjustedIncrementDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAdjustedIncrementFiberNormed
local instance gridAdjustedIncrementSectionNormed_r197f7a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridAdjustedIncrementSectionSpace_r197f7a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_3_r197f7a_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_adjusted_increment (g : SmoothMetric M) (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J B Y : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hY : ∀ m, RealModes.HasPolynomialBound (Y m)) (hH : RealModes.HasPolynomialBound H)
    (hH1 : ∀ x, 1 ≤ x → 1 ≤ H x) (hY1 : ∀ m x, 1 ≤ x → 1 ≤ Y m x)
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, RealModes.HasPolynomialBound (P m)) ∧
      (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x → (n : ℝ) ≤ H x → ∀ r : ℝ, 0 < r →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {ρ R : ℝ}
        (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ _hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      ρ⁻¹ ≤ H x →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
        (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
        (d i j).budgets.mode m ≤ B m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      (hh : 0 < h) →
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion (a i) h) →
      ∀ Qb : ∀ i, (a i) → PhaseBasis,
      (∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w (i,k.val,j) • (Qb i k).ξ j)) →
      (∀ i k j y, y ∈ (c i (k,j)).e.source → (d i (k,j)).cutoff ((c i (k,j)).e y) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val y / w (i,k.val,j)) →
      (∀ i k j y, y ∈ (c i (k,j)).e.source →
        (d i (k,j)).form ((c i (k,j)).e y) = (Qb i k).Q j) →
      (∀ i k j, tsupport (supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆
        (c i (k,j)).e.source) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
      ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m x) f) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m x*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m x*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • f)) := by
  classical
  obtain ⟨e,E,S,T,hE,hS,hT,htrial⟩ :=
    A.polynomial_finite_atlas_trial q B (fun _ => H) Y hB (fun _ => hH) hY
  obtain ⟨Rb,hRb,hRb1,hread⟩ := A.polynomial_tensor_read_budget S hS
  let B' := fun m x => 1+B m x+Rb m x
  have hB' (m : ℕ) : RealModes.HasPolynomialBound (B' m) :=
    ((RealModes.polynomialBound_const zero_le_one).add (hB m)).add (hRb m)
  have hB'1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ B' m x := by
    have hb := hB1 m x hx
    have hr := (hRb1 m x hx).1
    dsimp [B'] <;> linarith
  have hBB' (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : B m x ≤ B' m x := by
    have hr := (hRb1 m x hx).1
    dsimp [B'] <;> linarith
  have hRB' (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : Rb m x ≤ B' m x := by
    have hb := hB1 m x hx
    dsimp [B'] <;> linarith
  obtain ⟨α,β,γ,ζ,D,hα,hβ,hγ,hζ,hD,hinc⟩ := A.grid_free_forced_increment V houter hε hκ hb
    FJ C J B B' hFJ hFJ1 hC hJ hB hB' hC1 hB'1 q
  let P := gridIncrementSize α β H
  let Q := gridIncrementError α β γ ζ T D H
  refine ⟨e,E,P,Q,hE,gridIncrementSize_polynomial α β H hα hβ hH,
    gridIncrementError_polynomial α β γ ζ T D H hα hβ hγ hζ hT hD hH,?_⟩
  intro h a ξ w hw hV n hn x hx hnH r hr F hF hlocal hpairs hImm hnormal hgram
    φ τ s c ρ R d hφ hc hρ hτ hs hτs hs1 hρB hρH hbud hFjets hh hcover Qb hphase
    hcut hform hsup hsmall f hf hsym hnear hsize δ hδ hδτ
  have hK (i : A.centers) (j : (a i) × Fin 3) :
      (modeSupport (A.cellChartCompact i (a i) h j.1.val) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    Set.image_mono (A.cellChartCompact_subset i (a i) h j.1.val)
  have hcard (i : A.centers) : (Fintype.card ((a i) × Fin 3) : ℝ) ≤ H x := by
    have hi : Fintype.card ((a i) × Fin 3) ≤ n :=
      (Fintype.card_le_of_injective (fun j : (a i) × Fin 3 => (⟨i,j⟩ : A.GridPhaseIndex a))
        (by intro j k he; exact eq_of_heq (Sigma.mk.inj he).2)).trans hn
    exact (Nat.cast_le.mpr hi).trans hnH
  obtain ⟨u,hu,husym,_,huball,husize,hures⟩ := htrial x hx g.inner g.contMDiff r hr d hρ
    hτ hs hτs hs1 (fun _ => hH1 x hx) (fun m => hY1 m x hx)
    (fun i _ => ⟨hcard i,hρH⟩) hbud hsmall f hf hsym hnear hsize δ hδ
  have hub (i : A.centers) (m : ℕ) := hread x hx s hs hs1 u hu husize i m
  have hbud' (i : A.centers) (j : (a i) × Fin 3) (m : ℕ) :
      (d i j).budgets.inv m ≤ B' m x ∧ (d i j).budgets.forms m ≤ B' m x ∧
      (d i j).budgets.psi m ≤ B' m x ∧ (d i j).budgets.normal m ≤ B m x :=
    ⟨(hbud i j m).1.trans (hBB' m x hx),
      (hbud i j m).2.2.1.trans (hBB' m x hx),
      (hbud i j m).2.2.2.2.1.trans (hBB' m x hx),(hbud i j m).2.2.2.2.2.1⟩
  have hmean (m : ℕ) : A.TensorWeightedBound τ m (δ^2*T m x*(τ/s)^(q+1))
      (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f) := by
    have he := A.grid_free_mean_residual hh hcover d hρ Qb (fun i k j => w (i,k.val,j))
      (fun i k j => (zero_lt_one.trans_le (hw (i,k.val,j))).ne') hphase hcut hform hsup hK
      u hu husym huball hδ.ne' hτ.ne' q f hf hτ hτs (hures m)
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨U,hU,hUb,hUe⟩ := hinc h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal
    hgram d hφ hc hρ hτ hs hτs hs1 (fun m => (hρB m).trans (hBB' m x hx)) hbud' hFjets
    δ hδ hδτ u hu huball (fun i m => (hub i m).mono_const (hRB' m x hx)) f hf
    (fun m => δ^2*T m x*(τ/s)^(q+1)) hmean
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnon (Z : ℕ → ℝ → ℝ) (hz : ∀ m, RealModes.HasPolynomialBound (Z m)) (m : ℕ) :
      0 ≤ Z m x := by obtain ⟨_,_,_,hp⟩ := hz m; exact (hp x hx).1
  refine ⟨U,hU,?_,?_⟩
  · intro m i
    apply (hUb m i).mono_const
    exact gridIncrementSize_bound (hnon α hα m) (hnon β hβ m) hn0 hnH hδ.le hτ.le
  · intro m i
    apply (hUe m i).mono_const
    exact gridIncrementError_bound (hnon α hα (m+1)) (hnon β hβ (m+1))
      (hnon γ hγ m) (hnon ζ hζ m) (hnon T hT m) (hD m) hn0 hnH hδ.le hτ hδτ
      (hτs.trans hs1) (pow_nonneg (div_nonneg hτ.le hs.le) _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCardinality
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial growth of the variable grid and its quadratic labels. -/
noncomputable section
open scoped BigOperators ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma gridPhaseIndex_card (s : A.centers → Finset Index) :
    (Fintype.card (A.GridPhaseIndex s) : ℝ) = 3*∑ i : A.centers, ((s i).card : ℝ) := by
  classical
  simp only [GridPhaseIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe,
    Fintype.card_fin,Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearMeanBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct every numerical mean budget in a selected linear phase
chart with explicit polynomial dependence on the geometry. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

lemma linearMeanGeometryBudget_growth (p : ℕ → ℕ) (A : ℕ → ℝ)
    (B P : ℕ → ℝ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hB : ∀ m, HasPolynomialBound (B m)) (hP : ∀ m, HasPolynomialBound (P m)) (m : ℕ) :
    HasPolynomialBound (fun x => linearMeanGeometryBudget p A
      (fun r => B r x) (fun r => P r x) m) :=
  ((((polynomialBound_const zero_le_one).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 3 by norm_num)).mul (hB m))).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 16 by norm_num)).mul ((hB m).pow 2))).add (hP m)).add
    ((polynomialBound_const (hA m)).mul ((hB m).pow (p m)))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridMeanBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual grid mean budgets in the inverse grid scale. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes JetPolynomial

lemma gridMeanBudget_polynomial (p : ℕ → ℕ) (A L : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ) (hA : ∀ m, 0 ≤ A m) (hL : ∀ m, 0 ≤ L m)
    (hB : ∀ m, HasPolynomialBound (B m)) (m : ℕ) :
    HasPolynomialBound (gridMeanBudget p A L B m) := by
  apply linearMeanGeometryBudget_growth p A B _ hA hB
  intro j
  exact (polynomialBound_const zero_le_one).add
    (phaseCutoffBudget_polynomial j
      ((polynomialBound_const (hL j)).mul (polynomialBound_id.pow (6*j)))
      (hB j) (polynomialBound_const zero_le_one))

lemma gridMeanBudget_at_inverse (p : ℕ → ℕ) (A L : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    gridMeanBudget p A L B m z⁻¹ =
      linearMeanGeometryBudget p A (fun j => B j z⁻¹)
        (fun j => 1+phaseCutoffBudget j (L j/z^(6*j)) (B j z⁻¹) 1) m := by
  simp only [gridMeanBudget,inv_pow,div_eq_mul_inv]

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridGeometricIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberSpace
local instance gridGeometricIncrementDualAdd_r197f7a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberNormed
local instance gridGeometricIncrementSectionNormed_r197f7a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGeometricIncrementSectionSpace_r197f7a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_4_r197f7a_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_geometric_increment_oai (g : SmoothMetric M) (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b a₀ C₀ H₀ K D : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH₀ : 0 ≤ H₀) (hK : 0 ≤ K) (hD : 0 < D)
:
    ∃ r : ℝ, 0 < r ∧ ∀ (FJ Y : ℕ → ℝ → ℝ),
    (∀ m, RealModes.HasPolynomialBound (FJ m)) →
    (∀ m, RealModes.HasPolynomialBound (Y m)) →
    (∀ m x, 1 ≤ x → 1 ≤ FJ m x) →
    (∀ m x, 1 ≤ x → 1 ≤ Y m x) → ∀ q : ℕ,
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, RealModes.HasPolynomialBound (P m)) ∧
      (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, ∀ _hz : 0 < z, z ≤ 1 → ∀ a : A.centers → Finset Index,
      (∑ i, ((a i).card : ℝ)) ≤ K/z^12 →
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion (a i) (z^6)) →
    ∀ (Qb : ∀ i, (a i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i k j, ξ (i,k.val,j) = (Qb i k).ξ j) → (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      (∀ i k j, ‖(Qb i k).Q j‖ ≤ C₀) →
      (∀ i k j y, (Qb i k).Q j (A.tensorPlaneRead i g.inner y) ≤ H₀) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Qb i k).Q j (A.tensorPlaneRead i g.inner y)) →
    ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a (z^6) l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a (z^6) κ ξ w F →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (w (i,k.val,j) • (Qb i k).ξ j) ∧
        ‖secondQuadratic (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (-(w (i,k.val,j) • (Qb i k).ξ j).2,(w (i,k.val,j) • (Qb i k).ξ j).1)‖⁻¹ ≤ D) →
    ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 2*D ≤ FJ m z⁻¹ ∧ C₀ ≤ FJ m z⁻¹) →
      (∀ i k j m, ‖w (i,k.val,j) • (Qb i k).ξ j‖ ≤ FJ m z⁻¹ ∧
        ∀ hξ : w (i,k.val,j) • (Qb i k).ξ j ≠ 0,
          ‖(phaseEquiv (w (i,k.val,j) • (Qb i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ FJ m z⁻¹) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (FJ m z⁻¹/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*(z⁻¹)^e))) →
    ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m z⁻¹) f) →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • f)) := by
  classical
  obtain ⟨p,p',C,C',L,hC,hC',hL,r,ρ,R,hr,hρ,hR,hdata⟩ :=
    A.polynomial_grid_mean_data g ha₀ hC₀ hH₀
  refine ⟨r,hr,?_⟩
  intro FJ Y hFJ hY hFJ1 hY1 q
  let Cs := fun m x => C m*(FJ m x)^(p m)
  let Js := fun m x => 1+2*FJ m x
  let B := fun m x => 1+ρ⁻¹+gridMeanBudget p' C' L FJ m x
  let H := fun x => 1+ρ⁻¹+3*K*x^12
  have hCs (m : ℕ) : RealModes.HasPolynomialBound (Cs m) :=
    (RealModes.polynomialBound_const (zero_le_one.trans (hC m))).mul ((hFJ m).pow (p m))
  have hJs (m : ℕ) : RealModes.HasPolynomialBound (Js m) :=
    (RealModes.polynomialBound_const zero_le_one).add
      ((RealModes.polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hFJ m))
  have hB (m : ℕ) : RealModes.HasPolynomialBound (B m) :=
    ((RealModes.polynomialBound_const zero_le_one).add (RealModes.polynomialBound_const (inv_nonneg.mpr hρ.le))).add
      (gridMeanBudget_polynomial p' C' L FJ (fun m => zero_le_one.trans (hC' m))
        (fun m => zero_le_one.trans (hL m)) hFJ m)
  have hH : RealModes.HasPolynomialBound H :=
    ((RealModes.polynomialBound_const zero_le_one).add (RealModes.polynomialBound_const (inv_nonneg.mpr hρ.le))).add
      ((RealModes.polynomialBound_const (by positivity : 0 ≤ 3*K)).mul (RealModes.polynomialBound_id.pow 12))
  have hBn (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ gridMeanBudget p' C' L FJ m x :=
    (gridMeanBudget_polynomial p' C' L FJ (fun m => zero_le_one.trans (hC' m))
      (fun m => zero_le_one.trans (hL m)) hFJ m).nonneg hx
  have hB1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ B m x := by
    have hh := hBn m x hx
    have hi := inv_nonneg.mpr hρ.le
    dsimp [B] <;> linarith
  have hCs1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Cs m x :=
    one_le_mul_of_one_le_of_one_le (hC m) (one_le_pow₀ (hFJ1 m x hx))
  have hH1 (x : ℝ) (hx : 1 ≤ x) : 1 ≤ H x := by
    have hi := inv_nonneg.mpr hρ.le
    have hp : 0 ≤ 3*K*x^12 := by positivity
    dsimp [H] <;> linarith
  obtain ⟨e,E,P,Q,hE,hP,hQ,hstep⟩ := A.grid_adjusted_increment g V houter hε hκ hb
    FJ Cs Js B Y H hFJ hFJ1 hCs hJs hB hY hH hH1 hY1 hCs1 hB1 q
  refine ⟨e,E,P,Q,hE,hP,hQ,?_⟩
  intro z hz hz1 a hcard hcover Qb ξ w hξ hw hV hQnorm hQup hQlow F hF
    hlocal hpairs hImm hnormal hgram hcell τ s hτ hs hτs hs1 hBD hphases hFjets
    hsmall f hf hsym hnear hsize δ hδ hδτ
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr hz1
  let n := Fintype.card (A.GridPhaseIndex a)
  have hnH : (n : ℝ) ≤ H z⁻¹ := by
    change (Fintype.card (A.GridPhaseIndex a) : ℝ) ≤ _
    rw [A.gridPhaseIndex_card]
    have hc : 3*∑ i, ((a i).card : ℝ) ≤ 3*K*(z⁻¹)^12 := by
      have hh := mul_le_mul_of_nonneg_left hcard (by norm_num : (0:ℝ) ≤ 3)
      simpa only [inv_pow,div_eq_mul_inv,mul_assoc] using hh
    have hi := inv_nonneg.mpr hρ.le
    change 3*∑ i : A.centers, ((a i).card : ℝ) ≤ 1+ρ⁻¹+3*K*(z⁻¹)^12
    linarith
  have hgeom (i : A.centers) (k : a i) (j : Fin 3) (y : SmallModes.Base)
      (hy : y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base)) :=
    let hy' := (Set.image_mono (A.cellChartCompact_subset i (a i) (z^6) k.val)) hy
    And.intro (hImm i y hy') (And.intro (hcell i k j y hy).1
      (And.intro (hgram i y hy') (hcell i k j y hy).2))
  obtain ⟨c,d,hsolver,hcut,hform,hsupp,hbud⟩ := hdata z hz hz1 a hcover Qb
    (fun i k j => w (i,k.val,j)) (fun i k j => hw (i,k.val,j)) hQnorm hQup hQlow F hF τ s hs hs1
    D hD (fun m => FJ m z⁻¹) (fun m => hFJ1 m z⁻¹ hx) hBD hphases hFjets hgeom
  have hbud' (i : A.centers) (j : (a i) × Fin 3) (m : ℕ) :
      (d i j).budgets.inv m ≤ B m z⁻¹ ∧ (d i j).budgets.chi m ≤ B m z⁻¹ ∧
      (d i j).budgets.forms m ≤ B m z⁻¹ ∧ (d i j).budgets.pull m ≤ B m z⁻¹ ∧
      (d i j).budgets.psi m ≤ B m z⁻¹ ∧ (d i j).budgets.normal m ≤ B m z⁻¹ ∧
      (d i j).budgets.mode m ≤ B m z⁻¹ := by
    have he : linearMeanGeometryBudget p' C' (fun m => FJ m z⁻¹)
        (fun l => 1+phaseCutoffBudget l (L l/z^(6*l)) (FJ l z⁻¹) 1) m ≤ B m z⁻¹ := by
      rw [← gridMeanBudget_at_inverse]
      have hi := inv_nonneg.mpr hρ.le
      dsimp [B] <;> linarith
    obtain ⟨hi,hc,hf,hp,hψ,hn,hm⟩ := hbud i j m
    exact ⟨hi.trans he,hc.trans he,hf.trans he,hp.trans he,hψ.trans he,hn.trans he,hm.trans he⟩
  refine hstep (z^6) a ξ w hw hV n le_rfl z⁻¹ hx hnH r hr F hF
    hlocal hpairs hImm hnormal hgram d ?_ ?_ hρ hτ hs hτs hs1 ?_ ?_
    hbud' hFjets (pow_pos hz 6) hcover Qb ?_ ?_ ?_ ?_
    hsmall f hf hsym hnear hsize δ hδ hδτ
  · intro i j
    rw [hξ i j.1 j.2]
  · intro i j
    exact ⟨funext (fun m => (hsolver i j m).1),funext (fun m => (hsolver i j m).2.1),
      fun m => (hsolver i j m).2.2⟩
  · intro m
    have hh := hBn m z⁻¹ hx
    dsimp [B] <;> linarith
  · have hp : 0 ≤ 3*K*(z⁻¹)^12 := by positivity
    dsimp [H] <;> linarith
  · intro i k j
    funext y
    simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  · intro i k j y hy
    exact hcut i (k,j) y hy
  · intro i k j y _
    exact congrFun (hform i (k,j)) _
  · intro i k j
    change tsupport (fun y => A.planeWeight i y * normalizedCutoff (a i) (z^6) k.val y) ⊆ _
    exact hsupp i (k,j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment_oai.{u_1}
