-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:16.808986+00:00
-- url     : https://prove2.me/submissions/3f6cb182-7a63-42b4-9e1a-fe85c3d4736b

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_freeDisplacement_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_freeDisplacement_residual_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
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



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma fullErrorConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fullErrorConstant n m K :=
  mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK))
    (targetConstant_nonneg n (m + 1) hK)

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RootMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma sqrt_difference {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt u - Real.sqrt v = (u - v) * rootDifferenceCoefficient ![u, v] := by
  have hh : Real.sqrt u + Real.sqrt v ≠ 0 := ne_of_gt
    (add_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hv))
  dsimp [rootDifferenceCoefficient]
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hh).2
  nlinarith [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma weighted_coefficient {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A : Base → Tensor}
    {s J P C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m C A) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * C)
      (coefficient Q e A) := by
  have hAe := hAB.comp_coordinates hV hU hs hs1 hJ hC he hA heU heB
  have hh := hQB.clm_apply hV hs.le hP (by positivity) hQ (hA.comp he heU) hAe
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma weighted_coefficient_difference {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A B : Base → Tensor}
    {s J P D : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m D (A - B)) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * D)
      (fun p => coefficient Q e A p - coefficient Q e B p) := by
  apply (weighted_coefficient hU hV hs hs1 hJ hP hD hQ he heU (hA.sub hB) heB hQB hAB).congr
  intro p hp
  exact (map_sub (Q p) (A (e p)) (B (e p))).symm




end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearized_add_right {n : ℕ} {F X Y : RField n} {p : Base}
    (hX : DifferentiableAt ℝ X p) (hY : DifferentiableAt ℝ Y p) (v w : Base) :
    realLinearized F (fun q => X q + Y q) v w p =
      realLinearized F X v w p + realLinearized F Y v w p := by
  simp only [realLinearized, partial_add hX hY, dotProduct_add]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean

lemma evaluate_realLinearizedTensor {n : ℕ} (F X : RField n) (p v w : Base) :
    evaluate (realLinearizedTensor F X p) v w = realLinearized F X v w p := by
  simp only [realLinearized, derivative_base_decomposition F p v,
    derivative_base_decomposition F p w, derivative_base_decomposition X p v,
    derivative_base_decomposition X p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realLinearizedTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realLinearized]
  ring



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
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
open Set ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realLinearizedTensor_congr_right {n : ℕ} {F X Y : RField n} {p : Base}
    (h : X =ᶠ[nhds p] Y) : realLinearizedTensor F X p = realLinearizedTensor F Y p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]

lemma realLinearizedTensor_zero_right {n : ℕ} (F : RField n) (p : Base) :
    realLinearizedTensor F (fun _ => 0) p = 0 := by
  ext i
  simp [realLinearizedTensor_apply, realLinearized, coordDeriv]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ExtendedCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
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
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



lemma displacement_zero_value {n : ℕ} (τ : ℝ) (φ : Base → ℝ) {A : Field n}
    {p : Base} (hA : A p = 0) : displacement τ φ A p = 0 := by
  ext i
  simp [displacement, QuadraticMean.realMode, QuadraticMean.realPart, hA]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

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

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance planeReadSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

namespace Perturbation

lemma linearized_add {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (p : Base) :
    linearized P ε G (fun x => H x + K x) t p =
      linearized P ε G H t p + linearized P ε G K t p := by
  simp only [linearized, Expression.variation_add _ G hH hK, mul_add, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartDisplacement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real displacements and tensor targets transported through a permitted
phase chart, with their actual support and size estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (φ : SmallModes.Base → ℝ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x)

lemma chart_displacement_smooth_support (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    ContDiff ℝ ∞ (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ∧
      tsupport (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ⊆ K := by
  refine ⟨contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn
    (chartPull e he K hK Z).contDiff.contDiffOn τ), ?_⟩
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  exact hx (RealModes.displacement_zero_value τ φ ((chartPull e he K hK Z).zero_on_compl hn))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full linearized metric perturbation preserves the support of its
varying field, including every higher-jet polynomial term. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero_of_notMem {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {p : SmallModes.Base} (hp : p ∉ tsupport X) :
    coordinateFullLinearized P ε G X p = 0 := by
  have hx : X =ᶠ[nhds p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : (X ∘ planeCoordinateIsometry) =ᶠ[nhds (planeCoordinateIsometry.symm p)] (fun _ => 0) := by
    apply hx.comp_tendsto
    simpa only [planeCoordinateIsometry.apply_symm_apply] using
      (planeCoordinateIsometry.continuous.continuousAt (x := planeCoordinateIsometry.symm p)).tendsto
  have hn : planeCoordinateIsometry.symm p ∉ tsupport (X ∘ planeCoordinateIsometry) :=
    notMem_tsupport_iff_eventuallyEq.mpr hc
  have hm : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X p = 0 := by
    rw [RealModes.realLinearizedTensor_congr_right hx, RealModes.realLinearizedTensor_zero_right]
  funext k
  simp only [coordinateFullLinearized, Pi.add_apply, hm, Pi.zero_apply, zero_add,
    coordinateRealLinearized, linearized]
  apply Finset.sum_eq_zero
  intro l _
  rw [(P k l).variation_zero_of_notMem G hn 0, mul_zero]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

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

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorPlaneRestore
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

theorem vectorPlaneRestore_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : A.centers → SmallModes.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.WeightedBound s m (D*C) (A.vectorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i => f i ∘ planeCoordinateIsometry) s C hs hs1 hC
    (fun i => (hf i).comp planeCoordinateIsometry.contDiff)
    (fun i => weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i))

end SmoothingAtlas
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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma restore_plane_mfderiv (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (hd : DifferentiableAt ℝ f (planeCoordinateIsometry (chart (i : M) p))) :
    mfderiv planeModel 𝓘(ℝ,V)
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
    (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
      (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p)) := by
  have he : restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) =ᶠ[𝓝 p]
      (f ∘ planeCoordinateIsometry) ∘ chart (i : M) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with x hx
    exact A.restore_plane_on_source i f hf hx
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have hfc : DifferentiableAt ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) :=
    hd.comp _ planeCoordinateIsometry.differentiableAt
  rw [he.mfderiv_eq]
  change mfderiv planeModel 𝓘(ℝ,V) ((f ∘ planeCoordinateIsometry) ∘ chart (i : M)) p = _
  rw [mfderiv_comp p hfc.mdifferentiableAt (hc.mdifferentiableAt (by simp))]
  rw [mfderiv_eq_fderiv]
  change (fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p)).comp
    (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p) = _
  have heq : fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact (hd.hasFDerivAt.comp _ planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [heq]
  exact ContinuousLinearMap.comp_assoc _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricCalculus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric identities for actual smooth maps on the surface. The
finite-sum identity retains every cross term between distinct chart modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma surfaceDifferential_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) :
    surfaceDifferential (F+U) p = surfaceDifferential F p + surfaceDifferential U p :=
  mfderiv_add hF hU

lemma mfderiv_finite_sum {ι : Type*} (s : Finset ι) (f : ι → M → V) {p : M}
    (hf : ∀ i ∈ s, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) :
    surfaceDifferential (∑ i ∈ s, f i) p =
      ∑ i ∈ s, surfaceDifferential (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mfderiv_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : MDifferentiableAt planeModel 𝓘(ℝ,V) (∑ i ∈ s, f i) p := by
      have key : ∀ t : Finset ι, (∀ i ∈ t, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) →
          MDifferentiableAt planeModel 𝓘(ℝ,V) (∑ i ∈ t, f i) p := by
        intro t
        induction t using Finset.induction_on with
        | empty =>
          intro _
          simp only [Finset.sum_empty]
          exact mdifferentiableAt_const
        | insert b t hb ih' =>
          intro hh
          rw [Finset.sum_insert hb]
          exact (hh b (Finset.mem_insert_self b t)).add
            (ih' (fun i hi => hh i (Finset.mem_insert_of_mem hi)))
      exact key s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [surfaceDifferential_add h1 h2, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma linearMetricForm_finite_sum {ι : Type*} [Fintype ι]
    (F : M → V) (f : ι → M → V) {p : M}
    (hf : ∀ i, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p)
    (v w : TangentSpace planeModel p) :
    linearMetricForm F (∑ i, f i) p v w = ∑ i, linearMetricForm F (f i) p v w := by
  unfold linearMetricForm
  rw [mfderiv_finite_sum Finset.univ f (fun i _ => hf i)]
  simp only [sum_apply,inner_sum,sum_inner,Finset.sum_add_distrib]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric and linearized metric of supported restored displacements
in the original atlas coordinates. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4
open FiniteOrderSmoothing JetPolynomial

lemma surfaceDifferential_zero_off_support
    {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M → V) {p : M}
    (hp : p ∉ tsupport F) : surfaceDifferential F p = 0 := by
  have he : F =ᶠ[𝓝 p] (fun _ => (0 : V)) := notMem_tsupport_iff_eventuallyEq.mp hp
  unfold surfaceDifferential
  rw [he.mfderiv_eq, mfderiv_const]
  rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricTensorFiberNormed_r6fc90c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r6fc90c_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTensorDualAdd
local instance metricTensorDualSmul_r6fc90c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_apply (F U : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    linearMetricTensor F U p v w = linearMetricForm F U p v w := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric of the actual global oscillation, including every cross term
between different atlas patches. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasMetricFiberNormed_r6fc90c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasMetricFiberSpace_r6fc90c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasMetricDualAdd_r6fc90c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasMetricDualSmul_r6fc90c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasMetricSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMetricSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma euclidean_vectorPlaneRestore (f : A.centers → SmallModes.Base → RealModes.RVec 4) :
    spaceCoordinates.symm ∘ A.vectorPlaneRestore f =
      A.vectorPlaneRestore (fun i => spaceCoordinates.symm ∘ f i) := by
  funext p
  simp only [vectorPlaneRestore,Function.comp_apply,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,map_smul]
  · simp only [restore,indicator_of_notMem hp,map_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredLinearizedMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact globalization of the actual metric linearization. The local
base map is the constructed smooth representative of the global map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4

lemma euclidean_linearized_coordinate_value (F U : SmallModes.Base → Space)
    {y : SmallModes.Base} (hF : DifferentiableAt ℝ F y) (hU : DifferentiableAt ℝ U y)
    (v w : SmallModes.Base) :
    PhaseMean.evaluate (RealModes.realLinearizedTensor (spaceCoordinates ∘ F) (spaceCoordinates ∘ U) y) v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ U y w) +
        inner ℝ (fderiv ℝ U y v) (fderiv ℝ F y w) := by
  rw [RealModes.evaluate_realLinearizedTensor]
  simp only [RealModes.realLinearized,SmallModes.coordDeriv]
  rw [(spaceCoordinates.hasFDerivAt.comp y hF.hasFDerivAt).fderiv,
    (spaceCoordinates.hasFDerivAt.comp y hU.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change spaceCoordinates (fderiv ℝ F y v) ⬝ᵥ spaceCoordinates (fderiv ℝ U y w) +
    spaceCoordinates (fderiv ℝ F y w) ⬝ᵥ spaceCoordinates (fderiv ℝ U y v) = _
  rw [spaceCoordinates_dot,spaceCoordinates_dot]
  congr 1
  exact real_inner_comm _ _

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberSpace
local instance restoredLinearDualSmul_r6fc90c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberNormed
local instance restoredLinearSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredLinearSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem restored_linearized_metric (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (spaceCoordinates ∘ f) (planeCoordinateIsometry y))) := by
  funext p
  ext v w
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [linearMetricTensor_apply,A.tensorRestore_apply i _ hp,fiberFromThree_apply]
    have hd := A.plane_chart_differential i hp
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w) = _ at hw
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p w) = _ at hw
    rw [euclidean_linearized_coordinate_value _ _
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _) (hf.differentiable (by simp) _)]
    have hu := A.restore_plane_mfderiv i f hsp hp (hf.differentiable (by simp) _)
    change surfaceDifferential (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (surfaceDifferential (chart (i : M)) p)) at hu
    unfold linearMetricForm
    rw [hu]
    by_cases hs : p ∈ tsupport (A.weight i)
    · rw [A.vectorPlaneRead_differential i hF hs,A.outer_one i p hs,one_mul]
      simp only [ContinuousLinearMap.comp_apply,hv,hw]
      rfl
    · have hn : planeCoordinateIsometry (chart (i : M) p) ∉ tsupport f := by
        intro hh
        exact hs (A.mem_weight_support_of_plane i hp (hsp hh))
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp only [ContinuousLinearMap.zero_comp,zero_apply,inner_zero_left,inner_zero_right,add_zero,mul_zero]
  · have hs : p ∉ tsupport (A.weight i) := fun h => hp (A.weight_support i h)
    have hu := surfaceDifferential_zero_off_support
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))
      (fun h => hs (A.restore_plane_tsupport i f hsp h))
    have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [linearMetricTensor_apply,linearMetricForm,hu,zero_apply,inner_zero_left,
      inner_zero_right,add_zero,bundleRestore,ho,zero_smul]

end SmoothingAtlas
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasLinearizedMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual local linear residuals to the global metric tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance atlasLinearFiberNormed_r6fc90c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_r6fc90c_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasLinearDualAdd
local instance atlasLinearDualSmul_r6fc90c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasLinearSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma linearMetricTensor_finite_sum {ι : Type*} [Fintype ι]
    (F : M → Space) (f : ι → M → Space) (hf : ∀ i, ContMDiff planeModel spaceModel ∞ (f i)) :
    linearMetricTensor F (∑ i, f i) = fun p => ∑ i, linearMetricTensor F (f i) p := by
  funext p
  ext v w
  simpa only [sum_apply,linearMetricTensor_apply] using
    linearMetricForm_finite_sum F f (fun i => ((hf i) p).mdifferentiableAt (by simp)) v w

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasLinearDualAdd
local instance atlasLinearFiberNormed_r6fc90c_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_r6fc90c_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasLinearDualSmul_r6fc90c_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasLinearSectionNormed_r6fc90c_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace_r6fc90c_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → Space) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (spaceCoordinates ∘ f i)) := by
  unfold vectorPlaneRestore
  rw [linearMetricTensor_finite_sum F
    (fun i : A.centers => restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry))
    (fun i => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))]
  funext p
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.restored_linearized_metric i hF (f i) (hf i) (hsp i)) p

theorem euclidean_vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → RealModes.RVec 4) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i)) := by
  rw [A.euclidean_vectorPlaneRestore]
  have hh := A.vectorPlaneRestore_linearized hF (fun i => spaceCoordinates.symm ∘ f i)
    (fun i => spaceCoordinates.symm.contDiff.comp (hf i))
    (fun i => (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) (f i)).trans (hsp i))
  have he (i : A.centers) : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f i) = f i := by
    funext x
    simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullLinearized P ε G (X + Y) =
      coordinateFullLinearized P ε G X + coordinateFullLinearized P ε G Y := by
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullLinearized, Pi.add_apply, coordinateRealLinearized,
    RealModes.realLinearizedTensor_apply]
  rw [hc, linearized_add _ ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff), ha,
    RealModes.realLinearized_add_right (hX.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hY.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additivity and smoothness of the actual full linearized operator.
Coefficient smoothness is required only near the support of the variation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) :
    coordinateFullLinearized P ε G 0 = 0 := by
  funext p
  exact coordinateFullLinearized_zero_of_notMem P ε G (by simp)

lemma coordinateFullLinearized_sum {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (a : Finset ι) (X : ι → RealModes.RField 4) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    coordinateFullLinearized P ε G (fun p => ∑ i ∈ a, X i p) =
      fun p => ∑ i ∈ a, coordinateFullLinearized P ε G (X i) p := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change coordinateFullLinearized P ε G 0 = 0
    exact coordinateFullLinearized_zero P ε G
  | @insert i a hi ih =>
    have hs : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, X j p) := ContDiff.sum fun j _ => hX j
    simp only [Finset.sum_insert hi]
    change coordinateFullLinearized P ε G (X i + fun p => ∑ j ∈ a, X j p) = _
    rw [coordinateFullLinearized_add P ε G (hX i) hs, ih]
    rfl

lemma coordinateFullLinearized_smooth {n : ℕ} {O : Set LowJet} {U : Set Base}
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {X : RealModes.RField 4} (hX : ContDiff ℝ ∞ X)
    (hXs : tsupport X ⊆ (modeSupport K : Set SmallModes.Base)) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  let Xs : SupportedField (F := Fin 4 → ℝ) (modeSupport K) :=
    ContDiffMapSupportedIn.of_support_subset hX (subset_closure.trans hXs)
  let Xp := pullSupported planeCoordinateIsometry K Xs
  have hp : ContDiff ℝ ∞ (coordinateRealLinearized P ε G X 0) := by
    apply contDiff_pi.mpr
    intro k
    have hs : ContDiff ℝ ∞ (fun x => ∑ l, ε ^ (l.val + 1) * (P k l).variation G Xp (x, 0)) :=
      ContDiff.sum (s := Finset.univ) (fun l _ =>
      contDiff_const.mul ((P k l).variation_smooth_global hO hU K.isCompact.isClosed hKU
        (hP k l) hG Xp.contDiff hQ Xp.tsupport_subset 0))
    exact hs.comp planeCoordinateIsometry.symm.contDiff
  exact (contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add hp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedSolverFacts
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite polynomial solver at parameter zero is exactly the metric
linearization; its explicit size and residual budgets are nonnegative. -/
noncomputable section
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

lemma coordinateFullLinearized_unperturbed {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (G : Base → Space) (X : RealModes.RField 4) :
    coordinateFullLinearized P 0 G X =
      RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X := by
  funext x k
  simp [coordinateFullLinearized,coordinateRealLinearized,linearized]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_r6fc90c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_r6fc90c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_r6fc90c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_r6fc90c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedReciprocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseSqrt
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for normalization by a positive square root. -/
noncomputable section
open Set Polynomial
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inverse_half (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) x‖ =
      ‖(descPochhammer ℝ j).eval (-1/2)‖*x^(-1/2-(j : ℝ)) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi hx,Real.iter_deriv_rpow_const]
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]

lemma inverse_half_power_bound {x K : ℝ} (hx : 0 < x) (hK : 1 ≤ K)
    (hi : x⁻¹ ≤ K) {j m : ℕ} (hj : j ≤ m) :
    x^(-1/2-(j : ℝ)) ≤ K^(m+1) := by
  have he : x^(-1/2-(j : ℝ)) = (x⁻¹)^((j : ℝ)+1/2) := by
    rw [← Real.rpow_neg_one x,← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  have hj0 : 0 ≤ (j : ℝ)+1/2 := by positivity
  calc
    (x⁻¹)^((j : ℝ)+1/2) ≤ K^((j : ℝ)+1/2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hi hj0
    _ ≤ K^((m+1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      push_cast
      linarith)
    _ = K^(m+1) := Real.rpow_natCast _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_inverse_sqrt (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s C K : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ K) → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
        (fun x => (Real.sqrt (f x))⁻¹) := by
  let D : ℝ := 1+∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖
  have hD : 1 ≤ D := by
    have hh : 0 ≤ ∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [D]
    linarith
  have hDj {j : ℕ} (hj : j ≤ m) : ‖(descPochhammer ℝ j).eval (-1/2)‖ ≤ D := by
    have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) =>
      norm_nonneg ((descPochhammer ℝ i).eval (-1/2))) (Finset.mem_range.mpr (by omega : j < m+1))
    dsimp only [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro U hU s C K f hs hC hK hf hpos hi hb
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) (f x)‖ ≤ D*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inverse_half j (hpos x hx)]
    exact mul_le_mul (hDj hj) (inverse_half_power_bound (hpos x hx) hK (hi x hx) hj)
      (Real.rpow_nonneg (hpos x hx).le _) (zero_le_one.trans hD)
  have hbound := hb.comp hU isOpen_Ioi.uniqueDiffOn hs hC (by positivity : 0 ≤ D*K^(m+1))
    hf hg hpos hd
  have hbound' : WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
      ((fun y : ℝ => y^(-1/2 : ℝ)) ∘ f) := by
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hbound'.congr
  intro x hx
  simp only [Function.comp_apply,Real.sqrt_eq_rpow]
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (hpos x hx).le]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedRealAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real scalar and vector products used in the quantitative normal formula. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real_dup2 {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x*g x) := by
  intro j hj x hx
  calc
    _ ≤ s^j*(∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*
        ‖iteratedFDerivWithin ℝ i f U x‖*‖iteratedFDerivWithin ℝ (j-i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2^j*C*D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeDisplacement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real displacement of the actual charted free amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma coordinate_originalFreeSeed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    coordinateAmplitude (c.originalFreeSeed δ q b) =
      (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b) :
        SmallModes.Field 4) := by
  funext x
  change (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b))
    (planeCoordinateIsometry (planeCoordinateIsometry.symm x)) = _
  rw [planeCoordinateIsometry.apply_symm_apply]

lemma freeDisplacement_smooth_support (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    ContDiff ℝ ∞ (c.freeDisplacement δ q b) ∧
      tsupport (c.freeDisplacement δ q b) ⊆ (modeSupport K : Set SmallModes.Base) := by
  unfold freeDisplacement
  rw [c.coordinate_originalFreeSeed]
  exact chart_displacement_smooth_support c.e c.smoothForward (modeSupport K) c.supportChart
    (coordinatePhase φ) (c.smoothPhase.comp planeCoordinateIsometry.symm.contDiff) τ (c.freeSeed δ q b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformFree
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform size and full-linearization residuals for the actual free
oscillation used by the charted mean construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma displacement_smooth_support (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.displacement hρ δ q A) ∧
      tsupport (d.displacement hρ δ q A) ⊆ (modeSupport K : Set SmallModes.Base) :=
  c.freeDisplacement_smooth_support δ q (d.amplitude hρ A)

end ChartedMeanData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite free oscillation and its original-coordinate linear
residual. The constants precede the immersion and scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma chartedFreeSum_eq (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    chartedFreeSum d hρ δ q A = fun x => ∑ i, (d i).displacement hρ δ q A x := rfl

lemma chartedFreeSum_smooth_support (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (chartedFreeSum d hρ δ q A) ∧
      tsupport (chartedFreeSum d hρ δ q A) ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) := by
  rw [chartedFreeSum_eq]
  refine ⟨ContDiff.sum (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1),?_⟩
  apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hz => hn (Set.mem_iUnion.mpr
    ⟨i,((d i).displacement_smooth_support hρ δ q A).2 hz⟩))

end ClosedSurfaceR4.JetPolynomial.Perturbation

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

lemma realMode_zero {n : ℕ} (θ : ℝ) : realMode θ (0 : Fin n → ℂ) = 0 := by
  change realPartCLM n (QuadraticMean.phase θ • (0 : Fin n → ℂ)) = 0
  rw [smul_zero,map_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
attribute [-instance] _root_.instVAddIntReal_solutions
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeRestore
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variable-family oscillation is the restoration of its local free sums. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

lemma finiteAtlasFreeOscillation_eq_restore
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.finiteAtlasFreeOscillation d hρ δ q u =
      A.vectorPlaneRestore (fun i => chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u)) := by
  classical
  have hj (i : A.centers) (j : ι i) :
      restore (i : M) (A.outer i)
        ((d i j).displacement hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) =
      surfaceMode τ (A.finiteGlobalPhase (φ := φ) i j) (A.finiteGlobalAmplitude d hρ δ q u i j) := by
    have hh := A.restore_displacement i τ (coordinatePhase (φ i j))
      (coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))
      ((coordinateAmplitude_support _).trans (hK i j))
    simpa only [ChartedMeanData.displacement,PolynomialSolveData.freeDisplacement,
      ChartedMeanData.freeAmplitude,finiteGlobalPhase,finiteGlobalAmplitude,
      coordinatePhase,coordinateAmplitude,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hh
  have hi (i : A.centers) :
      restore (i : M) (A.outer i)
        (chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) =
      ∑ j : ι i, surfaceMode τ (A.finiteGlobalPhase (φ := φ) i j)
        (A.finiteGlobalAmplitude d hρ δ q u i j) := by
    calc
      _ = ∑ j : ι i, restore (i : M) (A.outer i)
          ((d i j).displacement hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) := by
        funext p
        by_cases hp : p ∈ (chart (i : M)).source
        · simp only [restore,indicator_of_mem hp,Function.comp_apply,chartedFreeSum_eq,
            Finset.sum_apply,Finset.smul_sum]
        · simp only [restore,indicator_of_notMem hp,Finset.sum_apply,Finset.sum_const_zero]
      _ = _ := Finset.sum_congr rfl (fun j _ => hj i j)
  rw [finiteAtlasFreeOscillation,Fintype.sum_sigma]
  exact (Finset.sum_congr rfl (fun i _ => hi i)).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRootBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit square-root and square-root-difference bounds from a reciprocal
positivity margin, without a compact-set derivative constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sqrtBudget_nonneg (m : ℕ) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ sqrtBudget m D B := by unfold sqrtBudget; positivity

lemma inverse_sqrt_le {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hi : x⁻¹ ≤ B) :
    (Real.sqrt x)⁻¹ ≤ B := by
  have hh := inverse_half_power_bound hx hB hi (j := 0) (m := 0) (Nat.le_refl 0)
  have he : x^(-1/2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow,show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hx.le]
  simpa only [Nat.cast_zero,Nat.zero_add,sub_zero,pow_one,he] using hh

theorem polynomial_sqrt_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ B →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → WeightedBound U s m B f →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) := by
  obtain ⟨D,hD,hbound⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B f hs hB hf hp hi hb
  have hr := hf.sqrt (fun x hx => (hp x hx).ne')
  have hi' := hr.inv (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
  have hh := hb.mul_real_dup2 hU hs.le (zero_le_one.trans hB) (by positivity)
    hf hi' (hbound hU hs hB hB hf hp hi hb)
  apply hh.congr
  intro x hx
  change Real.sqrt (f x) = f x*(Real.sqrt (f x))⁻¹
  rw [← div_eq_mul_inv,eq_div_iff (Real.sqrt_pos.mpr (hp x hx)).ne']
  exact Real.mul_self_sqrt (hp x hx).le

theorem polynomial_root_bounds (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B A : ℝ} {f g : E → ℝ}, 0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) ∧
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (g x)) ∧
      WeightedBound U s m (rootDifferenceBudget m D B*A)
        (fun x => Real.sqrt (f x)-Real.sqrt (g x)) := by
  obtain ⟨D,hD,hr⟩ := polynomial_sqrt_bound (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B A f g hs hB hA hf hg hfp hgp hfi hgi hfb hgb hdiff
  have hrf := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hrg := hg.sqrt (fun x hx => (hgp x hx).ne')
  have bF := hr hU hs hB hf hfp hfi hfb
  have bG := hr hU hs hB hg hgp hgi hgb
  have hS : 0 ≤ sqrtBudget m D B := sqrtBudget_nonneg m (zero_le_one.trans hD) (zero_le_one.trans hB)
  have hsum := bF.add hU hs.le hrf hrg bG
  have hsum' : WeightedBound U s m (1+2*sqrtBudget m D B)
      (fun x => Real.sqrt (f x)+Real.sqrt (g x)) := hsum.mono_const (by linarith)
  have hpos (x : E) (hx : x ∈ U) : 0 < Real.sqrt (f x)+Real.sqrt (g x) :=
    add_pos (Real.sqrt_pos.mpr (hfp x hx)) (Real.sqrt_pos.mpr (hgp x hx))
  have hinv (x : E) (hx : x ∈ U) :
      ‖(Real.sqrt (f x)+Real.sqrt (g x))⁻¹‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos x hx))]
    exact ((inv_le_inv₀ (hpos x hx) (Real.sqrt_pos.mpr (hfp x hx))).mpr
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))).trans (inverse_sqrt_le (hfp x hx) hB (hfi x hx))
  have bInv := hsum'.inv_real hU hs (by linarith) hB (hrf.add hrg)
    (fun x hx => (hpos x hx).ne') hinv
  have hsmoothInv := (hrf.add hrg).inv (fun x hx => (hpos x hx).ne')
  have hh := hdiff.mul_real_dup2 hU hs.le hA (by positivity) (hf.sub hg) hsmoothInv bInv
  refine ⟨bF,bG,?_⟩
  have hh' : WeightedBound U s m (rootDifferenceBudget m D B*A)
      (fun x => (f x-g x)*(Real.sqrt (f x)+Real.sqrt (g x))⁻¹) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold rootDifferenceBudget
    ring
  apply hh'.congr
  intro x hx
  exact sqrt_difference (hfp x hx) (hgp x hx)

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAmplitudeBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the supported square-root amplitudes of the
metric decomposition, including their difference estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomial_phaseAmplitude_bounds (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U : Set E}, UniqueDiffOn ℝ U → ∀ {s B A : ℝ} {ψ f g : E → ℝ},
      0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B ψ → WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ f) ∧
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ g) ∧
      WeightedBound U s m (C*B^d*A) (fun x => phaseAmplitude ψ f x-phaseAmplitude ψ g x) := by
  obtain ⟨D,hD,hr⟩ := polynomial_root_bounds (E := E) m
  have hpoly : HasPolynomialBound (phaseAmplitudeBudget m D) := by
    unfold phaseAmplitudeBudget rootDifferenceBudget sqrtBudget
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro U hU s B A ψ f g hs hB hA hψ hf hg hfp hgp hfi hgi hbψ hbf hbg hdiff
  obtain ⟨bF,bG,bDiff⟩ := hr hU hs hB hA hf hg hfp hgp hfi hgi hbf hbg hdiff
  have hB0 := zero_le_one.trans hB
  have hS := sqrtBudget_nonneg m (zero_le_one.trans hD) hB0
  have hR : 0 ≤ rootDifferenceBudget m D B := by unfold rootDifferenceBudget; positivity
  have hleft : 2^m*B*sqrtBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*rootDifferenceBudget m D B := by positivity
    linarith
  have hright : 2^m*B*rootDifferenceBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*sqrtBudget m D B := by positivity
    linarith
  have hfroot := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hgroot := hg.sqrt (fun x hx => (hgp x hx).ne')
  have hfa := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hfroot bF
  have hga := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hgroot bG
  refine ⟨hfa.mono_const (hleft.trans (hpoly B hB).2),
    hga.mono_const (hleft.trans (hpoly B hB).2),?_⟩
  have hda := hbψ.mul_real_dup2 hU hs.le hB0 (mul_nonneg hR hA) hψ (hfroot.sub hgroot) bDiff
  have hsize : 2^m*B*(rootDifferenceBudget m D B*A) ≤ C*B^d*A := by
    calc
      _ = (2^m*B*rootDifferenceBudget m D B)*A := by ring
      _ ≤ C*B^d*A := mul_le_mul_of_nonneg_right (hright.trans (hpoly B hB).2) hA
  apply (hda.mono_const hsize).congr
  intro x hx
  dsimp only [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricFreeBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial budgets for the actual unperturbed free metric modes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_freeSizeFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (N : ℕ → ℝ) (q m : ℕ) :
    c.freeSizeFactor q m (N (m+q+1)) = metricFreeSizeBudget c.C c.J N q m := by
  have hD' : c.D = fun _ => 0 := funext hD
  simp only [freeSizeFactor,metricFreeSizeBudget,tensorOrder_emptyMetricPolynomial,hD']

lemma metric_freeResidualFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (N : ℕ → ℝ) (q m : ℕ) :
    c.freeResidualFactor q m (N (m+q+1)) = metricFreeResidualBudget c.C c.J N q m := by
  have hκ : c.κ = fun r => errorConstant r (c.C r) := by
    funext r
    simp only [κ,hD r,zero_mul,max_eq_left (errorConstant_nonneg r (c.nonnegC r))]
  have hγ : c.freeInitialFactor = fun r => fullErrorConstant 4 r (c.C r) := by
    funext r
    simp only [freeInitialFactor,hD r,zero_mul,
      max_eq_left (fullErrorConstant_nonneg 4 r (c.nonnegC r))]
  simp only [freeResidualFactor,freeChartResidualFactor,metricFreeResidualBudget,hκ,hγ,
    tensorOrder_emptyMetricPolynomial,inputOrder,Nat.zero_add,Nat.mul_one]
  congr 3

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalAmplitude
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial square-root amplitudes for the actual local metric data. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

lemma coefficientBudget_polynomial (m : ℕ) : HasPolynomialBound (coefficientBudget m) := by
  unfold coefficientBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma inputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hi : d.inv m ≤ B) (hf : d.forms m ≤ B) :
    inputFactor d m ≤ coefficientBudget m B := by
  have hI := d.inv_pos m
  have hF := d.forms_pos m
  unfold inputFactor coefficientBudget
  gcongr

theorem polynomial_local_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv m ≤ B → d.forms m ≤ B → d.psi m ≤ B →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s m B A → WeightedBound U s m B A' →
      WeightedBound U s m D (A-A') →
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A)) ∧
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A')) ∧
      WeightedBound V s m (C*B^p*D)
        (fun x => phaseAmplitude ψ (coefficient Q e A) x-phaseAmplitude ψ (coefficient Q e A') x) := by
  obtain ⟨k,C₀,hC₀,hamp⟩ := polynomial_phaseAmplitude_bounds (E := Base) m
  let S := fun B : ℝ => 1+B+coefficientBudget m B*B
  have hSp : HasPolynomialBound S :=
    ((polynomialBound_const zero_le_one).add polynomialBound_id).add
      ((coefficientBudget_polynomial m).mul polynomialBound_id)
  have hpoly : HasPolynomialBound (fun B => C₀*(S B)^k*(1+coefficientBudget m B)) :=
    ((polynomialBound_const (zero_le_one.trans hC₀)).mul (hSp.pow k)).mul
      ((polynomialBound_const zero_le_one).add (coefficientBudget_polynomial m))
  obtain ⟨p,C,hC,hpoly⟩ := hpoly
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hJ : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hS : 1 ≤ S B ∧ B ≤ S B ∧ coefficientBudget m B*B ≤ S B := by
    dsimp [S]
    have hh : 0 ≤ coefficientBudget m B*B := mul_nonneg hJ hB0
    constructor
    · linarith
    constructor <;> linarith
  have hfactor := inputFactor_le_coefficientBudget d m hB hi hf
  have hcoeff (T : Base → Tensor) (hT : ContDiffOn ℝ ∞ T U)
      (hbT : WeightedBound U s m B T) : WeightedBound V s m (S B) (coefficient Q e T) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hB0 h.smoothQ h.smoothInv
      h.invInto hT (d.inv_bound m) (d.forms_bound m) hbT
    exact hh.mono_const ((mul_le_mul_of_nonneg_right hfactor hB0).trans hS.2.2)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hA' (d.inv_bound m) (d.forms_bound m) hbD
  have hdiff' : WeightedBound V s m (coefficientBudget m B*D)
      ((coefficient Q e A)-(coefficient Q e A')) :=
    hdiff.mono_const (mul_le_mul_of_nonneg_right hfactor hD)
  have hpos (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, 0 < coefficient Q e T x :=
    fun x hx => hρ.trans_le (coefficient_trial_range h.invInto h.margin ht hx).1
  have hinv (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, (coefficient Q e T x)⁻¹ ≤ S B := by
    intro x hx
    exact ((inv_le_inv₀ (hpos T ht x hx) hρ).mpr
      (coefficient_trial_range h.invInto h.margin ht hx).1).trans (hρB.trans hS.2.1)
  obtain ⟨ha,ha',hd⟩ := hamp h.domain.isOpen.uniqueDiffOn hs hS.1 (mul_nonneg hJ hD)
    h.smoothPsi (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA')
    (hpos A hball) (hpos A' hball') (hinv A hball) (hinv A' hball')
    ((d.psi_bound m).mono_const (hψ.trans hS.2.1)) (hcoeff A hA hbA) (hcoeff A' hA' hbA') hdiff'
  have hsize := (hpoly B hB).2
  have hbase : C₀*(S B)^k ≤ C*B^p := by
    calc
      _ ≤ C₀*(S B)^k*(1+coefficientBudget m B) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := hsize
  have hdiffsize : C₀*(S B)^k*(coefficientBudget m B*D) ≤ C*B^p*D := by
    calc
      _ ≤ (C₀*(S B)^k*(1+coefficientBudget m B))*D := by
        have hz : 0 ≤ C₀*(S B)^k := by positivity
        nlinarith [mul_nonneg hz hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize hD
  exact ⟨ha.mono_const hbase,ha'.mono_const hbase,hd.mono_const hdiffsize⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual supported square-root trial amplitude. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

 theorem polynomial_trial_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < (s : ℝ) → s ≤ 1 → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv m ≤ B → d.budgets.forms m ≤ B → d.budgets.psi m ≤ B →
      ∀ (f g : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ f c.e.source → ContDiffOn ℝ ∞ g c.e.source →
      InTrialBall c.e.source reference r f → InTrialBall c.e.source reference r g →
      WeightedBound c.e.source s m B f → WeightedBound c.e.source s m B g →
      WeightedBound c.e.source s m D (f-g) →
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ f) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ g) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m
        (d.amplitude hρ f-d.amplitude hρ g) ≤ C*B^p*D := by
  obtain ⟨p,C,hC,hamp⟩ := polynomial_local_amplitude_bounds m
  refine ⟨p,C,hC,?_⟩
  intro n P ε τ G hG φ K s c r ρ R reference d hρ hs hs1 B hB hρB hi hf hp f g D hD
    hfs hgs hfb hgb hbf hbg hdiff
  obtain ⟨hu,hv,hd⟩ := hamp d.localBounds d.budgets hs hs1 hρ B hB hρB hi hf hp
    f g D hD hfs hgs hfb hgb hbf hbg hdiff
  have hef : (d.amplitude hρ f : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm f) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hfs hfb)
  have heg : (d.amplitude hρ g : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm g) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hgs hgb)
  have hC0 : 0 ≤ C*B^p := mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hB) _)
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  have hb1 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ f) := by
    simpa only [hef] using hu
  have hb2 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ g) := by
    simpa only [heg] using hv
  have hb3 : WeightedBound c.e.target s m (C*B^p*D) (d.amplitude hρ f-d.amplitude hρ g) := by
    change WeightedBound c.e.target s m _ (fun x => d.amplitude hρ f x-d.amplitude hρ g x)
    simpa only [hef,heg] using hd
  exact ⟨supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb1.extend_support c.e.open_target ((d.amplitude hρ f).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb2.extend_support c.e.open_target ((d.amplitude hρ g).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs (mul_nonneg hC0 hD) _
      (hb3.extend_support c.e.open_target
        ((d.amplitude hρ f-d.amplitude hρ g).tsupport_subset.trans hsp) (mul_nonneg hC0 hD))⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialChartedFree
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual free displacements with polynomial geometric and input budgets. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_charted_free_bounds (q m : ℕ) :
    ∃ p : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      (∀ j, c.D j = 0) → ∀ hρ : 0 < ρ,
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv (m+q+1) ≤ B → d.budgets.forms (m+q+1) ≤ B →
      d.budgets.psi (m+q+1) ≤ B →
      ∀ N : ℕ → ℝ, (∀ j, 0 ≤ N j) → d.budgets.normal (m+q+1) ≤ N (m+q+1) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ f : SmallModes.Base → Tensor,
      ContDiff ℝ ∞ f → InTrialBall univ reference r f →
      WeightedBound univ s (m+q+1) B f →
      WeightedBound univ τ m
        (metricFreeSizeBudget c.C c.J N q m*(A*B^p)*(δ*τ))
        (d.displacement hρ δ q f) ∧
      WeightedBound univ τ m
        ((τ/s)^(q+1)*metricFreeResidualBudget c.C c.J N q m*(A*B^p)*(δ*τ))
        (coordinateFullLinearized emptyMetricPolynomial 0 G (d.displacement hρ δ q f)) := by
  obtain ⟨p,A,hA,hamp⟩ := polynomial_trial_amplitude_bounds (m+q+1)
  refine ⟨p,A,hA,?_⟩
  intro τ G hG φ K s c r ρ R reference d hD hρ hτ hs hτs hs1 B hB hρB hi hf hp N hN hn δ hδ f hfs hfb hbf
  have hz : WeightedBound c.e.source s (m+q+1) 0 (f-f) := by
    apply (weightedBound_zero c.e.source s (m+q+1) (F := Tensor)).congr
    intro x _
    exact sub_self (f x)
  have hball : InTrialBall c.e.source reference r f := fun x _ => hfb x (mem_univ x)
  have ha := (hamp d hρ hs hs1 B hB hρB hi hf hp f f 0 le_rfl hfs.contDiffOn hfs.contDiffOn
    hball hball (hbf.restrict_open c.e.open_source) (hbf.restrict_open c.e.open_source) hz).1
  have hj : PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m = m+q+1 := by
    simp only [PolynomialSolveData.inputOrder,tensorOrder_emptyMetricPolynomial,Nat.zero_add,Nat.mul_one]
    omega
  have ha' : supportedWeightedSeminorm c.chartCompact s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (d.amplitude hρ f) ≤ A*B^p := by
    simpa only [hj] using ha
  have hn' : WeightedBound c.e.target s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (N (m+q+1)) (freeNormal c.realMap) := by
    rw [hj]
    exact (d.budgets.normal_bound (m+q+1)).mono_const hn
  have hAp : 0 ≤ A*B^p := mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hB) _)
  have hsmall : τ/s + (0 : ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
    simp only [zero_div,add_zero]
    exact (div_le_one₀ hs).mpr hτs
  have hsize := c.freeDisplacement_bound hδ hτ hs hτs hs1 le_rfl hsmall q m
    hAp (hN _) hn' (d.amplitude hρ f) ha'
  have hres := c.freeDisplacement_residual_bound hδ hτ hs hτs hs1 le_rfl q m
    hAp (hN _) hn' (d.amplitude hρ f) ha'
  rw [c.metric_freeSizeFactor_eq hD N q m] at hsize
  rw [c.metric_freeResidualFactor_eq hD N q m] at hres
  exact ⟨hsize,by simpa only [zero_div,add_zero,ChartedMeanData.displacement] using hres⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialChartedFreeFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial free estimates uniform over the number of phase cells. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_charted_free_family (q m : ℕ) :
    ∃ p : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {ι : Type*} [Fintype ι] {τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData emptyMetricPolynomial 0 G hG (φ i) (K i) τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ C J : ℕ → ℝ, (∀ i, (c i).C = C ∧ (c i).J = J ∧ ∀ j, (c i).D j = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i, (d i).budgets.inv (m+q+1) ≤ B ∧ (d i).budgets.forms (m+q+1) ≤ B ∧
        (d i).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ j, 0 ≤ N j) →
      (∀ i, (d i).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ f : SmallModes.Base → Tensor,
      ContDiff ℝ ∞ f → InTrialBall univ reference r f →
      WeightedBound univ s (m+q+1) B f →
      WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ))
        (chartedFreeSum d hρ δ q f) ∧
      WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*(τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
        (coordinateFullLinearized emptyMetricPolynomial 0 G (chartedFreeSum d hρ δ q f)) := by
  classical
  obtain ⟨p,A,hA,hfree⟩ := polynomial_charted_free_bounds q m
  refine ⟨p,A,hA,?_⟩
  intro ι _ τ G hG φ K s c r ρ R reference d C J hc hρ hτ hs hτs hs1 B hB hρB hb N hN hn δ hδ f hfs hfb hbf
  have hi (i : ι) := hfree (d i) (hc i).2.2 hρ hτ hs hτs hs1 B hB hρB
    (hb i).1 (hb i).2.1 (hb i).2.2 N hN (hn i) δ hδ f hfs hfb hbf
  have hsize (i : ι) : WeightedBound univ τ m
      (metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ)) ((d i).displacement hρ δ q f) := by
    simpa only [(hc i).1,(hc i).2.1] using (hi i).1
  have hres (i : ι) : WeightedBound univ τ m
      ((τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
      (coordinateFullLinearized emptyMetricPolynomial 0 G ((d i).displacement hρ δ q f)) := by
    simpa only [(hc i).1,(hc i).2.1] using (hi i).2
  rw [chartedFreeSum_eq]
  constructor
  · have hh := WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun _ : ι => metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ))
      (fun i => (d i).displacement hρ δ q f)
      (fun i _ => ((d i).displacement_smooth_support hρ δ q f).1.contDiffOn)
      (fun i _ => hsize i)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  · rw [coordinateFullLinearized_sum emptyMetricPolynomial 0 G Finset.univ _
      (fun i => ((d i).displacement_smooth_support hρ δ q f).1)]
    have hh := WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun _ : ι => (τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
      (fun i => coordinateFullLinearized emptyMetricPolynomial 0 G ((d i).displacement hρ δ q f))
      (fun i _ => (coordinateFullLinearized_smooth (c i).openO (c i).openU emptyMetricPolynomial
        (c i).smoothP hG (c i).mapsG (K i) (c i).supportU
        ((d i).displacement_smooth_support hρ δ q f).1
        ((d i).displacement_smooth_support hρ δ q f).2 0).contDiffOn)
      (fun i _ => hres i)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasFree
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas polynomial free bounds for variable finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberSpace
local instance polynomialAtlasFreeDualAdd_r6fc90c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberNormed
local instance polynomialAtlasFreeSectionNormed_r6fc90c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasFreeSectionSpace_r6fc90c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_free_oai (q m : ℕ) :
    ∃ (p : ℕ) (E Dv Dt : ℝ), 1 ≤ E ∧ 0 ≤ Dv ∧ 0 ≤ Dt ∧
    ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)], ∀ n : ℕ,
      (∀ i, Fintype.card (ι i) ≤ n) →
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      ∀ C J : ℕ → ℝ,
      (∀ i j, (c i j).C = C ∧ (c i j).J = J ∧ ∀ k, (c i j).D k = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i j, (d i j).budgets.inv (m+q+1) ≤ B ∧ (d i j).budgets.forms (m+q+1) ≤ B ∧
        (d i j).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ k, 0 ≤ N k) →
      (∀ i j, (d i j).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i, WeightedEstimates.WeightedBound univ s (m+q+1) B (A.tensorPlaneRead i u)) →
      A.WeightedBound τ m
        (Dv*(n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
        (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
      A.TensorWeightedBound τ m
        (Dt*(n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u)) := by
  classical
  obtain ⟨p,E,hE,hfree⟩ := polynomial_charted_free_family q m
  obtain ⟨Dv,hDv,hv⟩ := A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  obtain ⟨Dt,hDt,ht⟩ := A.tensorPlaneRestore_bound m
  refine ⟨p,E,Dv,Dt,hE,hDv,hDt,?_⟩
  intro ι _ n hn F hF φ K τ s c r ρ R reference d C J hc hρ hτ hs hτs hs1 hK B hB hρB hb N hN hnormal δ hδ u hu hball hbu
  let f := fun i => chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u)
  have hf (i) : ContDiff ℝ ∞ (f i) := (chartedFreeSum_smooth_support (d i) hρ δ q _).1
  have hsp (i) : tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp ((chartedFreeSum_smooth_support (d i) hρ δ q _).2 hx)
    exact hK i j hj
  have hi (i) := hfree (d i) C J (hc i) hρ hτ hs hτs hs1 B hB hρB (hb i) N hN (hnormal i)
    δ hδ (A.tensorPlaneRead i u) (A.tensorPlaneRead_smooth i hu) (hball i) (hbu i)
  have hn' (i) : (Fintype.card (ι i) : ℝ) ≤ n := Nat.cast_le.mpr (hn i)
  have hEB : 0 ≤ E*B^p := mul_nonneg (zero_le_one.trans hE) (pow_nonneg (zero_le_one.trans hB) _)
  have hdt : 0 ≤ δ*τ := mul_nonneg hδ hτ.le
  have hη : 0 ≤ (τ/s)^(q+1) := pow_nonneg (div_nonneg hτ.le hs.le) _
  have hsize (i) : WeightedEstimates.WeightedBound univ τ m
      ((n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ)) (f i) := by
    apply (hi i).1.mono_const
    apply mul_le_mul_of_nonneg_right _ hdt
    apply mul_le_mul_of_nonneg_right _ hEB
    calc
      _ ≤ (Fintype.card (ι i) : ℝ)*max 1 (metricFreeSizeBudget C J N q m) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hn' i) (zero_le_one.trans (le_max_left _ _))
  have hres (i) : WeightedEstimates.WeightedBound univ τ m
      ((n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
      (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i)) := by
    have hh := (hi i).2
    simp only [coordinateFullLinearized_unperturbed,A.jetChartMap_plane] at hh
    apply hh.mono_const
    apply mul_le_mul_of_nonneg_right _ hdt
    apply mul_le_mul_of_nonneg_right _ hEB
    calc
      _ ≤ (Fintype.card (ι i) : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) hη)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hn' i) hη)
        (zero_le_one.trans (le_max_left _ _))
  rw [A.finiteAtlasFreeOscillation_eq_restore d hρ δ q u hK]
  constructor
  · have hh := hv f τ ((n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
      hτ (hτs.trans hs1) (by positivity) hf hsize
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [A.euclidean_vectorPlaneRestore_linearized hF f hf hsp]
    have hh := ht _ τ ((n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
      hτ (hτs.trans hs1) (by positivity)
      (fun i => contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
        (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn (hf i).contDiffOn)) hres
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free_oai.{u_1, u_2}
