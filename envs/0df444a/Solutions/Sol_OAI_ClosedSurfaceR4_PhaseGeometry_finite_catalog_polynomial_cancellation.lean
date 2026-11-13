-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:29:26.882819+00:00
-- url     : https://prove2.me/submissions/204c96c6-68dd-423d-9910-cf0b35bd5049

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
import Definitions.Def_OAIQ249SI007
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_exists_solution
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_nonlinear_unperturbed_solver

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
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

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
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

lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
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

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

lemma continuous_gramDet_field {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have hx := (contDiff_real_coordDeriv hF dx).continuous
  have hy := (contDiff_real_coordDeriv hF dy).continuous
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma good_eventually {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} {p : X}
    (hB : ContinuousAt B p) (hξ : ContinuousAt ξ p) (hg : Good (B p) (ξ p)) :
    ∀ᶠ q in 𝓝 p, Good (B q) (ξ q) := by
  have ho : IsOpen {z : (Fin 3 → RVec n) × Base | Good z.1 z.2} :=
    isOpen_good continuous_fst continuous_snd
  exact (hB.prodMk hξ).preimage_mem_nhds (ho.mem_nhds hg)




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
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

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LengthMargins
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
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


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
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

lemma WeightedBound.indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    WeightedBound univ s m C (U.indicator f) := by
  classical
  apply WeightedBound.extend_support hU ((tsupport_indicator_subset hK hz).trans hKU) hC
  apply hb.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PullbackBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)
open ClosedSurfaceR4.QuadraticMean (weighted_real_complex)

lemma weighted_base_fst {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).1) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.fst ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))

lemma weighted_base_snd {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).2) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.snd ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))

lemma weighted_complexEvaluate {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → ComplexTensor} {v w : Base → Base} {s C D B : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hbA : WeightedBound U s m C A) (hbv : WeightedBound U s m D v)
    (hbw : WeightedBound U s m B w) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * B))
      (fun p => complexEvaluate (A p) (v p) (w p)) := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have hvcB := weighted_real_complex hU hs hD hv.fst (weighted_base_fst hU hs hD hv hbv)
  have hvdB := weighted_real_complex hU hs hD hv.snd (weighted_base_snd hU hs hD hv hbv)
  have hwcB := weighted_real_complex hU hs hB hw.fst (weighted_base_fst hU hs hB hw hbw)
  have hwdB := weighted_real_complex hU hs hB hw.snd (weighted_base_snd hU hs hB hw hbw)
  have h0s := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1s := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2s := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  have h0 := ((hbA.component hU hs hC hA 0).mul hU hs hC hD
    (contDiffOn_pi.mp hA 0) hvc hvcB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 0).mul hvc) hwc hwcB
  have h2 := ((hbA.component hU hs hC hA 2).mul hU hs hC hD
    (contDiffOn_pi.mp hA 2) hvd hvdB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 2).mul hvd) hwd hwdB
  have h11 := hvcB.mul hU hs hD hB hvc hwd hwdB
  have h12 := hvdB.mul hU hs hD hB hvd hwc hwcB
  have h1 := (hbA.component hU hs hC hA 1).mul hU hs hC (by positivity)
    (contDiffOn_pi.mp hA 1) ((hvc.mul hwd).add (hvd.mul hwc))
    (h11.add hU hs (hvc.mul hwd) (hvd.mul hwc) h12)
  have hh := (h0.add hU hs h0s h1s h1).add hU hs (h0s.add h1s) h2s h2
  convert hh using 1 <;> first | rfl | ring

lemma weighted_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => complexPullbackField e p (A p)) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    (contDiffOn_pi.mp (contDiffOn_complexPullbackField_apply hU hA he))
  intro i
  exact weighted_complexEvaluate hU.uniqueDiffOn hs.le hC hD hD hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i)) hbA
    (hbe _ (firstDirection_norm i)) (hbe _ (secondDirection_norm i))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DirectionStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma norm_secondQuadratic_le {n : ℕ} (B : Fin 3 → RVec n) (v : Base) :
    ‖secondQuadratic B v‖ ≤ 4*‖B‖*‖v‖^2 := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hq1 : |v.1^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hq2 : |v.2^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hm : |2*v.1*v.2| ≤ 2*‖v‖^2 := by
    simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg v)]
  unfold secondQuadratic
  calc
    _ ≤ (‖v.1^2 • B 0‖+‖(2*v.1*v.2) • B 1‖)+‖v.2^2 • B 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖^2*‖B‖+(2*‖v‖^2)*‖B‖)+‖v‖^2*‖B‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm B 0
      · exact norm_le_pi_norm B 1
      · exact norm_le_pi_norm B 2
    _ = _ := by ring

lemma norm_rotated_covector (ξ : Base) : ‖(-ξ.2,ξ.1)‖ = ‖ξ‖ := by
  simp only [Prod.norm_def,norm_neg]
  exact max_comm _ _




end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DenominatorBounds
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

lemma relative_margin_covector_sq {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε : ℝ} (hB : B ≠ 0)
    (hmargin : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ε ≤ 4*‖ξ‖^2 := by
  have hlen := norm_secondQuadratic_le B (-ξ.2,ξ.1)
  rw [norm_rotated_covector] at hlen
  have hh : ε*‖B‖ ≤ (4*‖ξ‖^2)*‖B‖ := hmargin.trans (by nlinarith [hlen])
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hB)).mp hh



theorem reciprocal_second_length_bound {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hB : b ≤ ‖B‖)
    (hmargin : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ‖secondQuadratic B (-ξ.2,ξ.1)‖⁻¹ ≤ (ε*b)⁻¹ := by
  have hp := (mul_pos hε hb).trans_le ((mul_le_mul_of_nonneg_left hB hε.le).trans hmargin)
  simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hε hb)
    ((mul_le_mul_of_nonneg_left hB hε.le).trans hmargin)



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_UniformMean
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
open ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.RootMean



lemma weighted_coordDeriv_of_jets {U : Set Base} (hU : IsOpen U)
    {f : Base → Base} (hf : ContDiffOn ℝ ∞ f U) {τ D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ j f U p‖ ≤ D) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U τ m D (coordDeriv v f) := by
  have hd : WeightedBound U τ m D (fderivWithin ℝ f U) := by
    intro j hj p hp
    rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hp]
    exact (mul_le_mul_of_nonneg_left (hb (j+1) (by omega) (by omega) p hp)
      (pow_nonneg hτ j)).trans (mul_le_of_le_one_left hD (pow_le_one₀ hτ hτ1))
  have hh := hd.clm_apply_const hU.uniqueDiffOn hτ
    (hf.fderivWithin hU.uniqueDiffOn le_rfl) v
  apply (hh.mono_const (mul_le_of_le_one_left hD hv)).congr
  intro p hp
  simp only [coordDeriv, fderivWithin_of_isOpen hU hp]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhasePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite smooth partitions on the compact set on which a phase correction is
required.  The coefficients have compact support inside the supplied open
phase domains.  These are ordinary partition coefficients, so splitting a
tensor target does not require taking square roots.
-/

noncomputable section

open Set Manifold TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)

/-- A finite open cover of a compact subset of the phase plane admits compactly
supported smooth partition coefficients indexed by that same cover. -/
theorem exists_compact_phase_partition {ι : Type*} [Fintype ι]
    {K : Set Base} (hK : IsCompact K) (U : ι → Set Base)
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    Nonempty (CompactPhasePartition ι K U) := by
  classical
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Base)
  let V : ι → Set Base := fun i => U i ∩ Metric.ball 0 r
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).inter Metric.isOpen_ball
  have hcoverV : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, hi, hr hx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Base))
    hK.isClosed V hV hcoverV
  refine ⟨{
    weight := fun i => ρ i
    smooth := fun i => (ρ i).contMDiff.contDiff
    nonneg := ρ.nonneg
    le_one := ρ.le_one
    compact_support := ?_
    subordinate := fun i x hx => (hρ i hx).1
    sum_eq_one := ?_ }⟩
  · intro i
    apply (isCompact_closedBall (0 : Base) r).of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    exact Metric.ball_subset_closedBall ((hρ i hx).2)
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPhaseChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncritical smooth phase is the first coordinate of a smooth local chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseLinear_phaseDerivative (φ : Base → ℝ) (p : Base) :
    phaseLinear (phaseDerivative φ p) = fderiv ℝ φ p := by
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,phaseLinear_apply,phaseDerivative]
  ring

/-- The chart is globally smooth as a function, and its inverse is smooth on
its target. Later cutoff extensions can make the inverse globally smooth. -/
theorem exists_smooth_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let L := phaseEquiv (phaseDerivative φ p) hp
  let f : Base → Base := fun x => (φ x,(L x).2)
  have hf : ContDiff ℝ ∞ f := hφ.prodMk (contDiff_snd.comp L.contDiff)
  have hφ' : HasFDerivAt φ (phaseLinear (phaseDerivative φ p)) p := by
    rw [phaseLinear_phaseDerivative]
    exact (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hf' : HasFDerivAt f L.toContinuousLinearMap p := by
    have hprod := hφ'.prodMk ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp p L.hasFDerivAt)
    have heq : (phaseLinear (phaseDerivative φ p)).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap) = L.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq] at hprod
    exact hprod
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := {x : Base | IsUnit (fderiv ℝ f x)}
  have hW : IsOpen W := Units.isOpen.preimage (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hpW : p ∈ W := by
    change IsUnit (fderiv ℝ f p)
    rw [hf'.fderiv]
    exact L.toUnit.isUnit
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = f := rfl
  refine ⟨e,?_,?_,?_,?_⟩
  · exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hpW⟩
  · exact fun x => rfl
  · simpa only [he] using hf
  · intro y hy
    have hunit : IsUnit (fderiv ℝ f (e.symm y)) := (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := ContinuousLinearEquiv.ofUnit u
    have hd : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hf.differentiable (by simp) (e.symm y)).hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      exact hu
    exact (e.contDiffAt_symm hy hd (by rw [he]; exact hf.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ExtendedPhaseChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth extensions of local phase coordinates on smaller neighborhoods. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

/-- Shrinking a smooth local chart lets its inverse be represented by an
actual globally smooth function, as needed by the supported mode solver. -/
theorem extend_local_chart_inverse (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {p : Base} (hp : p ∈ e.source) :
    ∃ d : OpenPartialHomeomorph Base Base, p ∈ d.source ∧
      (d : Base → Base) = e ∧ d.source ⊆ e.source ∧ d.target ⊆ e.target ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm := by
  obtain ⟨B,hB,_,_,hEq⟩ := smooth_extension_near e.open_target hi.contMDiffOn (e.map_source hp)
  have hN : {y : Base | B y = e.symm y} ∩ e.target ∈ 𝓝 (e p) :=
    inter_mem hEq (e.open_target.mem_nhds (e.map_source hp))
  obtain ⟨V,hV,hVo,hVp⟩ := mem_nhds_iff.mp hN
  have hvEq {y : Base} (hy : y ∈ V) : B y = e.symm y := (hV hy).1
  let d : OpenPartialHomeomorph Base Base := {
    toFun := e
    invFun := B
    source := e.source ∩ e ⁻¹' V
    target := e.target ∩ V
    map_source' := fun x hx => ⟨e.map_source hx.1,hx.2⟩
    map_target' := by
      intro y hy
      rw [hvEq hy.2]
      refine ⟨e.map_target hy.1,?_⟩
      change e (e.symm y) ∈ V
      simpa only [e.right_inv hy.1] using hy.2
    left_inv' := by
      intro x hx
      rw [hvEq hx.2]
      exact e.left_inv hx.1
    right_inv' := by
      intro y hy
      rw [hvEq hy.2]
      exact e.right_inv hy.1
    open_source := e.open_source.inter (hVo.preimage he.continuous)
    open_target := e.open_target.inter hVo
    continuousOn_toFun := he.continuous.continuousOn
    continuousOn_invFun := hB.contDiff.continuous.continuousOn
  }
  exact ⟨d,⟨hp,hVp⟩,rfl,fun _ h => h.1,fun _ h => h.1,he,hB.contDiff⟩

/-- Every noncritical phase admits the globally smooth representatives used
by local polynomial cancellation. This is a geometric construction. -/
theorem exists_extended_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm := by
  obtain ⟨e,hep,hphase,he,hi⟩ := exists_smooth_phase_chart hφ hp
  obtain ⟨d,hdp,hde,_,_,hd,hdi⟩ := extend_local_chart_inverse e he hi hep
  exact ⟨d,hdp,fun x => by rw [hde]; exact hphase x,hd,hdi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FastPhaseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform weighted bounds after substituting the fast circle phase. Local
real lifts keep the constants independent of the number of oscillations. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open_domain {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hb : WeightedBound U s m C f) : WeightedBound V s m C f := by
  intro j hj p hp
  rw [iteratedFDerivWithin_of_isOpen j hV hp]
  have h := hb j hj p (hVU hp)
  rwa [iteratedFDerivWithin_of_isOpen j hU (hVU hp)] at h

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NoncriticalPhaseCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact phase-chart geometry chosen independently of the immersion. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

 theorem exists_noncriticalPhaseChart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ c : NoncriticalPhaseChart φ, p ∈ c.chart.source := by
  obtain ⟨e,hep,hphase,he,hi⟩ := exists_extended_phase_chart hφ hp
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_source p hep
  let V := Metric.ball p (r/2)
  let KE := Metric.closedBall p (r/2)
  have hKE : IsCompact KE := isCompact_closedBall p (r/2)
  let KV := e '' KE
  have hKV : IsCompact KV := hKE.image he.continuous
  let d := e.restrOpen V Metric.isOpen_ball
  refine ⟨⟨d,hphase,he,hi,⟨KE,hKE⟩,⟨KV,hKV⟩,?_,?_⟩,?_⟩
  · intro x hx
    exact Metric.ball_subset_closedBall hx.2
  · intro y hy
    refine ⟨d.symm y,Metric.ball_subset_closedBall (d.map_target hy).2,?_⟩
    exact d.right_inv hy
  · exact ⟨hep,Metric.mem_ball_self (by linarith)⟩

 theorem finite_noncritical_phase_cover {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (hφK : ∀ p ∈ (K : Set Base), phaseDerivative φ p ≠ 0) :
    ∃ (t : Finset K) (c : t → NoncriticalPhaseChart φ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source := by
  classical
  choose c hc using fun p : K => exists_noncriticalPhaseChart hφ (hφK p p.property)
  have hcover : (K : Set Base) ⊆ ⋃ p : K, (c p).chart.source := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hc ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := K.isCompact.elim_finite_subcover (fun p : K => (c p).chart.source)
    (fun p => (c p).chart.open_source) hcover
  refine ⟨t,fun i => c i.val,?_⟩
  intro p hp
  obtain ⟨i,hit,hi⟩ := mem_iUnion₂.mp (ht hp)
  exact mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

lemma HasPolynomialBound.max {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => max (f x) (g x)) := by
  have hfn : ∀ x, 1 ≤ x → 0 ≤ f x := by
    obtain ⟨_,_,_,h⟩ := hf
    exact fun x hx => (h x hx).1
  have hgn : ∀ x, 1 ≤ x → 0 ≤ g x := by
    obtain ⟨_,_,_,h⟩ := hg
    exact fun x hx => (h x hx).1
  exact (hf.add hg).of_le (fun x hx => (hfn x hx).trans (le_max_left _ _))
    (fun x hx => max_le (le_add_of_nonneg_right (hgn x hx)) (le_add_of_nonneg_left (hfn x hx)))

lemma HasPolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialBound (f i)) :
    HasPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialBound_const (show (0:ℝ) ≤ 0 by rfl)
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

lemma HasPolynomialBound.comp {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) (hge : ∀ x, 1 ≤ x → 1 ≤ g x) :
    HasPolynomialBound (fun x => f (g x)) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨e*d,C*D^d,one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD),?_⟩
  intro x hx
  refine ⟨(hf (g x) (hge x hx)).1,?_⟩
  calc
    f (g x) ≤ C*(g x)^d := (hf (g x) (hge x hx)).2
    _ ≤ C*(D*x^e)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hg x hx).1 (hg x hx).2 _) (zero_le_one.trans hC)
    _ = (C*D^d)*x^(e*d) := by rw [mul_pow,pow_mul]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartGeometry
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good phase directions remain good in their actual nonlinear phase charts. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_derivative (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ Base := by
  have hh : e ∘ e.symm =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [← fderiv_comp y (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
    hh.fderiv_eq,fderiv_id]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearPhaseFrameMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Gram and transverse-normal denominators in nonlinear
first-coordinate phase charts. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_det_inv (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (coordDet (fderiv ℝ e.symm y))⁻¹ = coordDet (fderiv ℝ e (e.symm y)) := by
  have hd := congrArg coordDet (inverse_chart_derivative e he hi hy)
  rw [coordDet_comp,coordDet_id] at hd
  have hn : coordDet (fderiv ℝ e.symm y) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hd
    exact zero_ne_one hd
  have hh := congrArg (fun t => t*(coordDet (fderiv ℝ e.symm y))⁻¹) hd
  simpa only [mul_assoc,mul_inv_cancel₀ hn,mul_one,one_mul] using hh.symm

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FixedChartGeometry
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a fixed phase chart preserves its derivative budgets.
Both Jacobian denominators are bounded by the original chart's first jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma coordDet_abs_le_norm (A : Base →L[ℝ] Base) : |coordDet A| ≤ 2*‖A‖^2 := by
  have hx : ‖A dx‖ ≤ ‖A‖ := by simpa [dx] using A.le_opNorm dx
  have hy : ‖A dy‖ ≤ ‖A‖ := by simpa [dy] using A.le_opNorm dy
  have ha := (norm_fst_le (A dx)).trans hx
  have hb := (norm_snd_le (A dx)).trans hx
  have hc := (norm_fst_le (A dy)).trans hy
  have hd := (norm_snd_le (A dy)).trans hy
  simp only [Real.norm_eq_abs] at ha hb hc hd
  calc
    |coordDet A| ≤ |(A dx).1*(A dy).2|+|(A dx).2*(A dy).1| := abs_sub _ _
    _ ≤ ‖A‖*‖A‖+‖A‖*‖A‖ := by rw [abs_mul,abs_mul]; gcongr
    _ = 2*‖A‖^2 := by ring

lemma chart_jacobian_bounds (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {J : ℝ}
    (_hJ : 0 ≤ J)
    (hf : ∀ x ∈ e.source, ‖fderiv ℝ e x‖ ≤ J)
    (hb : ∀ x ∈ e.target, ‖fderiv ℝ e.symm x‖ ≤ J) :
    ∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ 2*J^2 ∧
      ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ 2*J^2 := by
  intro x hx
  constructor
  · exact (coordDet_abs_le_norm _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf x hx) 2)
        (by norm_num))
  · have hh := inverse_chart_det_inv e.symm hi he hx
    change (coordDet (fderiv ℝ e x))⁻¹ = coordDet (fderiv ℝ e.symm (e x)) at hh
    rw [hh,Real.norm_eq_abs]
    exact (coordDet_abs_le_norm _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (hb (e x) (e.map_source hx)) 2) (by norm_num))

lemma restrict_chart_forward_jets (e : OpenPartialHomeomorph Base Base)
    (U : Set Base) (hU : IsOpen U) (J : ℕ → ℝ)
    (hb : ∀ m j, j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m) :
    ∀ m j, j ≤ m → ∀ x ∈ (e.restrOpen U hU).source,
      ‖iteratedFDerivWithin ℝ j (e.restrOpen U hU)
        (e.restrOpen U hU).source x‖ ≤ J m := by
  intro m j hj x hx
  have hh := hb m j hj x hx.1
  rw [iteratedFDerivWithin_of_isOpen j e.open_source hx.1] at hh
  simpa only [OpenPartialHomeomorph.coe_restrOpen,
    iteratedFDerivWithin_of_isOpen j (e.restrOpen U hU).open_source hx] using hh

lemma restrict_chart_inverse_jets (e : OpenPartialHomeomorph Base Base)
    (U : Set Base) (hU : IsOpen U) (J : ℕ → ℝ)
    (hb : ∀ m j, j ≤ m → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ J m) :
    ∀ m j, j ≤ m → ∀ x ∈ (e.restrOpen U hU).target,
      ‖iteratedFDerivWithin ℝ j (e.restrOpen U hU).symm
        (e.restrOpen U hU).target x‖ ≤ J m := by
  intro m j hj x hx
  have hh := hb m j hj x hx.1
  rw [iteratedFDerivWithin_of_isOpen j e.open_target hx.1] at hh
  simpa only [OpenPartialHomeomorph.coe_restrOpen_symm,
    iteratedFDerivWithin_of_isOpen j (e.restrOpen U hU).open_target hx] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseDenominatorNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact-support denominator bound extends to an open phase domain
with a specified factor of two. The domain may depend on the immersion;
the numerical bounds do not. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma continuousAt_phaseNormal {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0) :
    ContinuousAt (fun y => secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)) x := by
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hh : ContinuousAt (fun y : Base => (realSecondTensor F y,
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) x :=
    hb.prodMk (hp.snd.neg.prodMk hp.fst)
  have hc : ContinuousAt (fun z : (Fin 3 → RVec 4) × Base => secondQuadratic z.1 z.2)
      (realSecondTensor F x, (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)) :=
    (continuous_secondQuadratic (n := 4)).continuousAt
  exact hc.comp (f := fun y : Base => (realSecondTensor F y,
    (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) hh

lemma eventually_gram_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (h : ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) :
    ∀ᶠ y in 𝓝 x,
      ‖(NormalFrame.gramDet (coordDeriv dx F y) (coordDeriv dy F y))⁻¹‖ < 2*B := by
  have hc := ((continuous_gramDet_field hF).continuousAt (x := x)).inv₀ hD
  exact hc.norm.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

lemma eventually_normal_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (hn : secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1) ≠ 0)
    (h : ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∀ᶠ y in 𝓝 x, ‖secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖⁻¹ < 2*B := by
  have hc := (continuousAt_phaseNormal hF hφ x hD).norm.inv₀ (norm_ne_zero_iff.mpr hn)
  exact hc.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

theorem phase_denominator_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set Base) {B : ℝ} (hB : 0 < B)
    (hImm : ∀ x ∈ K, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ K, Good (realSecondTensor F x) (phaseDerivative φ x))
    (hgram : ∀ x ∈ K, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B)
    (hnormal : ∀ x ∈ K, ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U,
      Function.Injective (fderiv ℝ F x) ∧ Good (realSecondTensor F x) (phaseDerivative φ x) ∧
      ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
      ‖secondQuadratic (realSecondTensor F x)
        (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B := by
  let S : Set Base := {x | Function.Injective (fderiv ℝ F x) ∧
    Good (realSecondTensor F x) (phaseDerivative φ x) ∧
    ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
    ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B}
  refine ⟨interior S,isOpen_interior,?_,fun x hx => (show x ∈ S from interior_subset hx)⟩
  intro x hx
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ F x) (hImm x hx)
  have hge := eventually_gram_reciprocal_bound hF x hB hD (hgram x hx)
  have hne := eventually_normal_reciprocal_bound hF hφ x hB hD (hgood x hx).2
    (hnormal x hx)
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hgood' := good_eventually hb hp (hgood x hx)
  have hD' := (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hD',hgood',hge,hne] with y hyD hyg hyG hyN
  exact ⟨injective_of_gramDet_ne_zero _ hyD,hyg,hyG.le,hyN.le⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply
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

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

lemma tensorChartPush_bound (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {s : ℝ≥0} {J D : ℝ} {m : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm)) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (tensorChartPush e hi K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm K s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm K s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source).comp_coordinates
    e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ hN hi
    f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  have ht := weighted_complexPullbackField_apply e.open_target hs (by positivity) hD
    (f.contDiff.comp_contDiffOn hi) hi hb hfield
  have hg := ht.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (tensorChartPush_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit terminal derivative orders in finite error profiles. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_terminal (L : ℕ) (K C f : ℕ → ℝ) (j m : ℕ) :
    boundProfile L K (fun r => C r * f (r + L)) j m =
      boundProfile L K C j m * f (m + (j + 1) * L) := by
  induction j generalizing m with
  | zero => simp only [boundProfile, zero_add, one_mul]
  | succ j ih =>
    rw [boundProfile, ih, boundProfile]
    have he : m + L + (j + 1) * L = m + (j + 1 + 1) * L := by ring
    rw [he, mul_assoc]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedForcedSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite forced correction has a scale-independent amplitude
budget. Only the finite number of required input derivatives grows. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma forcedModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) : 0 ≤ forcedModeBudget n L B D q m := by
  apply add_nonneg (initialConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)) _ _

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedSupport
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FixedChartNonlinearSolver
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual nonlinear solvers on a fixed phase chart. Only its open domain is
restricted when the immersed map changes; all coordinate budgets stay fixed. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

lemma fixedChartSolverBudget_polynomial (J : ℕ → ℝ) (B : ℕ → ℝ → ℝ)
    {D : ℝ} (hJ : ∀ m, 0 ≤ J m) (hD : 0 ≤ D)
    (hB : ∀ m, HasPolynomialBound (B m)) (m : ℕ) :
    HasPolynomialBound (fun x => fixedChartSolverBudget J (fun j => B j x) D m) := by
  exact ((((polynomialBound_const zero_le_one).add (hB m)).add
    (polynomialBound_const (hJ (m+3)))).add
      (polynomialBound_const (mul_nonneg (by norm_num) (sq_nonneg (J 1))))).add
        (polynomialBound_const (mul_nonneg (by norm_num) hD))

theorem fixed_chart_nonlinear_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (e : NoncriticalPhaseChart (coordinatePhase φ)),
      (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) →
      (∀ m j, j ≤ m → ∀ x ∈ e.chart.source,
        ‖iteratedFDerivWithin ℝ j e.chart e.chart.source x‖ ≤ J m) →
      (∀ m j, j ≤ m → ∀ x ∈ e.chart.target,
        ‖iteratedFDerivWithin ℝ j e.chart.symm e.chart.target x‖ ≤ J m) →
      ∀ D : ℝ, 1 ≤ D →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (phaseDerivative (coordinatePhase φ) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound e.chart.source 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        (∀ m, c.C m = A m*(fixedChartSolverBudget J B D m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = fixedChartSolverBudget J B D m) ∧
        (∀ m j, j ≤ m → ∀ x ∈ c.e.target,
          ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ J m) := by
  obtain ⟨p,A,hA,hsolve⟩ := polynomial_nonlinear_unperturbed_solver
  refine ⟨p,A,hA,?_⟩
  intro G hG K φ hφ e hKe J hJ hf hi D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  have hF := hG.comp planeCoordinateIsometry.symm.contDiff
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨U,hU,hKU,hgeom⟩ := phase_denominator_neighborhood hF hφ' (modeSupport K)
    (zero_lt_one.trans_le hD) hImm hgood hgram hnormal
  let d := e.chart.restrOpen U hU
  have hd : ContDiff ℝ ∞ d := e.smooth
  have hdi : ContDiff ℝ ∞ d.symm := e.smoothInverse
  have hf' := restrict_chart_forward_jets e.chart U hU J hf
  have hi' := restrict_chart_inverse_jets e.chart U hU J hi
  have hdf (x : SmallModes.Base) (hx : x ∈ e.chart.source) :
      ‖fderiv ℝ e.chart x‖ ≤ J 1 := by
    have hh := hf 1 1 le_rfl x hx
    rwa [iteratedFDerivWithin_of_isOpen 1 e.chart.open_source hx,norm_iteratedFDeriv_one] at hh
  have hdb (x : SmallModes.Base) (hx : x ∈ e.chart.target) :
      ‖fderiv ℝ e.chart.symm x‖ ≤ J 1 := by
    have hh := hi 1 1 le_rfl x hx
    rwa [iteratedFDerivWithin_of_isOpen 1 e.chart.open_target hx,norm_iteratedFDeriv_one] at hh
  have hjac := chart_jacobian_bounds e.chart e.smooth e.smoothInverse
    (zero_le_one.trans (hJ 1)) hdf hdb
  let E := fixedChartSolverBudget J B D
  have heach (m : ℕ) : 1 ≤ E m ∧ B m ≤ E m ∧ J (m+3) ≤ E m ∧
      2*(J 1)^2 ≤ E m ∧ 2*D ≤ E m := by
    have hb0 := zero_le_one.trans (hB m)
    have hj0 := zero_le_one.trans (hJ (m+3))
    have hd0 := zero_le_one.trans hD
    have hs0 := sq_nonneg (J 1)
    dsimp [E,fixedChartSolverBudget]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨c,he,hC,hzero,hcj⟩ := hsolve hG K hφ d hd hdi e.phase
    (fun x hx => ⟨hKe hx,hKU hx⟩)
    (fun x hx => (hgeom x hx.2).1) (fun x hx => (hgeom x hx.2).2.1)
    τ s hs hs1 E (fun m => (heach m).1) (by
      intro m
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · intro j hj
        have hh : WeightedBound d.source 1 j (B m/(s : ℝ)^(j-2))
            (G ∘ planeCoordinateIsometry.symm) := by
          intro k hk x hx
          rw [iteratedFDerivWithin_of_isOpen k d.open_source hx]
          have hv := hFj m j hj k hk x hx.1
          rwa [iteratedFDerivWithin_of_isOpen k e.chart.open_source hx.1] at hv
        exact hh.mono_const (div_le_div_of_nonneg_right (heach m).2.1 (pow_nonneg hs.le _))
      · intro j _ hj x hx
        exact (hf' (m+3) j hj x hx).trans (heach m).2.2.1
      · intro x hx
        exact (hjac x hx.1).2.trans (heach m).2.2.2.1
      · intro x hx
        exact (hjac x hx.1).1.trans (heach m).2.2.2.1
      · intro x hx
        exact (hgeom x hx.2).2.2.1.trans (heach m).2.2.2.2
      · intro x hx
        exact (hgeom x hx.2).2.2.2.trans (heach m).2.2.2.2)
  refine ⟨c,hC,hzero,hcj,?_⟩
  intro m j hj x hx
  rw [he] at hx ⊢
  exact hi' m j hj x hx

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NoncriticalPhaseBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed coordinate budgets on the finite cover of a noncritical phase.
The immersion has no role in selecting these constants. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes WeightedEstimates

theorem noncritical_phase_cover_budgets {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (hφK : ∀ x ∈ (K : Set Base), phaseDerivative φ x ≠ 0) :
    ∃ (t : Finset K) (c : t → NoncriticalPhaseChart φ) (J : ℕ → ℝ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source ∧ (∀ m, 1 ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.source,
        ‖iteratedFDerivWithin ℝ j (c i).chart (c i).chart.source x‖ ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.target,
        ‖iteratedFDerivWithin ℝ j (c i).chart.symm (c i).chart.target x‖ ≤ J m) := by
  classical
  obtain ⟨t,c,hcover⟩ := finite_noncritical_phase_cover hφ K hφK
  choose D hD hd using fun (i : t) m => compact_local_weighted_bound
    (c i).chart.open_source isOpen_univ (c i).sourceCompact.isCompact (c i).sourceBound
    (subset_univ _) (c i).smooth.contDiffOn m
  choose E hE he using fun (i : t) m => compact_local_weighted_bound
    (c i).chart.open_target isOpen_univ (c i).targetCompact.isCompact (c i).targetBound
    (subset_univ _) (c i).smoothInverse.contDiffOn m
  let J := fun m => 1+∑ i : t, (D i m+E i m)
  have hJ (m) : 1 ≤ J m := by
    have hh : 0 ≤ ∑ i : t, (D i m+E i m) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (zero_le_one.trans (hD i m)) (zero_le_one.trans (hE i m)))
    exact le_add_of_nonneg_right hh
  have hDE (i : t) (m) : D i m ≤ J m ∧ E i m ≤ J m := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i : t => D i m+E i m)
      (fun i _ => add_nonneg (zero_le_one.trans (hD i m)) (zero_le_one.trans (hE i m))) (Finset.mem_univ i)
    have hs : D i m+E i m ≤ J m := hh.trans (le_add_of_nonneg_left zero_le_one)
    exact ⟨(le_add_of_nonneg_right (zero_le_one.trans (hE i m))).trans hs,
      (le_add_of_nonneg_left (zero_le_one.trans (hD i m))).trans hs⟩
  refine ⟨t,c,J,hcover,hJ,?_,?_⟩
  · intro i m j hj x hx
    have hh := hd i m 1 zero_le_one le_rfl j hj x hx
    simpa only [one_pow,one_mul] using hh.trans (hDE i m).1
  · intro i m j hj x hx
    have hh := he i m 1 zero_le_one le_rfl j hj x hx
    simpa only [one_pow,one_mul] using hh.trans (hDE i m).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Split an actual smooth compactly supported target using the finite smooth
phase partition.  Every piece is a supported smooth field on a compact subset
of its phase domain, and the sum of the pieces is the original target.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pieceSupport_subset_original (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) ⊆ K := fun _ hx => hx.1

theorem pieceSupport_subset_domain (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) ⊆ U i := fun _ hx => P.subordinate i hx.2

/-- The finite pieces sum to the original target at every point, including
outside the compact set on which the coefficients sum to one. -/
theorem sum_splitSupported_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (x : Base) :
    ∑ i, P.splitSupported A i x = A x := by
  classical
  simp only [splitSupported_apply, ← Finset.sum_smul]
  by_cases hx : x ∈ (K : Set Base)
  · rw [P.sum_eq_one x hx, one_smul]
  · simp only [A.zero_on_compl hx, Pi.zero_apply, smul_zero]

end CompactPhasePartition

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-order bounds for the actual partition split.  A fixed partition has
bounded derivatives of every fixed order.  Consequently the split costs a
constant depending only on that partition and the order, uniformly over all
short scales at most one and linearly in the target seminorm.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

open SmallModes (Base)
open JetPolynomial (SupportedField supportedWeightedSeminorm
  weightedBound_of_supportedSeminorm supportedSeminorm_le_of_weightedBound)
open WeightedEstimates

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

theorem weightSize_nonneg (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) (i : ι) :
    0 ≤ P.weightSize m i := apply_nonneg _ _

theorem weight_weightedBound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : (s : ℝ) ≤ 1) :
    WeightedBound univ s m (P.weightSize m i) (P.weight i) := by
  exact (weightedBound_of_supportedSeminorm (1 : ℝ≥0) m
    (P.supportedWeight i)).shrink_scale s.coe_nonneg hs

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product estimate with the coefficient's explicit derivative size. -/
theorem splitSupported_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      (2 ^ m * P.weightSize m i) * supportedWeightedSeminorm K s m A := by
  have hA := weightedBound_of_supportedSeminorm s m A
  have hprod := (P.weight_weightedBound m i s hs1).smul_real uniqueDiffOn_univ
    s.coe_nonneg (P.weightSize_nonneg m i) (apply_nonneg _ _)
    (P.smooth i).contDiffOn A.contDiff.contDiffOn hA
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (mul_nonneg (by positivity) (P.weightSize_nonneg m i))
      (apply_nonneg _ _)) (P.splitSupported A i) hprod

theorem one_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) :
    1 ≤ P.splitConstant m := by
  have hsum : 0 ≤ ∑ i, 2 ^ m * P.weightSize m i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (P.weightSize_nonneg m i))
  change 1 ≤ 1 + ∑ i, 2 ^ m * P.weightSize m i
  linarith

theorem coefficient_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) : 2 ^ m * P.weightSize m i ≤ P.splitConstant m := by
  classical
  have hi : 2 ^ m * P.weightSize m i ≤ ∑ j, 2 ^ m * P.weightSize m j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (P.weightSize_nonneg m j))
      (Finset.mem_univ i)
  change 2 ^ m * P.weightSize m i ≤ 1 + ∑ j, 2 ^ m * P.weightSize m j
  linarith

/-- The fixed finite partition costs no negative power of the scale. -/
theorem splitSupported_uniform_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      P.splitConstant m * supportedWeightedSeminorm K s m A :=
  (P.splitSupported_bound m i s hs hs1 A).trans
    (mul_le_mul_of_nonneg_right (P.coefficient_le_splitConstant m i) (apply_nonneg _ _))

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMarginCompact
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A relative normal-length margin places every relevant point in a fixed
compact noncritical region, before the immersion or its fast scale is selected. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phaseMarginCompact_noncritical {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) {ε : ℝ} (hε : 0 < ε) {x : Base}
    (hx : x ∈ (phaseMarginCompact hφ K ε : Set Base)) : phaseDerivative φ x ≠ 0 := by
  intro hz
  have hh : ε ≤ 4*‖phaseDerivative φ x‖^2 := hx.2
  rw [hz,norm_zero] at hh
  norm_num at hh
  exact (not_le_of_gt hε) hh

lemma mem_phaseMarginCompact_of_relative_margin {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) {ε : ℝ} {x : Base} (hx : x ∈ (K : Set Base))
    (B : Fin 3 → RVec 4) (hB : B ≠ 0)
    (hm : ε*‖B‖ ≤ ‖secondQuadratic B (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖) :
    x ∈ (phaseMarginCompact hφ K ε : Set Base) :=
  ⟨hx,relative_margin_covector_sq B (phaseDerivative φ x) hB hm⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseSupportCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer compact phase supports between the two plane coordinate conventions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma onModeSupport_seminorm (K : Compacts SmallModes.Base) (s : ℝ≥0)
    (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := E) K) :
    supportedWeightedSeminorm (modeSupport (jetSupport K)) s m (onModeSupport K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      (onModeSupport K f) (weightedBound_of_supportedSeminorm s m f)
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      f (weightedBound_of_supportedSeminorm s m (onModeSupport K f))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FinitePolynomialCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cancellation by the actual polynomial phase solvers. All
summands are constructed with one common accuracy and wavelength. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem finite_polynomial_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ) (K : ι → Compacts Base)
    {τ : ℝ} {s : ℝ≥0} (c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : ∀ i, SupportedField (F := ComplexTensor) (modeSupport (K i))) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧
      tsupport X ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).size (f i) q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).residual (f i) q m)
        (fun x => coordinateFullLinearized P ε G X x +
          ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
  classical
  choose X hsm hsp hb hr using fun i => (c i).exists_solution hτ hs hτs hs1 hε hsmall (f i) q
  refine ⟨(fun p => ∑ i, X i p), ContDiff.sum (fun i _ => hsm i), ?_, ?_, ?_⟩
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
    intro p hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport (fun hx => hn (Set.mem_iUnion.mpr ⟨i, hsp i hx⟩))
  · intro m
    exact WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (hsm i).contDiffOn) (fun i _ => hb i m)
  · intro m
    have he : (fun x => coordinateFullLinearized P ε G (fun p => ∑ i, X i p) x +
        ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x) =
        (fun x => ∑ i, (coordinateFullLinearized P ε G (X i) x +
          QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
      rw [coordinateFullLinearized_sum P ε G Finset.univ X hsm]
      funext x
      exact Finset.sum_add_distrib.symm
    rw [he]
    apply WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => ?_) (fun i _ => hr i m)
    exact ((coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
      (c i).mapsG (K i) (c i).supportU (hsm i) (hsp i) ε).add
      (contDiffOn_univ.mp (RealModes.contDiffOn_displacement
        (((c i).smoothPhase.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
        (f i).contDiff.contDiffOn τ))).contDiffOn

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the finite input norm and the small residual power from the
geometric solver constants. The input order is explicit. -/
noncomputable section
open scoped NNReal ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma sizeFactor_nonneg (q m : ℕ) : 0 ≤ c.sizeFactor q m := by
  have hj : 0 ≤ c.J m := zero_le_one.trans (c.oneLEJ m)
  exact mul_nonneg (mul_nonneg (by positivity)
    (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) c.C c.D c.nonnegC q m)) (pow_nonneg hj _)

lemma κ_nonneg (m : ℕ) : 0 ≤ c.κ m :=
  (SmallModes.errorConstant_nonneg m (c.nonnegC m)).trans (le_max_left _ _)

lemma residualFactor_nonneg (q m : ℕ) : 0 ≤ c.residualFactor q m := by
  exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m
    (zero_le_one.trans (c.oneLEJ m)) (zero_le_one.trans (c.oneLEJ (m + 1)))) (by positivity))
    (FiniteParametrix.boundProfile_nonneg c.κ_nonneg c.κ_nonneg q m)

lemma size_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.size f q m = c.sizeFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold size sizeFactor inputOrder
  ring

lemma residual_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.residual f q m = (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      c.residualFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold residual residualFactor inputOrder
  rw [FiniteParametrix.boundProfile_terminal]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInputNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual tensor input norm of the phase solver. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

theorem norm_le_of_weightedBound (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (I : ℕ → ℝ) (hI : ∀ m, 1 ≤ I m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ c.e.target,
      ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I m)
    (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (f : SupportedField (F := ComplexTensor) (modeSupport K))
    (hb : WeightedBound Set.univ s m C f) :
    c.norm f m ≤ tensorChartBudget m (I m) (I (m + 1)) * C := by
  have hn := supportedSeminorm_le_of_weightedBound hs hC f hb
  have hfield := RealModes.weighted_coordDeriv_of_jets c.e.open_target c.smoothInverse s.coe_nonneg hs1
    (zero_le_one.trans (hI (m + 1))) (hcoords (m + 1))
  have hh := tensorChartPush_bound c.e (modeSupport K) c.supportChart c.smoothInverse hs hs1
    (hI m) (zero_le_one.trans (hI (m + 1))) (hcoords m) hfield f
  exact hh.trans (mul_le_mul_of_nonneg_left hn
    (tensorChartBudget_nonneg m (zero_le_one.trans (hI m)) (zero_le_one.trans (hI (m + 1)))))

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DisplacementSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recombination of phase targets split by a finite partition. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.QuadraticMean

lemma realMode_sum {n : ℕ} {ι : Type*} [Fintype ι] (θ : ℝ) (A : ι → CVec n) :
    realMode θ (∑ i, A i) = ∑ i, realMode θ (A i) := by
  funext k
  simp [realMode,realPart,Finset.mul_sum]

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedSolverFacts
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialModeBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free and forced parametrices have polynomial budgets. These
are the actual constants used by the existing mode estimates. -/
noncomputable section
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem errorConstant_polynomial (m : ℕ) :
    HasPolynomialBound (errorConstant m) := by
  unfold errorConstant reducedConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem amplitudeConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (amplitudeConstant n m) := by
  unfold amplitudeConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem initialConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (initialConstant n m) := by
  unfold initialConstant
  exact ((polynomialBound_const (by positivity)).add
    ((polynomialBound_const (by positivity)).mul polynomialBound_id)).add
      (amplitudeConstant_polynomial n m)

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.FiniteParametrix
open RealModes

theorem boundProfile_polynomial (L : ℕ) (K C : ℕ → ℝ → ℝ)
    (hK : ∀ m, HasPolynomialBound (K m)) (hC : ∀ m, HasPolynomialBound (C m))
    (q m : ℕ) : HasPolynomialBound (fun x => boundProfile L (fun r => K r x) (fun r => C r x) q m) := by
  induction q generalizing m with
  | zero => exact hC m
  | succ q ih => exact (hK m).mul (ih (m+L))

end ClosedSurfaceR4.FiniteParametrix

namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem forcedModeBudget_polynomial (n L : ℕ) (B D : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => forcedModeBudget n L (fun r => B r x) (fun r => D r x) q m) := by
  let κ := fun r x => max (errorConstant r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  have hκ (r : ℕ) : HasPolynomialBound (κ r) :=
    ((errorConstant_polynomial r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hi := (initialConstant_polynomial n m).comp (hB m) (hB1 m)
  have hsum := HasPolynomialBound.sum (Finset.range q)
    (fun i x => initialConstant n m (B m x)*
      FiniteParametrix.boundProfile (L+1) (fun r => κ r x) (fun r => κ r x) i (m+(L+1)))
    (fun i _ => hi.mul (FiniteParametrix.boundProfile_polynomial (L+1) κ κ hκ hκ i (m+(L+1))))
  exact hi.add hsum

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcedBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial constants for the actual supported forced metric solver.
The scale factor in its residual is separated from its geometric budget. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

theorem metricForcedSizeBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricForcedSizeBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have hz : ∀ m : ℕ, HasPolynomialBound (fun _ : ℝ => (0 : ℝ)) :=
    fun _ => polynomialBound_const le_rfl
  exact ((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul
    ((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
      ((forcedModeBudget_polynomial 4 0 C (fun _ _ => 0) hC hz hC1 q m).mul
        (hN (m+q+1))))).mul ((hJ m).pow m)

theorem metricForcedResidualBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricForcedResidualBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have he (r : ℕ) := (errorConstant_polynomial r).comp (hC r) (hC1 r)
  have hb := FiniteParametrix.boundProfile_polynomial 1
    (fun r x => errorConstant r (C r x))
    (fun r x => errorConstant r (C r x)*N (r+1) x) he
    (fun r => (he r).mul (hN (r+1))) q m
  have ht : HasPolynomialBound (fun x => tensorChartBudget m (J m x) (J (m+1) x)) := by
    unfold tensorChartBudget
    exact (polynomialBound_const (show (0 : ℝ) ≤ 4 by norm_num)).mul
      (((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
        (((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
          ((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul ((hJ m).pow m))).mul
            (hJ (m+1)))).mul (hJ (m+1)))
  exact ht.mul ((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul hb)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricForcedFactorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial geometric factors and the number of actual quadratic labels. -/
noncomputable section
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open SmallModes RealModes
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_sizeFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (q m : ℕ) :
    c.sizeFactor q m = metricForcedSizeBudget c.C c.J (fun _ => 1) q m := by
  have hD' : c.D = (fun _ => 0) := funext hD
  simp only [sizeFactor,metricForcedSizeBudget,tensorOrder_emptyMetricPolynomial,hD',mul_one]
  ring

lemma metric_residualFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (q m : ℕ) :
    c.residualFactor q m = metricForcedResidualBudget c.C c.J (fun _ => 1) q m := by
  have hκ : c.κ = fun r => errorConstant r (c.C r) := by
    funext r
    simp only [κ,hD r,zero_mul,max_eq_left (errorConstant_nonneg r (c.nonnegC r))]
  simp only [residualFactor,metricForcedResidualBudget,hκ,tensorOrder_emptyMetricPolynomial,
    Nat.zero_add,mul_one]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitSplitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-chart correction retains explicit coordinate, splitting and
cardinality factors. These factors can be bounded before a fast scale is chosen. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

 theorem explicit_finite_split_cancellation {ι : Type*} [Fintype ι]
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (φ : JetPolynomial.Base → ℝ) (K : Compacts SmallModes.Base)
    (L : ι → Compacts JetPolynomial.Base)
    (T : (i : ι) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)))
    {τ : ℝ} {s : ℝ≥0}
    (c : (i : ι) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hLK : ∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K)
    (C J I S : ℕ → ℝ) (hI : ∀ m, 1 ≤ I m) (hS : ∀ m, 1 ≤ S m)
    (hc : ∀ i, (c i).C = C ∧ (c i).D = (fun _ => 0) ∧ (c i).J = J)
    (hi : ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
      ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I m)
    (hT : ∀ m i A, supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
      S m * supportedWeightedSeminorm K s m A)
    (hsum : ∀ A x, ∑ i, T i A x = A x) (q : ℕ)
    (A : SupportedField (F := ComplexTensor) K) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
      (∀ m, WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*splitSizeBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A) X) ∧
      (∀ m, WeightedBound univ τ m
        ((τ/s)^(q+1)*(Fintype.card ι : ℝ)*splitResidualBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A)
        (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
          QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  have hsmall : τ/s+(0:ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
    simpa only [zero_div,add_zero] using (div_le_one₀ hs).mpr hτs
  obtain ⟨X,hX,hsp,hb,hr⟩ := finite_polynomial_cancellation emptyMetricPolynomial 0 hG
    (fun _ : ι => φ) L c hτ hs hτs hs1 le_rfl hsmall (fun i => T i A) q
  have hn (i : ι) (m : ℕ) : (c i).norm (T i A) m ≤
      (tensorChartBudget m (I m) (I (m+1))*S m)*supportedWeightedSeminorm K s m A := by
    have hh := (c i).norm_le_of_weightedBound hs hs1 I hI (hi i) m
      (mul_nonneg (zero_le_one.trans (hS m)) (apply_nonneg _ _)) (T i A)
      ((weightedBound_of_supportedSeminorm s m (T i A)).mono_const (hT m i A))
    simpa only [mul_assoc] using hh
  have hsize (i : ι) (m : ℕ) : (c i).size (T i A) q m ≤
      splitSizeBudget q m C J I S * supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A := by
    rw [(c i).size_eq_factor]
    calc
      _ ≤ (c i).sizeFactor q m * (splitInputBudget q m I S *
          supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) :=
        mul_le_mul_of_nonneg_left (hn i _) ((c i).sizeFactor_nonneg q m)
      _ ≤ max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) *
          (splitInputBudget q m I S * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) := by
        have hf : (c i).sizeFactor q m ≤
            max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) := by
          rw [(c i).metric_sizeFactor_eq (fun r => congrFun (hc i).2.1 r),
            (hc i).1,(hc i).2.2]
          exact le_max_right _ _
        apply mul_le_mul_of_nonneg_right hf
        exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg _
          (zero_le_one.trans (hI _)) (zero_le_one.trans (hI _)))
            (zero_le_one.trans (hS _))) (apply_nonneg _ _)
      _ = _ := by unfold splitSizeBudget; ring
  have hres (i : ι) (m : ℕ) : (c i).residual (T i A) q m ≤
      (τ/s)^(q+1)*splitResidualBudget q m C J I S * supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A := by
    rw [(c i).residual_eq_factor]
    simp only [zero_div,add_zero]
    calc
      _ ≤ (τ/s)^(q+1)*(c i).residualFactor q m * (splitInputBudget q m I S *
          supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) :=
        mul_le_mul_of_nonneg_left (hn i _) (mul_nonneg
          (pow_nonneg (div_nonneg hτ.le hs.le) _) ((c i).residualFactor_nonneg q m))
      _ ≤ (τ/s)^(q+1)*max 1 (metricForcedResidualBudget C J (fun _ => 1) q m) *
          (splitInputBudget q m I S * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg hτ.le hs.le) _)
          rw [(c i).metric_residualFactor_eq (fun r => congrFun (hc i).2.1 r),
            (hc i).1,(hc i).2.2]
          exact le_max_right _ _
        · exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg _
            (zero_le_one.trans (hI _)) (zero_le_one.trans (hI _)))
              (zero_le_one.trans (hS _))) (apply_nonneg _ _)
      _ = _ := by unfold splitResidualBudget; ring
  have hdisp (x : SmallModes.Base) :
      ∑ i, QuadraticMean.displacement τ (coordinatePhase φ) (T i A) x =
        QuadraticMean.displacement τ (coordinatePhase φ) A x := by
    simp only [QuadraticMean.displacement]
    rw [← QuadraticMean.realMode_sum,hsum A x]
  refine ⟨X,hX,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hsp hx)
    exact hLK i hi
  · intro m
    apply (hb m).mono_const
    calc
      _ ≤ ∑ _i : ι, splitSizeBudget q m C J I S * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A :=
        Finset.sum_le_sum (fun i _ => hsize i m)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] <;> ring
  · intro m
    have hsumres : (∑ i, (c i).residual (T i A) q m) ≤
        (τ/s)^(q+1)*(Fintype.card ι : ℝ)*splitResidualBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A := by
      calc
        _ ≤ ∑ _i : ι, (τ/s)^(q+1)*splitResidualBudget q m C J I S *
            supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
              (P := emptyMetricPolynomial) q m) A :=
          Finset.sum_le_sum (fun i _ => hres i m)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] <;> ring
    simpa only [coordinateFullLinearized_unperturbed,hdisp,Pi.add_def] using
      (hr m).mono_const hsumres

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSplitBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit finite-chart constants have polynomial dependence on the
coordinate and splitting profiles. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation RealModes

lemma tensorChartBudget_polynomial (m : ℕ) (I J : ℝ → ℝ)
    (hI : HasPolynomialBound I) (hJ : HasPolynomialBound J) :
    HasPolynomialBound (fun x => tensorChartBudget m (I x) (J x)) := by
  unfold tensorChartBudget
  repeat first
    | exact hI
    | exact hJ
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

lemma splitInputBudget_polynomial (q m : ℕ) (I S : ℕ → ℝ → ℝ)
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j)) :
    HasPolynomialBound (fun x => splitInputBudget q m (fun j => I j x) (fun j => S j x)) := by
  unfold splitInputBudget
  exact (tensorChartBudget_polynomial _ _ _ (hI _) (hI _)).mul (hS _)

lemma splitSizeBudget_polynomial (q m : ℕ) (C J I S : ℕ → ℝ → ℝ)
    (hC : ∀ j, HasPolynomialBound (C j)) (hJ : ∀ j, HasPolynomialBound (J j))
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j))
    (hC1 : ∀ j x, 1 ≤ x → 1 ≤ C j x) :
    HasPolynomialBound (fun x => splitSizeBudget q m
      (fun j => C j x) (fun j => J j x) (fun j => I j x) (fun j => S j x)) := by
  exact ((polynomialBound_const zero_le_one).max
    (metricForcedSizeBudget_polynomial C J (fun _ _ => 1) hC hJ
      (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
        (splitInputBudget_polynomial q m I S hI hS)

lemma splitResidualBudget_polynomial (q m : ℕ) (C J I S : ℕ → ℝ → ℝ)
    (hC : ∀ j, HasPolynomialBound (C j)) (hJ : ∀ j, HasPolynomialBound (J j))
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j))
    (hC1 : ∀ j x, 1 ≤ x → 1 ≤ C j x) :
    HasPolynomialBound (fun x => splitResidualBudget q m
      (fun j => C j x) (fun j => J j x) (fun j => I j x) (fun j => S j x)) := by
  exact ((polynomialBound_const zero_le_one).max
    (metricForcedResidualBudget_polynomial C J (fun _ _ => 1) hC hJ
      (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
        (splitInputBudget_polynomial q m I S hI hS)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FixedCompactSolverFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed noncritical phase cover supplies actual polynomially controlled
solvers for every smaller good target support. The cover and split constants
are selected before the immersion, scales, and target. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem fixed_compact_polynomial_solver_family
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    (hnoncritical : ∀ x ∈ (K₀ : Set SmallModes.Base),
      phaseDerivative (coordinatePhase φ) x ≠ 0) :
    ∃ (t : Finset K₀) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      ∀ D : ℝ, 1 ≤ D →
      (∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (phaseDerivative (coordinatePhase φ) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∃ (L : t → Compacts JetPolynomial.Base)
        (T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
          SupportedField (F := ComplexTensor) (modeSupport (L i)))
        (c : (i : t) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) τ s),
        (∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K) ∧
        (∀ i m, (c i).C m = A m*(fixedChartSolverBudget J B D m)^(p m)) ∧
        (∀ i m, (c i).D m = 0) ∧
        (∀ i m, (c i).J m = fixedChartSolverBudget J B D m) ∧
        (∀ i m j, j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ J m) ∧
        (∀ m i f, supportedWeightedSeminorm (modeSupport (L i)) s m (T i f) ≤
          S m * supportedWeightedSeminorm K s m f) ∧
        (∀ f x, ∑ i, T i f x = f x) := by
  classical
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨t,e,J,hcover,hJ,hf,hi⟩ := noncritical_phase_cover_budgets hφ' K₀ hnoncritical
  obtain ⟨P⟩ := PhasePartitions.exists_compact_phase_partition K₀.isCompact
    (fun i : t => (e i).chart.source) (fun i => (e i).chart.open_source) hcover
  obtain ⟨p,A,hA,hsolver⟩ := fixed_chart_nonlinear_solver
  refine ⟨t,J,P.splitConstant,p,A,hJ,P.one_le_splitConstant,hA,?_⟩
  intro G hG K hK D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  let Q : PhasePartitions.CompactPhasePartition t (K : Set SmallModes.Base)
      (fun i => (e i).chart.source) := P.restrictTarget K hK
  let L : t → Compacts JetPolynomial.Base := fun i => jetSupport (Q.pieceSupport i)
  let T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)) :=
    fun i => (onModeSupportLM (Q.pieceSupport i)).comp (Q.splitSupportedLM i)
  have hLK (i : t) : (modeSupport (L i) : Set SmallModes.Base) ⊆ K := by
    simpa only [L,modeSupport_jetSupport] using Q.pieceSupport_subset_original i
  have hLe (i : t) : (modeSupport (L i) : Set SmallModes.Base) ⊆ (e i).chart.source := by
    simpa only [L,modeSupport_jetSupport] using Q.pieceSupport_subset_domain i
  have hc (i : t) := hsolver hG (L i) hφ (e i) (hLe i) J hJ (hf i) (hi i) D hD
    (fun x hx => hImm x (hLK i hx)) (fun x hx => hgood x (hLK i hx))
    (fun x hx => hgram x (hLK i hx)) (fun x hx => hnormal x (hLK i hx))
    τ s hs hs1 B hB (fun m j hj => (hFj m j hj).restrict_open_domain
      isOpen_univ (e i).chart.open_source (subset_univ _))
  choose c hC hzero hCJ hInv using hc
  refine ⟨L,T,c,hLK,hC,hzero,hCJ,hInv,?_,?_⟩
  · intro m i f
    change supportedWeightedSeminorm (modeSupport (jetSupport (Q.pieceSupport i))) s m
      (onModeSupport (Q.pieceSupport i) (Q.splitSupported f i)) ≤ _
    rw [onModeSupport_seminorm _ s hs]
    exact Q.splitSupported_uniform_bound m i s hs hs1 f
  · intro f x
    exact Q.sum_splitSupported_apply f x

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FixedCompactCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-loss cancellation on a fixed compact noncritical region, with
polynomial geometric factors and an actual, support-preserving solution. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem fixed_compact_polynomial_cancellation
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    (hnoncritical : ∀ x ∈ (K₀ : Set SmallModes.Base),
      phaseDerivative (coordinatePhase φ) x ≠ 0) :
    ∃ (N : ℕ) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      ∀ D : ℝ, 1 ≤ D →
      (∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (phaseDerivative (coordinatePhase φ) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ q : ℕ, ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          ((N : ℝ)*splitSizeBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(N : ℝ)*splitResidualBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) f)) := by
  obtain ⟨t,J,S,p,A,hJ,hS,hA,hfamily⟩ :=
    fixed_compact_polynomial_solver_family hφ K₀ hnoncritical
  refine ⟨Fintype.card t,J,S,p,A,hJ,hS,hA,?_⟩
  intro G hG K hK D hD hImm hgood hgram hnormal τ s hτ hs hτs hs1 B hB hFj q f
  obtain ⟨L,T,c,hLK,hC,hzero,hCJ,hi,hT,hsum⟩ :=
    hfamily hG K hK D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  exact explicit_finite_split_cancellation hG φ K L T c hτ hs hτs hs1 hLK
    (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
    (fixedChartSolverBudget J B D) J S hJ hS
    (fun i => ⟨funext (hC i),funext (hzero i),funext (hCJ i)⟩)
    (fun i m j _ hj => hi i m j hj) hT hsum q f

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RelativePhaseCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative phase margins supply the fixed compact noncritical region and
the explicit normal denominator needed by the actual cancellation theorem. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem relative_phase_polynomial_cancellation
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ (N : ℕ) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      ∀ D : ℝ, 1 ≤ D → (ε*b)⁻¹ ≤ D →
      (∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        b ≤ ‖RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x‖) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ε*‖RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x‖ ≤
          ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
            (-(phaseDerivative (coordinatePhase φ) x).2,
              (phaseDerivative (coordinatePhase φ) x).1)‖) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ q : ℕ, ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          ((N : ℝ)*splitSizeBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(N : ℝ)*splitResidualBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) f)) := by
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨N,J,S,p,A,hJ,hS,hA,hcancel⟩ := fixed_compact_polynomial_cancellation hφ
    (phaseMarginCompact hφ' K₀ ε)
    (fun x hx => phaseMarginCompact_noncritical hφ' K₀ hε hx)
  refine ⟨N,J,S,p,A,hJ,hS,hA,?_⟩
  intro G hG K hK D hD hDB hImm hB hrel hgram τ s hτ hs hτs hs1 B hBP hFj q f
  have hn (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hB x hx))
  have hKK : (K : Set SmallModes.Base) ⊆ phaseMarginCompact hφ' K₀ ε := by
    intro x hx
    exact mem_phaseMarginCompact_of_relative_margin hφ' K₀ (hK hx) _ (hn x hx) (hrel x hx)
  have hgood (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x) :=
    good_of_direction_length_pos _ _ ((mul_pos hε (hb.trans_le (hB x hx))).trans_le (hrel x hx))
  have hnormal (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (-(phaseDerivative (coordinatePhase φ) x).2,
          (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D :=
    (reciprocal_second_length_bound _ _ hε hb (hB x hx) (hrel x hx)).trans hDB
  exact hcancel hG K hKK D hD hImm hgood hgram hnormal τ s hτ hs hτs hs1 B hBP hFj q f

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFixedCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial closure for the complete fixed-cover cancellation constants. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseGeometry
open RealModes JetPolynomial JetPolynomial.Perturbation

lemma fixed_cancellation_budgets_polynomial (N q m : ℕ)
    (J S A : ℕ → ℝ) (p : ℕ → ℕ) (B : ℕ → ℝ → ℝ) {D : ℝ}
    (hJ : ∀ r, 1 ≤ J r) (hS : ∀ r, 1 ≤ S r) (hA : ∀ r, 1 ≤ A r) (hD : 1 ≤ D)
    (hB : ∀ r, HasPolynomialBound (B r)) (hB1 : ∀ r x, 1 ≤ x → 1 ≤ B r x) :
    HasPolynomialBound (fun x => (N : ℝ)*splitSizeBudget q m
      (fun r => A r*(fixedChartSolverBudget J (fun j => B j x) D r)^(p r))
      (fixedChartSolverBudget J (fun j => B j x) D) J S) ∧
    HasPolynomialBound (fun x => (N : ℝ)*splitResidualBudget q m
      (fun r => A r*(fixedChartSolverBudget J (fun j => B j x) D r)^(p r))
      (fixedChartSolverBudget J (fun j => B j x) D) J S) := by
  let E : ℕ → ℝ → ℝ := fun r x => fixedChartSolverBudget J (fun j => B j x) D r
  have hE (r : ℕ) : HasPolynomialBound (E r) :=
    fixedChartSolverBudget_polynomial J B (fun r => zero_le_one.trans (hJ r))
      (zero_le_one.trans hD) hB r
  have hE1 (r : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ E r x := by
    have hb0 := zero_le_one.trans (hB1 r x hx)
    have hj0 := zero_le_one.trans (hJ (r+3))
    have hd0 := zero_le_one.trans hD
    have hs0 := sq_nonneg (J 1)
    dsimp [E,fixedChartSolverBudget]
    linarith
  have hC (r : ℕ) : HasPolynomialBound (fun x => A r*(E r x)^(p r)) :=
    (polynomialBound_const (zero_le_one.trans (hA r))).mul ((hE r).pow (p r))
  have hC1 (r : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ A r*(E r x)^(p r) :=
    one_le_mul_of_one_le_of_one_le (hA r) (one_le_pow₀ (hE1 r x hx))
  have hJp (r : ℕ) : HasPolynomialBound (fun _ : ℝ => J r) :=
    polynomialBound_const (zero_le_one.trans (hJ r))
  have hSp (r : ℕ) : HasPolynomialBound (fun _ : ℝ => S r) :=
    polynomialBound_const (zero_le_one.trans (hS r))
  exact ⟨(polynomialBound_const (Nat.cast_nonneg N)).mul
    (splitSizeBudget_polynomial q m (fun r x => A r*(E r x)^(p r)) E
      (fun r _ => J r) (fun r _ => S r) hC hE hJp hSp hC1),
    (polynomialBound_const (Nat.cast_nonneg N)).mul
    (splitResidualBudget_polynomial q m (fun r x => A r*(E r x)^(p r)) E
      (fun r _ => J r) (fun r _ => S r) hC hE hJp hSp hC1)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteCatalogCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One polynomial bound for all phases in a fixed finite catalog.
The target supports may vary with the immersion and the scale. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes

lemma coordinatePhase_lift (φ : SmallModes.Base → ℝ) :
    coordinatePhase (φ ∘ planeCoordinateIsometry) = φ := by
  funext x
  simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem finite_catalog_polynomial_cancellation_oai
    (Γ : Finset (SmallModes.Base → ℝ)) (hΓ : ∀ φ ∈ Γ, ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base) {ε b D : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B : ℕ → ℝ → ℝ) (hB : ∀ m, HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ x : ℝ, 1 ≤ x → ∀ φ ∈ Γ,
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      (∀ y ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) y)) →
      (∀ y ∈ (K : Set SmallModes.Base), b ≤ ‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
          ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
            (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) y)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) y))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (E m*x^(d m)*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(E m*x^(d m))*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ φ f)) := by
  classical
  have hsmooth (φ : Γ) : ContDiff ℝ ∞ (φ.val ∘ planeCoordinateIsometry) :=
    (hΓ φ.val φ.property).comp planeCoordinateIsometry.contDiff
  choose N J S p A hJ hS hA hc using fun φ : Γ =>
    relative_phase_polynomial_cancellation (hsmooth φ) K₀ hε hb
  let C := fun (φ : Γ) m x => (N φ : ℝ)*splitSizeBudget q m
    (fun r => A φ r*(fixedChartSolverBudget (J φ) (fun j => B j x) D r)^(p φ r))
    (fixedChartSolverBudget (J φ) (fun j => B j x) D) (J φ) (S φ)
  let R := fun (φ : Γ) m x => (N φ : ℝ)*splitResidualBudget q m
    (fun r => A φ r*(fixedChartSolverBudget (J φ) (fun j => B j x) D r)^(p φ r))
    (fixedChartSolverBudget (J φ) (fun j => B j x) D) (J φ) (S φ)
  have hpoly (φ : Γ) (m : ℕ) : HasPolynomialBound (C φ m) ∧ HasPolynomialBound (R φ m) :=
    fixed_cancellation_budgets_polynomial (N φ) q m (J φ) (S φ) (A φ) (p φ) B
      (hJ φ) (hS φ) (hA φ) hD hB hB1
  let H := fun m x => ∑ φ : Γ, (C φ m x+R φ m x)
  have hH (m : ℕ) : HasPolynomialBound (H m) :=
    HasPolynomialBound.sum Finset.univ (fun φ : Γ => fun x => C φ m x+R φ m x)
      (fun φ _ => (hpoly φ m).1.add (hpoly φ m).2)
  choose d E hE hbound using hH
  have hnonneg (φ : Γ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ C φ m x ∧ 0 ≤ R φ m x := by
    obtain ⟨_,_,_,h⟩ := (hpoly φ m).1
    obtain ⟨_,_,_,h'⟩ := (hpoly φ m).2
    exact ⟨(h x hx).1,(h' x hx).1⟩
  have hmajor (φ : Γ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
      C φ m x ≤ E m*x^(d m) ∧ R φ m x ≤ E m*x^(d m) := by
    have hh : C φ m x+R φ m x ≤ H m x :=
      Finset.single_le_sum (fun ψ _ => add_nonneg (hnonneg ψ m x hx).1 (hnonneg ψ m x hx).2)
        (Finset.mem_univ φ)
    exact ⟨((le_add_of_nonneg_right (hnonneg φ m x hx).2).trans hh).trans (hbound m x hx).2,
      ((le_add_of_nonneg_left (hnonneg φ m x hx).1).trans hh).trans (hbound m x hx).2⟩
  refine ⟨d,E,hE,?_⟩
  intro x hx φ hφ G hG K hK hImm hBnorm hrel hgram τ s hτ hs hτs hs1 hFj f
  let γ : Γ := ⟨φ,hφ⟩
  have hrel' : ∀ y ∈ (K : Set SmallModes.Base),
      ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
          (-(phaseDerivative (coordinatePhase (γ.val ∘ planeCoordinateIsometry)) y).2,
            (phaseDerivative (coordinatePhase (γ.val ∘ planeCoordinateIsometry)) y).1)‖ := by
    simpa only [coordinatePhase_lift] using hrel
  obtain ⟨X,hX,hsp,hv,hr⟩ := hc γ hG K hK D hD hDB hImm hBnorm hrel' hgram
    τ s hτ hs hτs hs1 (fun j => B j x) (fun j => hB1 j x hx) hFj q f
  refine ⟨X,hX,hsp,?_,?_⟩
  · intro m
    exact (hv m).mono_const (mul_le_mul_of_nonneg_right (hmajor γ m x hx).1 (apply_nonneg _ _))
  · intro m
    have hh := hr m
    simp only [coordinatePhase_lift] at hh
    apply hh.mono_const
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmajor γ m x hx).2
        (pow_nonneg (div_nonneg hτ.le hs.le) (q+1)))
      (show 0 ≤ supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f from apply_nonneg _ _)
    simpa only [R,mul_assoc] using hm

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation_oai := @OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation_oai
