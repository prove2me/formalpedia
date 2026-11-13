-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:04:39.51567+00:00
-- url     : https://prove2.me/submissions/b9d0f5f8-5410-49d7-95dd-5b9f8f8854da

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_gram_at_source

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-simp] _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
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

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma coordinateInverse_mfderiv_injective (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    Function.Injective (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) := by
  have hxt : x ∈ (coordinateChart p).target := by rwa [coordinateChart_target]
  have hs : coordinateInverse p x ∈ (coordinateChart p).source := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).map_target hxt
  have hi := ((coordinateInverse_smoothOn p) x hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) (coordinateInverse p x) hs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hs)
  have he : coordinateChart p ∘ coordinateInverse p =ᶠ[𝓝 x] id := by
    filter_upwards [(coordinateDomain_open p).mem_nhds hx] with y hy
    change coordinateChart p (coordinateInverse p y) = y
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).right_inv (by rwa [coordinateChart_target])
  have hd : (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) (coordinateInverse p x)).comp
      (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) =
      ContinuousLinearMap.id ℝ SmallModes.Base := by
    rw [← mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp)),
      he.mfderiv_eq,mfderiv_id]
    rfl
  intro v w hv
  have hvw := congrArg (mfderiv planeModel 𝓘(ℝ,SmallModes.Base)
    (coordinateChart p) (coordinateInverse p x)) hv
  have hdv := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L v) hd
  have hdw := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L w) hd
  exact hdv.symm.trans (hvw.trans hdw)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_Main
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold Filter


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem IsSmoothIsometricImmersion.mfderiv_injective {g : SmoothMetric M}
    {F : M → Space} (h : IsSmoothIsometricImmersion M g F) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  intro v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hv : mfderiv planeModel spaceModel F p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hinner := h.2 p (v - w) (v - w)
  rw [hv, inner_zero_left] at hinner
  exact (ne_of_gt (g.pos p (v - w) hne)) hinner.symm



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
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
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasImmersionGeometry
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma coordinateMap_injective_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (q : M) {x : SmallModes.Base} (hx : x ∈ coordinateDomain q) :
    Function.Injective (fderiv ℝ (coordinateMap F q) x) := by
  have hi := ((coordinateInverse_smoothOn q) x hx).contMDiffAt
    ((coordinateDomain_open q).mem_nhds hx)
  have hm := (hF (coordinateInverse q x)).mdifferentiableAt (by simp)
  have hic := hi.mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hm hic
  rw [mfderiv_eq_fderiv] at hd
  have hs : DifferentiableAt ℝ (F ∘ coordinateInverse q) x :=
    (hm.comp x hic).differentiableAt
  change Function.Injective (fderiv ℝ (spaceCoordinates ∘ (F ∘ coordinateInverse q)) x)
  rw [fderiv_comp x spaceCoordinates.differentiableAt hs,spaceCoordinates.fderiv,hd]
  exact spaceCoordinates.injective.comp ((hI _).comp (coordinateInverse_mfderiv_injective q hx))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma normalize_unit {v : Vec} (hv : v ≠ 0) : normalize v ⬝ᵥ normalize v = 1 := by
  have hp := dot_self_pos hv
  have hs : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have heq := Real.sq_sqrt hp.le
  field_simp
  nlinarith [heq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjection
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Project a global ambient field to the normal bundle using the fixed
finite atlas. No orientation or global tangent frame is chosen. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localProjectedNormal_zero (i : A.centers) (F n : M → Space) {x : SmallModes.Base}
    (hx : A.planeWeight i x = 0) : A.localProjectedNormal i F n x = 0 := by
  have hz : A.localizedNormalField i n x = 0 := by
    dsimp [localizedNormalField]
    by_cases hxt : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
    · simp only [planeWeight,chartWeight,Function.comp_apply,indicator_of_mem hxt] at hx
      simp [localize,hxt,hx]
    · simp [localize,hxt]
  simp [localProjectedNormal,hz,realNormalPart]

lemma vectorPlaneRead_fderiv_at_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) =
      (mfderiv planeModel spaceModel F p).comp
        ((mfderiv 𝓘(ℝ,JetPolynomial.Base) planeModel (chart (i : M)).symm
          (chart (i : M) p)).comp planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have hs := A.weight_support i hp
  unfold vectorPlaneRead
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
    planeCoordinateIsometry.symm.differentiableAt]
  simp only [LinearIsometryEquiv.symm_apply_apply,planeCoordinateIsometry.symm.fderiv]
  rw [A.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩,
    fderiv_comp_chart_symm (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M) ((chart (i : M)).map_source hs),
    (chart (i : M)).left_inv hs]
  rfl

lemma vectorPlaneRead_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hn : ∀ p v, inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (n p) = 0)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (u : SmallModes.Base) :
    coordDeriv u (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)) ⬝ᵥ spaceCoordinates (n p) = 0 := by
  rw [coordDeriv,fderiv_comp _ spaceCoordinates.differentiableAt
    ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _),spaceCoordinates.fderiv,
    ContinuousLinearMap.comp_apply,A.vectorPlaneRead_fderiv_at_weight i hF hp]
  change spaceCoordinates (surfaceDifferential F p _) ⬝ᵥ spaceCoordinates (n p) = 0
  rw [spaceCoordinates_dot]
  exact hn p _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealMetricDerivatives
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate metric derivatives needed for the intrinsic Gauss expression.
The third derivatives cancel before any estimate is made. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma real_partial_dot {n : ℕ} {F G : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q ⬝ᵥ G q) p =
      coordDeriv v F p ⬝ᵥ G p+F p ⬝ᵥ coordDeriv v G p := by
  have hf (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hF.hasFDerivAt)
  have hg (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hG.hasFDerivAt)
  have hs := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).fun_mul (hg i)).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.proj_apply] at hs
  unfold coordDeriv dotProduct
  rw [hs]
  simp only [sum_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma real_dot_smooth {n : ℕ} {F G : RField n}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q => F q ⬝ᵥ G q) :=
  ContDiff.sum (fun i _ => (contDiff_pi.mp hF i).mul (contDiff_pi.mp hG i))

lemma realMetric_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d v w : Base) :
    coordDeriv d (realMetric F v w) p =
      coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv w F p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv w F) p :=
  real_partial_dot ((contDiff_real_coordDeriv hF v).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    ((contDiff_real_coordDeriv hF w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) d

lemma realMetric_second_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d e v w : Base) :
    coordDeriv d (coordDeriv e (realMetric F v w)) p =
      coordDeriv d (coordDeriv e (coordDeriv v F)) p ⬝ᵥ coordDeriv w F p+
      coordDeriv e (coordDeriv v F) p ⬝ᵥ coordDeriv d (coordDeriv w F) p+
      (coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv e (coordDeriv w F) p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv e (coordDeriv w F)) p) := by
  have hv := contDiff_real_coordDeriv hF v
  have hw := contDiff_real_coordDeriv hF w
  have hev := contDiff_real_coordDeriv hv e
  have hew := contDiff_real_coordDeriv hw e
  have he : coordDeriv e (realMetric F v w) = fun q =>
      coordDeriv e (coordDeriv v F) q ⬝ᵥ coordDeriv w F q+
      coordDeriv v F q ⬝ᵥ coordDeriv e (coordDeriv w F) q :=
    funext fun q => realMetric_partial hF q e v w
  rw [he,partial_add ((real_dot_smooth hev hw).differentiable (by simp) p)
    ((real_dot_smooth hv hew).differentiable (by simp) p),
    real_partial_dot (hev.differentiable (by simp) p) (hw.differentiable (by simp) p),
    real_partial_dot (hv.differentiable (by simp) p) (hew.differentiable (by simp) p)]

/-- The raw second-derivative Gauss expression only uses second metric jets. -/
theorem raw_gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    coordDeriv dx (coordDeriv dx F) p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p-
      coordDeriv dx (coordDeriv dy F) p ⬝ᵥ coordDeriv dx (coordDeriv dy F) p =
    (2*coordDeriv dx (coordDeriv dy (realMetric F dx dy)) p-
      coordDeriv dy (coordDeriv dy (realMetric F dx dx)) p-
      coordDeriv dx (coordDeriv dx (realMetric F dy dy)) p)/2 := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  have hthird : coordDeriv dy (coordDeriv dx (coordDeriv dy F)) =
      coordDeriv dx (coordDeriv dy (coordDeriv dy F)) :=
    funext fun q => real_second_coordDeriv_comm (contDiff_real_coordDeriv hF dy) q dy dx
  simp only [realMetric_second_partial hF,hcomm,hthird]
  rw [dotProduct_comm (coordDeriv dx (coordDeriv dx (coordDeriv dy F)) p),
    dotProduct_comm (coordDeriv dx (coordDeriv dy (coordDeriv dy F)) p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate Gauss identity, proved from Euclidean derivatives and the
explicit normal projection.  Its right side depends only on the metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame

lemma normalPart_dot_normalPart (X Y U V : RVec 4) (hD : gramDet X Y ≠ 0) :
    realNormalPart X Y U ⬝ᵥ realNormalPart X Y V = U ⬝ᵥ V-
      inverseMetricPair (X ⬝ᵥ X) (X ⬝ᵥ Y) (Y ⬝ᵥ Y)
        (X ⬝ᵥ U) (Y ⬝ᵥ U) (X ⬝ᵥ V) (Y ⬝ᵥ V) := by
  have hperp := realNormalPart_perp X Y U hD
  have hX : realNormalPart X Y U ⬝ᵥ X = 0 := (dotProduct_comm _ _).trans hperp.1
  have hY : realNormalPart X Y U ⬝ᵥ Y = 0 := (dotProduct_comm _ _).trans hperp.2
  have hcut : realNormalPart X Y U ⬝ᵥ realNormalPart X Y V =
      realNormalPart X Y U ⬝ᵥ V := by
    conv_lhs => arg 2; unfold realNormalPart
    simp only [dotProduct_sub,dotProduct_smul,hX,hY,smul_eq_mul,mul_zero,sub_zero]
  rw [hcut]
  simp only [realNormalPart,inverseMetricPair,NormalFrame.gramDet,sub_dotProduct,smul_dotProduct,
    smul_eq_mul]
  ring

theorem gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p-
      realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p =
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  unfold realSecondForm
  rw [normalPart_dot_normalPart _ _ _ _ hD,normalPart_dot_normalPart _ _ _ _ hD]
  unfold coordinateGauss
  rw [← raw_gauss_metric_identity hF p]
  simp only [realMetric_partial hF,hcomm,realMetric,inverseMetricPair,dotProduct_comm]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricGaussInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gauss scalar of an exact realization is fixed by the prescribed metric
in a neighborhood, independent of the choice of immersion. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma coordDeriv_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Base → E} {p : Base} (h : f =ᶠ[𝓝 p] g) (v : Base) :
    coordDeriv v f =ᶠ[𝓝 p] coordDeriv v g :=
  h.fderiv.mono (fun _ he => congrArg (fun L : Base →L[ℝ] E => L v) he)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma contDiffAt_profileNormalPart {J : BoundaryProfile}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ profileNormalPart J := by
  exact contDiffAt_realNormalPart
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 2 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt hJ

lemma contDiffAt_profilePreferred {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profilePreferred J :=
  normalize_smoothAt (contDiffAt_profileNormalPart hJ.1) hJ.2

lemma isOpen_regularBoundaryProfiles : IsOpen regularBoundaryProfiles := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : BoundaryProfile => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_profileNormalPart hJ.1).continuousAt.eventually_ne hJ.2)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjectionBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas projection is a convex sum of the actual pointwise normal
projections. Local exterior estimates therefore pass to the global field. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma localizedNormalField_at_source (i : A.centers) (n : M → Space) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    A.localizedNormalField i n (planeCoordinateIsometry (chart (i : M) p)) =
      (A.weight i p)^2 • spaceCoordinates (n p) := by
  simp [localizedNormalField,localize,(chart (i : M)).map_source hp,
    (chart (i : M)).left_inv hp]

lemma restored_localProjectedNormal (i : A.centers) (F n : M → Space) (p : M) :
    restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ A.localProjectedNormal i F n) ∘ planeCoordinateIsometry) p =
        (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  by_cases hs : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hs,Function.comp_apply]
    by_cases hz : A.weight i p = 0
    · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
          (chart (i : M)).left_inv hs,hz]
      simp [A.localProjectedNormal_zero i F n hx,hz]
    · have hp := subset_tsupport (A.weight i) hz
      rw [A.outer_one i p hp,one_smul,localProjectedNormal,
        A.localizedNormalField_at_source i n hs,(realNormalPart_linear _ _).map_smul,
        map_smul]
      rfl
  · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hp => hs (A.weight_support i hp))
    simp [restore,hs,hz]

lemma projectedNormalField_eq_sum (F n : M → Space) (p : M) :
    A.projectedNormalField F n p =
      ∑ i : A.centers, (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  unfold projectedNormalField vectorPlaneRestore
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact A.restored_localProjectedNormal i F n p

lemma projectedNormalField_sub_eq (F n : M → Space) (p : M) :
    A.projectedNormalField F n p - n p =
      ∑ i : A.centers, (A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p) := by
  rw [A.projectedNormalField_eq_sum]
  simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,A.partition,one_smul]

/-- A local exterior error is not multiplied by the number of atlas
patches: the squared weights add to one. -/
theorem projectedNormalField_sub_bound (F n : M → Space) (p : M) {ε : ℝ}
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ ε) :
    ‖A.projectedNormalField F n p - n p‖ ≤ ε := by
  rw [A.projectedNormalField_sub_eq]
  calc
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : A.centers, (A.weight i p)^2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hz : A.weight i p = 0
      · simp [hz]
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hlocal i hz) (sq_nonneg _)
    _ = ε := by rw [← Finset.sum_mul,A.partition,one_mul]

lemma projectedNormalField_ne_zero (F n : M → Space) (p : M)
    (hn : ‖n p‖ = 1) (hclose : ‖A.projectedNormalField F n p - n p‖ < 1) :
    A.projectedNormalField F n p ≠ 0 := by
  intro hz
  simp [hz,hn] at hclose

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame VelocityFrame

/-- Uniform stability of the unnormalized projection on a compact family
of old tangent frames. This is the estimate used before normalizing the
finite-atlas sum. -/
theorem compact_raw_normal_projection {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {A B n : X → Vec} (hA : Continuous A) (hB : Continuous B) (hn : Continuous n)
    (hD : ∀ x, gramDet (A x) (B x) ≠ 0)
    (hunit : ∀ x, n x ⬝ᵥ n x = 1)
    (hAn : ∀ x, A x ⬝ᵥ n x = 0) (hBn : ∀ x, B x ⬝ᵥ n x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ A' B' : Vec,
      ‖A'-A x‖ < δ → ‖B'-B x‖ < δ →
      gramDet A' B' ≠ 0 ∧ ‖realNormalPart A' B' (n x)-n x‖ < ε := by
  let J : X → BoundaryProfile := fun x => ![A x,B x,n x,0,0]
  have hJ : Continuous J := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hn
    · exact continuous_const
    · exact continuous_const
  have he (x : X) : profileNormalPart (J x) = n x :=
    realNormalPart_of_perp _ _ _ (hAn x) (hBn x)
  have hreg : Set.range J ⊆ regularBoundaryProfiles := by
    rintro _ ⟨x,rfl⟩
    refine ⟨hD x,?_⟩
    rw [he]
    intro hz
    have hh := hunit x
    norm_num [hz] at hh
  have hK := isCompact_range hJ
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open isOpen_regularBoundaryProfiles hreg
  have hc : ContinuousOn profileNormalPart (Metric.cthickening r (Set.range J)) :=
    fun H hH => (contDiffAt_profileNormalPart (hsub hH).1).continuousAt.continuousWithinAt
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.cthickening.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro x A' B' hA' hB'
  let H : BoundaryProfile := ![A',B',n x,0,0]
  have herr : ‖H-J x‖ < min r d := by
    have hbnd : ‖H-J x‖ ≤ max ‖A'-A x‖ ‖B'-B x‖ := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simp [H,J]
      · simp [H,J]
      · simp [H,J]
    exact hbnd.trans_lt (max_lt hA' hB')
  have hH : H ∈ Metric.cthickening r (Set.range J) :=
    Metric.thickening_subset_cthickening r (Set.range J)
      (Metric.mem_thickening_iff.mpr ⟨J x,mem_range_self x,by
        simpa only [dist_eq_norm] using herr.trans_le (min_le_left r d)⟩)
  have hJ' : J x ∈ Metric.cthickening r (Set.range J) :=
    Metric.self_subset_cthickening (Set.range J) (mem_range_self x)
  have hh := hclose H hH (J x) hJ' (by
    simpa only [dist_eq_norm] using herr.trans_le (min_le_right r d))
  refine ⟨(hsub hH).1,?_⟩
  change ‖profileNormalPart H-n x‖ < ε
  simpa only [dist_eq_norm,he] using hh

end ClosedSurfaceR4.GeometryPreservation

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed local good-phase charts persist under a global C2 perturbation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F-G) = A.vectorPlaneRead i F - A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectedNormalLocal
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normalization of the atlas projection on an exterior open set. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_sub_unit_bound {u v : Space} (hu : u ≠ 0) (hv : ‖v‖ = 1) :
    ‖radialNormalize u-v‖ ≤ 2*‖u-v‖ := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he : ‖radialNormalize u-u‖ = |1-‖u‖| := by
    have he : ‖u‖⁻¹ • u-u = (‖u‖⁻¹-1) • u := by rw [sub_smul,one_smul]
    rw [radialNormalize,he,norm_smul,Real.norm_eq_abs]
    calc
      |‖u‖⁻¹-1| *‖u‖ = |(‖u‖⁻¹-1)*‖u‖| := by rw [abs_mul,abs_of_nonneg hn.le]
      _ = |1-‖u‖| := by congr 1; field_simp
  have habs : |1-‖u‖| ≤ ‖u-v‖ := by
    rw [abs_sub_comm,← hv]
    exact abs_norm_sub_norm_le u v
  calc
    ‖radialNormalize u-v‖ ≤ ‖radialNormalize u-u‖+‖u-v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*‖u-v‖ := by rw [he]; linarith

end ClosedSurfaceR4.SphericalJets
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
theorem unitProjectedNormalField_sub_bound {F n : M → Space} {p : M} {δ : ℝ}
    (hn : ‖n p‖ = 1) (hδ : δ < 1)
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ δ) :
    A.projectedNormalField F n p ≠ 0 ∧
      ‖A.unitProjectedNormalField F n p-n p‖ ≤ 2*δ := by
  have hb := A.projectedNormalField_sub_bound F n p hlocal
  have hne := A.projectedNormalField_ne_zero F n p hn (hb.trans_lt hδ)
  exact ⟨hne,(SphericalJets.radialNormalize_sub_unit_bound hne hn).trans
    (mul_le_mul_of_nonneg_left hb (by norm_num))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasProjectionStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One tolerance controls normal projection through every chart of the finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma compact_chart_projection_stability (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ p ∈ tsupport (A.weight i),
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p ∈ tsupport (A.weight i),
      ‖coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖A.chartProjectedNormal i G n p-n p‖ < ε := by
  let S := {p : M // p ∈ tsupport (A.weight i)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_tsupport (A.weight i)).isCompact
  let c : S → SmallModes.Base := fun p => planeCoordinateIsometry (chart (i : M) p.1)
  have hc : Continuous c := planeCoordinateIsometry.continuous.comp
    (((chart (i : M)).continuousOn.mono (A.weight_support i)).domRestrict)
  have hread := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  have hX := (contDiff_real_coordDeriv hread dx).continuous.comp hc
  have hY := (contDiff_real_coordDeriv hread dy).continuous.comp hc
  have hnn : Continuous (fun p : S => spaceCoordinates (n p.1)) :=
    spaceCoordinates.continuous.comp (hn.continuous.comp continuous_subtype_val)
  let L := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  obtain ⟨δ,hδ,hnear⟩ := GeometryPreservation.compact_raw_normal_projection hX hY hnn
    (fun p => hD p.1 p.2) (fun p => by
      rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hunit]; norm_num)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dx)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dy) (div_pos hε (by positivity : 0 < L+1))
  refine ⟨δ,hδ,?_⟩
  intro G p hp hx hy
  have hh := (hnear ⟨p,hp⟩ _ _ hx hy).2
  let r := realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (spaceCoordinates (n p))-spaceCoordinates (n p)
  change ‖r‖ < ε/(L+1) at hh
  have he : A.chartProjectedNormal i G n p-n p = spaceCoordinates.symm r := by
    simp only [r,chartProjectedNormal,map_sub,ContinuousLinearEquiv.symm_apply_apply,c]
  rw [he]
  calc
    ‖spaceCoordinates.symm r‖ ≤ L*‖r‖ := spaceCoordinates.symm.toContinuousLinearMap.le_opNorm r
    _ ≤ (L+1)*‖r‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hh (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

theorem compact_atlas_projection_stability {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p : M,
      (∀ i : A.centers, A.weight i p ≠ 0 → ∀ v ∈ ({dx,dy} : Set SmallModes.Base),
        ‖coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i G)
          (planeCoordinateIsometry (chart (i : M) p))-
          coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (planeCoordinateIsometry (chart (i : M) p))‖ < δ) →
      A.projectedNormalField G n p ≠ 0 ∧
        ‖A.unitProjectedNormalField G n p-n p‖ < ε := by
  classical
  let η := min (1/2 : ℝ) (ε/3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hi := fun i => A.compact_chart_projection_stability i hF hn hunit hN (hD i) hη
  choose d hd hnear using hi
  obtain ⟨δ,hδ,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨δ,hδ,?_⟩
  intro G p hp
  have hh := A.unitProjectedNormalField_sub_bound (F := G) (p := p) (hunit p)
    (lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1/2:ℝ)<1)) (fun i hz =>
      (hnear i G p (subset_tsupport _ hz)
        ((hp i hz dx (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).trans_le (hle i))
        ((hp i hz dy (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).trans_le (hle i))).le)
  exact ⟨hh.1,hh.2.trans_lt (by have := min_le_right (1/2:ℝ) (ε/3); dsimp [η] at * <;> linarith)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasBounds
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAnsatzAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma directionalMap_smooth {F : A → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (directionalMap F v) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ImmersedAtlasNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the projection's Gram hypotheses from the actual immersion. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_gram_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) ≠ 0 := by
  have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
  change gramDet (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dx)
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dy) ≠ 0
  rw [he.fderiv_eq]
  apply gramDet_ne_zero_of_injective
  apply coordinateMap_injective_of_immersion hF hI (i : M)
  change planeCoordinateIsometry (chart (i : M) p) ∈ (coordinateChart (i : M)).target
  rw [planeCoordinateIsometry_chart]
  exact (coordinateChart (i : M)).map_source (A.weight_support i hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global polynomial variation is local in its varying field.
In particular, restoring the polynomial does not enlarge that support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance polynomialSupportFiberNormed_r7349f7_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_r7349f7_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualAdd_r7349f7_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSupportDualSmul_r7349f7_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialSupportSectionNormed_r7349f7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSupportSectionSpace_r7349f7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_eventually_zero (i : A.centers) {X : M → Space} {p : M}
    (hp : p ∈ (chart (i : M)).source) (hX : X =ᶠ[𝓝 p] 0) :
    A.jetChartMap i X =ᶠ[𝓝 (chart (i : M) p)] 0 := by
  have ht := (chart (i : M)).map_source hp
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using
      ((chart (i : M)).continuousAt_symm ht).tendsto
  have he := hX.comp_tendsto hc
  filter_upwards [he,(chart (i : M)).open_target.mem_nhds ht] with y hy hyt
  change X ((chart (i : M)).symm y) = 0 at hy
  change spaceCoordinates (localize (i : M) (A.outer i) X y) = 0
  simp only [localize,indicator_of_mem hyt,hy,smul_zero,map_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the five-profile coefficient map with the genuine
second fundamental form of a smooth immersion. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma realBoundaryProfile_regular {F : RField 4} {p : Base} (z : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) :
    realBoundaryProfile F z p ∈ regularBoundaryProfiles := by
  exact ⟨hD,hB⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondFormNormalFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth fields of actual second forms and their preferred unit normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma realBoundaryProfile_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ) :
    ContDiff ℝ ∞ (realBoundaryProfile F z) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : Base => z)).smul (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five Euclidean profiles used by the exact primitive determine the
canonical normal frame in the real surface coordinates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame SurfaceJetCoordinates JetVelocityCoordinates
open SurfaceVelocityFamily.Loop

private lemma directional_euclidean_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v : JetPolynomial.Base) :
    PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv v) F (baseEquiv q)) := by
  funext q
  change fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ F) ∘ baseEquiv) q v = _
  rw [fderiv_comp q ((JetVelocityCoordinates.toEuclidean.contDiff.comp hF).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    baseEquiv.differentiableAt,ContinuousLinearMap.comp_apply,baseEquiv.fderiv]
  rw [fderiv_comp (baseEquiv q) JetVelocityCoordinates.toEuclidean.differentiableAt
    (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),ContinuousLinearMap.comp_apply,JetVelocityCoordinates.toEuclidean.fderiv]
  rfl

lemma boundaryProfileMap_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (primitiveJetProfile (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) z p) =
      realBoundaryProfile F z (baseEquiv p) := by
  have hfirst (v : JetPolynomial.Base) := directional_euclidean_chart hF v
  have hsecond (v w : JetPolynomial.Base) :
      PeriodicExpansion.directionalMap
        (PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v) w =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv w)
        (SmallModes.coordDeriv (baseEquiv v) F) (baseEquiv q)) := by
    rw [hfirst]
    exact directional_euclidean_chart (contDiff_real_coordDeriv hF _) w
  funext j
  fin_cases j
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0) p) = _
    rw [hfirst]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1) p) = _
    rw [hfirst]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_zero,baseEquiv_one,JetVelocityCoordinates.toEuclidean,
      ContinuousLinearEquiv.apply_symm_apply]
    exact real_second_coordDeriv_comm hF (baseEquiv p) SmallModes.dy SmallModes.dx
  · change spaceCoordinates (z • PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 0) p) = _
    rw [hsecond,map_smul]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveProfileStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five primitive derivative components are stable under a global C2
correction.  Their bound is uniform in the fast scale between zero and one. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates WeightedEstimates PeriodicExpansion

private lemma directional_sub {f g : JetPolynomial.Base → Euclidean}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v : JetPolynomial.Base) :
    directionalMap (f-g) v = directionalMap f v-directionalMap g v := by
  funext p
  change (fderiv ℝ (fun q => f q-g q) p) v = (fderiv ℝ f p) v-(fderiv ℝ g p) v
  rw [fderiv_fun_sub (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)]
  rfl

lemma primitiveJetProfile_sub {f g : JetPolynomial.Base → Euclidean}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : ℝ) (p : JetPolynomial.Base) :
    primitiveJetProfile (f-g) z p = primitiveJetProfile f z p-primitiveJetProfile g z p := by
  have hsecond (v w : JetPolynomial.Base) :
      directionalMap (directionalMap (f-g) v) w =
        directionalMap (directionalMap f v) w-directionalMap (directionalMap g v) w := by
    rw [directional_sub hf hg,directional_sub (directionalMap_smooth hf v) (directionalMap_smooth hg v)]
  unfold primitiveJetProfile
  simp only [hsecond]
  simp only [directional_sub hf hg]
  ext i
  fin_cases i <;> simp [smul_sub]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_sub (i : A.centers) (F G : M → Space) :
    A.vectorChartRead i (G-F) = A.vectorChartRead i G-A.vectorChartRead i F := by
  funext x
  unfold vectorChartRead localize
  by_cases hx : x ∈ (chart (i : M)).target <;> simp [hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasLeadingProfileStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global C3 displacement controls all five geometric leading profiles
in a fixed atlas chart, uniformly on compact sets and all periodic phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_sub (i : A.centers) (F G : M → Space) :
    A.jetChartMap i (G-F) = fun p => A.jetChartMap i G p-A.jetChartMap i F p := by
  unfold jetChartMap
  rw [A.vectorChartRead_sub]
  funext p
  exact map_sub spaceCoordinates _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCompositionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth changes of coordinates preserve the second-order
rescaled derivative profile needed by the primitive recursion. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_composition_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {S : Set Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : Base → E) (C : ℝ),
      0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ 1 m C f →
      WeightedBound S 1 m (D*C) (f ∘ T) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hS isOpen_univ hSc
    subset_closure (subset_univ _) hT.contDiffOn m
  let D : ℝ := (m.factorial : ℝ)*B^m
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos m) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro f C hC hf hb
  have hcoord : ∀ k, 1 ≤ k → k ≤ m → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k T S x‖ ≤ B := by
    intro k _ hk x hx
    simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl k hk x hx
  have hh := hb.comp_coordinates hS.uniqueDiffOn uniqueDiffOn_univ zero_lt_one le_rfl
    hB hC hT.contDiffOn hf.contDiffOn (fun _ _ => mem_univ _) hcoord
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [D]
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_smooth (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.phaseRealChartMap i T F) :=
  (A.jetChartMap_smooth i hF).comp (hT.comp baseEquiv.symm.contDiff)

lemma phaseRealChartMap_profile (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p) =
      realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) := by
  have he : (fun q => JetVelocityCoordinates.toEuclidean (A.phaseRealChartMap i T F (baseEquiv q))) =
      A.vectorChartRead i F ∘ T := by
    funext q
    change spaceCoordinates.symm
      (A.jetChartMap i F (T (baseEquiv.symm (baseEquiv q)))) = A.vectorChartRead i F (T q)
    rw [baseEquiv.symm_apply_apply]
    exact spaceCoordinates.symm_apply_apply _
  simpa only [he] using boundaryProfileMap_chart (A.phaseRealChartMap_smooth i hT hF) z p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseProfileStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the five derivative profiles after a fixed nonlinear change
of coordinates, with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates WeightedEstimates PeriodicExpansion

lemma primitiveJetProfile_bound_on {f : JetPolynomial.Base → Euclidean}
    {S : Set JetPolynomial.Base} (hS : IsOpen S)
    (hf : ContDiff ℝ ∞ f) {C z : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hb : WeightedBound S 1 2 C f) {p : JetPolynomial.Base} (hp : p ∈ S) :
    ‖primitiveJetProfile f z p‖ ≤ C := by
  have hw (vs : List (Fin 2)) (hlen : vs.length ≤ 2) :
      ‖iteratedDirectional (vs.map coordinateVector) f p‖ ≤ C := by
    have hv : ∀ v ∈ vs.map coordinateVector, ‖v‖ ≤ 1 := by
      intro v hv
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le j
    have hb' : WeightedBound S 1 (0+(vs.map coordinateVector).length) C f :=
      hb.mono_order (by simpa only [zero_add,List.length_map] using hlen)
    have hh := hb'.iteratedDirectional hS zero_lt_one hC hf.contDiffOn
      (vs.map coordinateVector) hv 0
    simpa only [one_pow,div_one] using hh.norm_le hp
  have hx : ‖directionalMap f (coordinateVector 0) p‖ ≤ C := by
    dsimp only [directionalMap]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [0] (by decide)
  have hy : ‖directionalMap f (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1] (by decide)
  have hdir (v : JetPolynomial.Base) : directionalMap f v = (fun q => fderiv ℝ f q v) := rfl
  have hxx : ‖directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 0) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [0,0] (by decide)
  have hxy : ‖directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1,0] (by decide)
  have hyy : ‖directionalMap (directionalMap f (coordinateVector 1)) (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1,1] (by decide)
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hyy
  · exact hxy
  · change ‖z • directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 0) p‖ ≤ C
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
    exact (mul_le_mul_of_nonneg_left hxx hz).trans (mul_le_of_le_one_left hC hz1)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_profile_correction_bound (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ∀ C z : ℝ, 0 ≤ C → 0 ≤ z → z ≤ 1 → A.WeightedBound 1 2 C (G-F) →
      ∀ p ∈ S,
      ‖primitiveJetProfile (A.vectorChartRead i G ∘ T) z p-
        primitiveJetProfile (A.vectorChartRead i F ∘ T) z p‖ ≤ D*C := by
  obtain ⟨D₀,hD₀,hd⟩ := A.vectorChartRead_bound (V := Space) i 2
  obtain ⟨D₁,hD₁,hcomp⟩ := compact_composition_bound (E := Space) hT hS hSc 2
  refine ⟨D₁*D₀,mul_nonneg (by linarith) hD₀,?_⟩
  intro F G hF hG C z hC hz hz1 hdiff p hp
  have hb := hd (G-F) 1 C zero_lt_one le_rfl hC (hG.sub hF) hdiff
  have hc := hcomp (A.vectorChartRead i (G-F)) (D₀*C)
    (mul_nonneg hD₀ hC) (A.vectorChartRead_smooth i (hG.sub hF)) hb
  have hid : A.vectorChartRead i (G-F) ∘ T =
      (A.vectorChartRead i G ∘ T)-(A.vectorChartRead i F ∘ T) := by
    rw [A.vectorChartRead_sub]
    rfl
  rw [hid] at hc
  rw [← primitiveJetProfile_sub ((A.vectorChartRead_smooth i hG).comp hT)
    ((A.vectorChartRead_smooth i hF).comp hT)]
  have hh := primitiveJetProfile_bound_on hS
    (((A.vectorChartRead_smooth i hG).comp hT).sub ((A.vectorChartRead_smooth i hF).comp hT))
    (mul_nonneg (by linarith : 0 ≤ D₁) (mul_nonneg hD₀ hC)) hz hz1 hc hp
  change ‖primitiveJetProfile ((A.vectorChartRead i G ∘ T)-(A.vectorChartRead i F ∘ T)) z p‖ ≤
    D₁*(D₀*C) at hh
  exact hh.trans_eq (mul_assoc D₁ D₀ C).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseExteriorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior C2 control in the actual nonlinear phase chart, including
the closure of the exterior where its boundary is glued. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates GeometryPreservation SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_eventuallyEq (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {F G : M → Space} {p : JetPolynomial.Base}
    (hp : T p ∈ (chart (i : M)).target)
    (hFG : F =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G) :
    A.phaseRealChartMap i T F =ᶠ[𝓝 (baseEquiv p)] A.phaseRealChartMap i T G := by
  have hsource := (chart (i : M)).map_target hp
  have hz : F-G =ᶠ[𝓝 ((chart (i : M)).symm (T p))] 0 := by
    filter_upwards [hFG] with q hq
    simp only [Pi.sub_apply,hq,sub_self,Pi.zero_apply]
  have he := A.jetChartMap_eventually_zero i hsource hz
  rw [(chart (i : M)).right_inv hp] at he
  rw [A.jetChartMap_sub] at he
  have hg : A.jetChartMap i F =ᶠ[𝓝 (T p)] A.jetChartMap i G := by
    filter_upwards [he] with q hq
    exact sub_eq_zero.mp hq
  have ht := hT.continuous.tendsto p
  have hb := baseEquiv.symm.continuous.tendsto (baseEquiv p)
  rw [baseEquiv.symm_apply_apply] at hb
  exact hg.comp_tendsto (ht.comp hb)


lemma phase_profile_eq_on_exterior_closure (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {F G : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) {O : Set JetPolynomial.Base}
    (hO : ∀ p ∈ O, T p ∈ (chart (i : M)).target)
    (hext : ∀ p ∈ O, F =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G)
    (z : ℝ) :
    ∀ p ∈ closure O, realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) =
      realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p) := by
  have he : EqOn (fun p => realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p))
      (fun p => realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p)) O := by
    intro p hp
    have hh := A.phaseRealChartMap_eventuallyEq i hT (hO p hp) (hext p hp)
    have hd (v : SmallModes.Base) := RealModes.coordDeriv_germ hh v
    have hdd (v w : SmallModes.Base) := RealModes.coordDeriv_germ (hd w) v
    funext j
    fin_cases j
    · exact (hd SmallModes.dx).eq_of_nhds
    · exact (hd SmallModes.dy).eq_of_nhds
    · exact (hdd SmallModes.dy SmallModes.dy).eq_of_nhds
    · exact (hdd SmallModes.dx SmallModes.dy).eq_of_nhds
    · exact congrArg (fun v => z • v) (hdd SmallModes.dx SmallModes.dx).eq_of_nhds
  exact he.closure ((realBoundaryProfile_smooth (A.phaseRealChartMap_smooth i hT hF) z).continuous.comp
    baseEquiv.continuous) ((realBoundaryProfile_smooth (A.phaseRealChartMap_smooth i hT hG) z).continuous.comp
    baseEquiv.continuous)

lemma phase_real_profile_correction_bound (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ∀ C z : ℝ, 0 ≤ C → 0 ≤ z → z ≤ 1 → A.WeightedBound 1 2 C (G-F) → ∀ p ∈ S,
      ‖realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p)-
        realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p)‖ ≤ D*C := by
  obtain ⟨D,hD,hbound⟩ := A.phase_profile_correction_bound i hT hS hSc
  refine ⟨‖boundaryProfileMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G hF hG C z hC hz hz1 hb p hp
  rw [← A.phaseRealChartMap_profile i hT hG,← A.phaseRealChartMap_profile i hT hF,← map_sub]
  exact (boundaryProfileMap.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (hbound F G hF hG C z hC hz hz1 hb p hp)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

theorem phase_exterior_profile_bound_closure (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set JetPolynomial.Base, (∀ p ∈ O, T p ∈ (chart (i : M)).target) →
      (∀ p ∈ O, V =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G) →
      ∀ p ∈ closure O ∩ S,
      ‖realBoundaryProfile (A.phaseRealChartMap i T W) 1 (baseEquiv p)-
        realBoundaryProfile (A.phaseRealChartMap i T F) 1 (baseEquiv p)‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hbound⟩ := A.phase_real_profile_correction_bound i hT hS hSc
  refine ⟨D,hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hO hext p hp
  have he := A.phase_profile_eq_on_exterior_closure i hT hV hG hO hext 1 p hp.1
  have hfirst := hbound V W hV hW c 1 hc zero_le_one le_rfl hWV p hp.2
  have hsecond := hbound F G hF hG b 1 hb zero_le_one le_rfl hGF p hp.2
  have ht := norm_sub_le_norm_sub_add_norm_sub (realBoundaryProfile (A.phaseRealChartMap i T W) 1 (baseEquiv p))
    (realBoundaryProfile (A.phaseRealChartMap i T V) 1 (baseEquiv p))
    (realBoundaryProfile (A.phaseRealChartMap i T F) 1 (baseEquiv p))
  rw [he] at ht hfirst
  exact ht.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth comparison maps agreeing on an open exterior have equal jets
at its boundary. This retains the disk boundary in exterior C2 estimates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_eventuallyEq_at_source {F G : M → Space} {p : M}
    (hFG : F =ᶠ[𝓝 p] G) (i : A.centers) (hp : p ∈ (chart (i : M)).source) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))]
        (spaceCoordinates ∘ A.vectorPlaneRead i G) := by
  have ht : Tendsto (fun x : SmallModes.Base => (chart (i : M)).symm (planeCoordinateIsometry.symm x))
      (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 p) := by
    have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
      simpa only [(chart (i : M)).left_inv hp] using
        ((chart (i : M)).continuousAt_symm ((chart (i : M)).map_source hp)).tendsto
    have hi : Tendsto planeCoordinateIsometry.symm
        (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 (chart (i : M) p)) := by
      simpa only [LinearIsometryEquiv.symm_apply_apply] using
        (planeCoordinateIsometry.symm.continuousAt (x := planeCoordinateIsometry (chart (i : M) p))).tendsto
    exact hc.comp hi
  filter_upwards [hFG.comp_tendsto ht] with x hx
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x)) =
    spaceCoordinates (localize (i : M) (A.outer i) G (planeCoordinateIsometry.symm x))
  unfold localize
  by_cases hxT : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [indicator_of_mem hxT]
    change F ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) =
      G ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) at hx
    rw [hx]
  · simp only [indicator_of_notMem hxT]

lemma planeRead_jets_eq_on_exterior_closure {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    {O : Set M} (hext : ∀ p ∈ O, F =ᶠ[𝓝 p] G)
    (i : A.centers) (m : ℕ) :
    ∀ p ∈ closure O, p ∈ (chart (i : M)).source →
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)) =
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p)) := by
  let U := (chart (i : M)).source
  have hU : IsOpen U := (chart (i : M)).open_source
  let a := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (planeCoordinateIsometry (chart (i : M) p))
  let b := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (planeCoordinateIsometry (chart (i : M) p))
  have hca : ContinuousOn a U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).continuous_iteratedFDeriv
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have hcb : ContinuousOn b U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).continuous_iteratedFDeriv
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have he : EqOn a b (O ∩ U) := by
    intro p hp
    exact ((A.planeRead_eventuallyEq_at_source (hext p hp.1) i hp.2).iteratedFDeriv ℝ m).eq_of_nhds
  have hclosed := he.of_subset_closure (hca.mono inter_subset_right) (hcb.mono inter_subset_right)
    (fun p hp => ⟨subset_closure hp.1,hp.2⟩) hU.closure_inter
  exact fun p hp hpU => hclosed ⟨hp,hpU⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the actual exterior C2 estimate through the boundary by continuity
of every coordinate jet. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_read_C2_bound_closure (j : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O, p ∈ tsupport (A.weight j) →
      ∀ m ≤ 2,
      ‖iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) j 2
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,
    mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp m hm
  let H := (G-F)+(W-V)
  have hH : ContMDiff planeModel spaceModel ∞ H := (hG.sub hF).add (hW.sub hV)
  have hbound : A.WeightedBound 1 2 (b+c) H := by
    intro i
    change WeightedEstimates.WeightedBound univ 1 2 (b+c)
      (localize (i : M) (A.weight i) ((G-F)+(W-V)))
    rw [localize_add]
    exact WeightedEstimates.WeightedBound.add uniqueDiffOn_univ zero_le_one
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hG.sub hF)).contDiffOn
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hW.sub hV)).contDiffOn
      (hGF i) (hWV i)
  have hread := hd H 1 (b+c) zero_lt_one le_rfl (add_nonneg hb hc) hH hbound
  have hlinear := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth j hH).contDiffOn spaceCoordinates.toContinuousLinearMap
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead j H) at hlinear
  have he' : ∀ q ∈ O, W-F =ᶠ[𝓝 q] H := by
    intro q hq
    filter_upwards [hext q hq] with x hx
    dsimp [H]
    rw [hx]
    abel
  have hjet := A.planeRead_jets_eq_on_exterior_closure (hW.sub hF) hH he' j m
    p hpO (A.weight_support j hp)
  change iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
    (planeCoordinateIsometry (chart (j : M) p)) = _ at hjet
  rw [hjet]
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,mul_assoc] using
    hlinear m hm (planeCoordinateIsometry (chart (j : M) p)) (mem_univ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureNormal
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained slow baseline and C2 correction control the actual
normalized exterior normal, uniformly over every atlas chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_projected_normal_close_closure {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O,
      A.projectedNormalField W n p ≠ 0 ∧ ‖A.unitProjectedNormalField W n p-n p‖ < ε := by
  classical
  obtain ⟨δ,hδ,hnear⟩ := A.compact_atlas_projection_stability hF hn hunit hN hD hε
  choose D hD0 hbound using fun i => A.exterior_read_C2_bound_closure i
  obtain ⟨ρ,hρ,_,hle⟩ := finite_positive_threshold (fun i => δ/(D i+1))
    (fun i => div_pos hδ (by have := hD0 i; positivity))
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hpO
  apply hnear W p
  intro i hi v hv
  have hp := subset_tsupport (A.weight i) hi
  have hd := hbound i F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp 1 (by omega)
  rw [norm_iteratedFDeriv_one] at hd
  have hs : D i*(b+c) < δ := by
    have ht := (lt_div_iff₀ (by have := hD0 i; positivity : 0 < D i+1)).mp
      (hbc.trans_le (hle i))
    nlinarith
  have hnV : ‖v‖ ≤ 1 := by
    rcases hv with rfl | hv
    · simp [dx]
    · have hv' : v = dy := by simpa only [mem_singleton_iff] using hv
      subst v
      simp [dy]
  have hre : spaceCoordinates ∘ A.vectorPlaneRead i (W-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i W)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact map_sub spaceCoordinates _ _
  rw [hre,fderiv_sub
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hW).differentiable (by simp) _))
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _))] at hd
  change ‖((fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i W) _)-
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _)) v‖ < δ
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_left hnV (norm_nonneg _)).trans (by simpa only [mul_one] using hd))).trans_lt hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossPhaseExteriorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior control in a fixed curve chart, while the analytic construction
and projected normal use the current immersion's smoothing atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem cross_phase_exterior_control {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ (O : Set M) (P : Set JetPolynomial.Base),
      (∀ y ∈ P, T y ∈ (chart (i : M)).target) →
      (∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ closure O, ∀ q ∈ closure P ∩ S,
      A.projectedNormalField W n.vector p ≠ 0 ∧
      ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p)-spaceCoordinates (n.vector p)‖ < ε ∧
      ‖realBoundaryProfile (B.phaseRealChartMap i T W) 1 (baseEquiv q)-
        realBoundaryProfile (B.phaseRealChartMap i T F) 1 (baseEquiv q)‖ < ε := by
  obtain ⟨D,hD,hbound⟩ := B.phase_exterior_profile_bound_closure i hT hS hSc
  obtain ⟨E,hE,hchange⟩ := A.weightedBound_change_atlas (V := Space) B 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hLp : 0 < L+1 := by positivity
  obtain ⟨r,hr,hnorm⟩ := A.exterior_projected_normal_close_closure hF n.smooth n.unit n.normal
    (fun j y hy => A.planeRead_gram_of_immersion hF hI houter j hy) (div_pos hε hLp)
  have hDE : 0 ≤ D*E := mul_nonneg hD hE
  refine ⟨min r (ε/(D*E+1)),lt_min hr (div_pos hε (by positivity)),?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O P hP hPO hext p hp q hq
  obtain ⟨hne,hnear⟩ := hnorm G V W hG hV hW b c hb hc
    (hbc.trans_le (min_le_left _ _)) hGF hWV O hext p hp
  have hprof := hbound F G V W hF hG hV hW (E*b) (E*c) (mul_nonneg hE hb) (mul_nonneg hE hc)
    (hchange (G-F) 1 b zero_lt_one le_rfl hb (hG.sub hF) hGF)
    (hchange (W-V) 1 c zero_lt_one le_rfl hc (hW.sub hV) hWV)
    P hP (fun y hy => hext _ (hPO y hy)) q hq
  have hsmall : D*(E*b+E*c) < ε := by
    have ht := (lt_div_iff₀ (by positivity : 0 < D*E+1)).mp
      (hbc.trans_le (min_le_right _ _))
    have hbc0 : 0 ≤ b+c := add_nonneg hb hc
    nlinarith
  refine ⟨hne,?_,hprof.trans_lt hsmall⟩
  rw [← map_sub]
  calc
    ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p-n.vector p)‖ ≤
        L*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      spaceCoordinates.toContinuousLinearMap.le_opNorm _
    _ ≤ (L+1)*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hnear hLp
    _ = ε := mul_div_cancel₀ _ hLp.ne'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold

namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame
lemma coordinateGauss_eq_curvature_mul (F : RField 4) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p *
        gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  change _ = (_ / gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * _
  exact (div_mul_cancel₀ _ hD).symm
end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseExteriorDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior comparison regions in the actual phase chart, including their
boundary points. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma phaseExteriorDomain_properties (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M) :
    ∀ y ∈ phaseExteriorDomain q e O,
      e.symm y ∈ (chart q).target ∧ (chart q).symm (e.symm y) ∈ O := by
  rintro y ⟨p,⟨hpO,hps⟩,rfl⟩
  have hpe : chart q p ∈ e.source := hps.2
  have he := e.left_inv hpe
  change e.symm (e (chart q p)) ∈ (chart q).target ∧
    (chart q).symm (e.symm (e (chart q p))) ∈ O
  rw [he,(chart q).left_inv hps.1]
  exact ⟨(chart q).map_source hps.1,hpO⟩

lemma phaseExteriorDomain_closure (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M)
    {p : M} (hps : p ∈ ((chart q).trans e).source) (hpO : p ∈ closure O) :
    e (chart q p) ∈ closure (phaseExteriorDomain q e O) := by
  have hc : ContinuousAt ((chart q).trans e) p := ((chart q).trans e).continuousAt hps
  exact mem_closure_image hc (((chart q).trans e).open_source.closure_inter ⟨hpO,hps⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetSecondForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unscaled five-jets encode the actual second form and ordered crossings.
These expressions are used for exterior C2 stability. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma boundaryJetSecond_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p v w : Base) :
    boundaryJetSecond (realBoundaryProfile F 1 p) v w = realSecondForm F v w p := by
  unfold boundaryJetSecond realBoundaryProfile realSecondForm
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,one_smul]
  rw [second_coordDeriv_bilinear hF v w p]

lemma continuousAt_boundaryJetSecond {J : BoundaryProfile} (v w : Base)
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0) :
    ContinuousAt (fun a : BoundaryProfile × (Base × Base) => boundaryJetSecond a.1 a.2.1 a.2.2)
      (J,v,w) := by
  have h0 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 0) :=
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h1 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 1) :=
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) =>
      (a.2.1.1*a.2.2.1) • a.1 4+(a.2.1.1*a.2.2.2+a.2.1.2*a.2.2.1) • a.1 3+
        (a.2.1.2*a.2.2.2) • a.1 2) := by fun_prop
  exact (contDiffAt_realNormalPart h0.contDiffAt h1.contDiffAt h2.contDiffAt hD).continuousAt

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetAvoidance
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior antipode exclusions are open conditions on the unscaled
second jet and the preferred normal. Compactness makes the tolerance uniform. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma isOpen_boundaryJetAvoidance : IsOpen boundaryJetAvoidance := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let Z := BoundaryProfile × (Vec × Base)
  have hd : Continuous (fun a : Z => NormalFrame.gramDet (a.1 0) (a.1 1)) := by
    exact contDiff_gram_pair.continuous.comp (show Continuous (fun a : Z => (a.1 0,a.1 1)) by
      dsimp [Z]
      fun_prop)
  have hm : Continuous (fun a : Z => (a.1,a.2.2,a.2.2)) := by fun_prop
  have hP := (continuousAt_boundaryJetSecond a.2.2 a.2.2 ha.1).comp
    (f := fun a : Z => (a.1,a.2.2,a.2.2)) (x := a) hm.continuousAt
  have hnorm := (normalize_smoothAt contDiffAt_id ha.2.1).continuousAt.comp
    (f := fun a : Z => boundaryJetSecond a.1 a.2.2 a.2.2) (x := a) hP
  have hn : Continuous (fun a : Z => a.2.1) := by fun_prop
  have hne := (hn.continuousAt.sub hnorm.neg).eventually_ne (sub_ne_zero.mpr ha.2.2)
  filter_upwards [hd.continuousAt.eventually_ne ha.1,hP.eventually_ne ha.2.1,hne] with b hbD hbP hbn
  exact ⟨hbD,hbP,sub_ne_zero.mp hbn⟩

theorem compact_boundary_jet_avoidance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {n : X → Vec} {v : X → Base}
    (hJ : Continuous J) (hn : Continuous n) (hv : Continuous v)
    (hold : ∀ x, (J x,n x,v x) ∈ boundaryJetAvoidance) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile, ∀ m : Vec,
      ‖H-J x‖ < δ → ‖m-n x‖ < δ → (H,m,v x) ∈ boundaryJetAvoidance := by
  let f := fun x => (J x,n x,v x)
  have hf : Continuous f := hJ.prodMk (hn.prodMk hv)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryJetAvoidance (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H m hH hm
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(m,v x)) (J x,(n x,v x)) < δ
  rw [Prod.dist_eq,dist_prod_same_right,dist_eq_norm,dist_eq_norm]
  exact max_lt hH hm

theorem compact_actual_exterior_avoidance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {n : X → Vec} {v : X → Base}
    (hp : Continuous p) (hn : Continuous n) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hP : ∀ x, realSecondForm F (v x) (v x) (p x) ≠ 0)
    (havoid : ∀ x, n x ≠ -normalize (realSecondForm F (v x) (v x) (p x))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → realSecondForm G (v x) (v x) (p x) ≠ 0 ∧
        m ≠ -normalize (realSecondForm G (v x) (v x) (p x)) := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_jet_avoidance hJ hn hv (by
    intro x
    refine ⟨hD x,?_,?_⟩ <;> rw [boundaryJetSecond_actual hF]
    · exact hP x
    · exact havoid x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG m hnear hm
  have hh := hclose x (realBoundaryProfile G 1 (p x)) m hnear hm
  simpa only [boundaryJetSecond_actual hG] using hh.2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetPositivity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exterior preservation of the positive normal pairings. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma isOpen_boundaryJetPositivity : IsOpen boundaryJetPositivity := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let Z := BoundaryProfile × (Vec × Base)
  have hd : Continuous (fun a : Z => NormalFrame.gramDet (a.1 0) (a.1 1)) :=
    contDiff_gram_pair.continuous.comp (show Continuous (fun a : Z => (a.1 0,a.1 1)) by
      dsimp [Z]
      fun_prop)
  have hm : Continuous (fun a : Z => (a.1,a.2.2,a.2.2)) := by fun_prop
  have hP := (continuousAt_boundaryJetSecond a.2.2 a.2.2 ha.1).comp
    (f := fun a : Z => (a.1,a.2.2,a.2.2)) (x := a) hm.continuousAt
  have hn : Continuous (fun a : Z => a.2.1) := by fun_prop
  have hdot : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hh := hdot.continuousAt.comp (f := fun a : Z =>
    (boundaryJetSecond a.1 a.2.2 a.2.2,a.2.1)) (x := a) (hP.prodMk hn.continuousAt)
  filter_upwards [hd.continuousAt.eventually_ne ha.1,hh.eventually (isOpen_Ioi.mem_nhds ha.2)] with b hb hp
  exact ⟨hb,hp⟩

theorem compact_boundary_jet_positivity {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {n : X → Vec} {v : X → Base}
    (hJ : Continuous J) (hn : Continuous n) (hv : Continuous v)
    (hold : ∀ x, (J x,n x,v x) ∈ boundaryJetPositivity) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile, ∀ m : Vec,
      ‖H-J x‖ < δ → ‖m-n x‖ < δ → 0 < boundaryJetSecond H (v x) (v x) ⬝ᵥ m := by
  let f := fun x => (J x,n x,v x)
  have hf : Continuous f := hJ.prodMk (hn.prodMk hv)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryJetPositivity (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H m hH hm
  apply And.right (a := NormalFrame.gramDet (H 0) (H 1) ≠ 0)
  change (H,m,v x) ∈ boundaryJetPositivity
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(m,v x)) (J x,(n x,v x)) < δ
  rw [Prod.dist_eq,dist_prod_same_right,dist_eq_norm,dist_eq_norm]
  exact max_lt hH hm

theorem compact_actual_exterior_pairing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {n : X → Vec} {v : X → Base}
    (hp : Continuous p) (hn : Continuous n) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hpositive : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ n x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → 0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ m := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_jet_positivity hJ hn hv (by
    intro x
    refine ⟨hD x,?_⟩
    rw [boundaryJetSecond_actual hF]
    exact hpositive x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG m hnear hm
  simpa only [boundaryJetSecond_actual hG] using hclose x (realBoundaryProfile G 1 (p x)) m hnear hm

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingPositivePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary Gauss inequality used when matching the interior and
exterior preferred normals. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open SmallModes RealModes NormalFrame

lemma dot_square_le_self_of_unit (W n : Vec) (hn : n ⬝ᵥ n = 1) :
    (W ⬝ᵥ n)^2 ≤ W ⬝ᵥ W := by
  have h : 0 ≤ (W-(W ⬝ᵥ n) • n) ⬝ᵥ (W-(W ⬝ᵥ n) • n) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  simp only [sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,hn,dotProduct_comm n W] at h
  nlinarith

lemma secondForm_gauss_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) :
    realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
      realSecondForm F v w p ⬝ᵥ realSecondForm F v w p =
    (v.1*w.2-v.2*w.1)^2 *
      (realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p -
        realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p) := by
  conv_lhs =>
    simp only [realSecondForm_bilinear hF v v,realSecondForm_bilinear hF w w,
      realSecondForm_bilinear hF v w]
  simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dx dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dy p)]
  ring

lemma orderedCrossing_le_pure_pairing {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (kappa : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hA : realSecondForm F v v p ≠ 0)
    (hk : coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) p = kappa*gramDet (coordDeriv dx F p) (coordDeriv dy F p)) :
    orderedCrossing F v w p kappa ≤
      realSecondForm F v v p ⬝ᵥ realSecondForm F w w p := by
  have hg := secondForm_gauss_directions hF p v w
  rw [gauss_metric_identity hF p hD,hk] at hg
  have hgram : gramDet (coordDeriv v F p) (coordDeriv w F p) =
      (v.1*w.2-v.2*w.1)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F v,coordDeriv_eq_basis F w,gramDet_change_basis]
  have hp := dot_square_le_self_of_unit (realSecondForm F v w p)
    (normalize (realSecondForm F v v p)) (normalize_unit hA)
  unfold orderedCrossing
  rw [hgram]
  nlinarith

lemma orderedCrossing_pos_pure_pairing {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (kappa : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hA : realSecondForm F v v p ≠ 0)
    (hk : coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) p = kappa*gramDet (coordDeriv dx F p) (coordDeriv dy F p))
    (hQ : 0 < orderedCrossing F v w p kappa) :
    0 < realSecondForm F w w p ⬝ᵥ normalize (realSecondForm F v v p) := by
  have hp := hQ.trans_le (orderedCrossing_le_pure_pairing hF p v w kappa hD hA hk)
  rw [normalize,dotProduct_smul,dotProduct_comm (realSecondForm F w w p)]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (dot_self_pos hA))) hp

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryNormalMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strict data for the interior/exterior normal interpolation.
The new canonical yy normal and the exterior normal both pair positively
with every later curve meeting the support boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma isOpen_boundaryPreferredPairing : IsOpen boundaryPreferredPairing := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hr : ContinuousAt (fun b : BoundaryProfile × Base => b.1) a := continuous_fst.continuousAt
  have hp := (continuousAt_boundaryJetSecond a.2 a.2 ha.1.1).comp
    (f := fun b : BoundaryProfile × Base => (b.1,b.2,b.2)) (x := a)
    (by fun_prop : ContinuousAt (fun b : BoundaryProfile × Base => (b.1,b.2,b.2)) a)
  have hn := (contDiffAt_profilePreferred ha.1).continuousAt.comp hr
  have hdot : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hh := hdot.continuousAt.comp (f := fun b : BoundaryProfile × Base =>
    (boundaryJetSecond b.1 b.2 b.2,profilePreferred b.1)) (x := a) (hp.prodMk hn)
  exact (hr.eventually (isOpen_regularBoundaryProfiles.mem_nhds ha.1)).and
    (hh.eventually (isOpen_Ioi.mem_nhds ha.2))

lemma profilePreferred_real (F : RField 4) (z : ℝ) (p : Base) :
    profilePreferred (realBoundaryProfile F z p) = normalize (realSecondForm F dy dy p) := rfl

lemma compact_actual_preferred_pairing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v : X → Base}
    (hp : Continuous p) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hB : ∀ x, realSecondForm F dy dy (p x) ≠ 0)
    (hpos : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ normalize (realSecondForm F dy dy (p x))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G →
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ∀ z : ℝ, 0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ profilePreferred (realBoundaryProfile G z (p x)) := by
  let f := fun x => (realBoundaryProfile F 1 (p x),v x)
  have hf : Continuous f := ((realBoundaryProfile_smooth hF 1).continuous.comp hp).prodMk hv
  have hmem (x : X) : f x ∈ boundaryPreferredPairing := by
    refine ⟨realBoundaryProfile_regular 1 (hD x) (hB x),?_⟩
    simpa only [f,boundaryJetSecond_actual hF,profilePreferred_real] using hpos x
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryPreferredPairing (by rintro _ ⟨x,rfl⟩; exact hmem x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG hclose z
  have hm : (realBoundaryProfile G 1 (p x),v x) ∈ boundaryPreferredPairing := by
    apply hsub
    apply Metric.thickening_subset_cthickening
    apply Metric.mem_thickening_iff.mpr
    refine ⟨f x,mem_range_self x,?_⟩
    change dist (realBoundaryProfile G 1 (p x),v x) (realBoundaryProfile F 1 (p x),v x) < δ
    rwa [dist_prod_same_right,dist_eq_norm]
  simpa only [boundaryJetSecond_actual hG,profilePreferred_real] using hm.2

theorem compact_actual_boundary_matching {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v : X → Base} {n : X → Vec}
    (hp : Continuous p) (hv : Continuous v) (hn : Continuous n)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hB : ∀ x, realSecondForm F dy dy (p x) ≠ 0)
    (havoid : ∀ x, n x ≠ -normalize (realSecondForm F dy dy (p x)))
    (hpos : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ n x)
    (κ : X → ℝ)
    (hGauss : ∀ x, coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) (p x) = κ x * NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)))
    (hQ : ∀ x, 0 < orderedCrossing F dy (v x) (p x) (κ x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → ∀ z : ℝ,
      realSecondForm G dy dy (p x) ≠ 0 ∧
      m ≠ -profilePreferred (realBoundaryProfile G z (p x)) ∧
      0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ m ∧
      0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ profilePreferred (realBoundaryProfile G z (p x)) := by
  obtain ⟨δa,hδa,ha⟩ := compact_actual_exterior_avoidance hF hp hn continuous_const hD hB havoid
  obtain ⟨δp,hδp,hpair⟩ := compact_actual_exterior_pairing hF hp hn hv hD hpos
  obtain ⟨δn,hδn,hpref⟩ := compact_actual_preferred_pairing hF hp hv hD hB
    (fun x => orderedCrossing_pos_pure_pairing hF (p x) dy (v x) (κ x) (hD x) (hB x) (hGauss x) (hQ x))
  let δ := min δa (min δp δn)
  have hδa' : δ ≤ δa := min_le_left _ _
  have hδp' : δ ≤ δp := (min_le_right _ _).trans (min_le_left _ _)
  have hδn' : δ ≤ δn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,lt_min hδa (lt_min hδp hδn),?_⟩
  intro x G hG m hGclose hm z
  obtain ⟨hB',hanti⟩ := ha x G hG m (hGclose.trans_le hδa') (hm.trans_le hδa')
  exact ⟨hB',by simpa only [profilePreferred_real] using hanti,
    hpair x G hG m (hGclose.trans_le hδp') (hm.trans_le hδp'),
    hpref x G hG (hGclose.trans_le hδn') z⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceBoundaryMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict original boundary geometry gives both positive pairings needed
to glue the exact canonical normal to the exterior projected normal. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_surface_boundary_matching_oai
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {C : Set M} (hC : IsCompact C)
    (hCs : C ⊆ ((chart (i : M)).trans e).source)
    (hw : ∀ p ∈ C, A.weight i p ≠ 0)
    (v : SmallModes.Base → SmallModes.Base) (hv : Continuous v)
    (hB : ∀ p ∈ C, realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
      (baseEquiv (e (chart (i : M) p))) ≠ 0)
    (havoid : ∀ p ∈ C, spaceCoordinates (n.vector p) ≠
      -normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      0 < realSecondForm (A.phaseRealChartMap i e.symm F) (v q) (v q) q ⬝ᵥ
        spaceCoordinates (n.vector p))
    (hcross : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ C ∩ closure O, ∀ z : ℝ,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm W
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p) ∧
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ profilePreferred (realBoundaryProfile H z q) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let Q : C → JetPolynomial.Base := fun p => e (chart (i : M) p)
  have hQ : Continuous Q := ((chart (i : M)).trans e).continuousOn.comp_continuous
    continuous_subtype_val (fun p => hCs p.property)
  have hK : IsCompact (Set.range Q) := isCompact_range hQ
  obtain ⟨S,hS,hKS,hSc,_⟩ := CollarVelocity.compact_open_thickening hK isOpen_univ (subset_univ _)
  have hD (p : C) := A.phase_gram_at_source i e he hi hF (hCs p.property) (hw p p.property)
  let H := A.phaseRealChartMap i e.symm F
  let κ : C → ℝ := fun p => coordinateGaussianCurvature (realMetric H dx dx)
    (realMetric H dx dy) (realMetric H dy dy) (baseEquiv (Q p))
  obtain ⟨δ,hδ,hstab⟩ := compact_actual_boundary_matching (A.phaseRealChartMap_smooth i hi hF.1)
    (baseEquiv.continuous.comp hQ) (hv.comp (baseEquiv.continuous.comp hQ))
    (spaceCoordinates.continuous.comp (n.smooth.continuous.comp continuous_subtype_val))
    hD (fun p : C => hB p p.property) (fun p : C => havoid p p.property)
    (fun p : C => hpositive p p.property) κ
    (fun p => coordinateGauss_eq_curvature_mul H _ (hD p))
    (fun p : C => hcross p p.property)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.cross_phase_exterior_control A hF.1
    (IsSmoothIsometricImmersion.mfderiv_injective hF) n houter i hi hS hSc hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hp z
  let P := phaseExteriorDomain (i : M) e O
  have hP := phaseExteriorDomain_properties (i : M) e O
  obtain ⟨_,hn,hj⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O P
    (fun y hy => (hP y hy).1) (fun y hy => (hP y hy).2) hext p hp.2
    (Q ⟨p,hp.1⟩) ⟨phaseExteriorDomain_closure (i : M) e O (hCs hp.1) hp.2,
      hKS (mem_range_self (⟨p,hp.1⟩ : C))⟩
  have hh := hstab (⟨p,hp.1⟩ : C) _ (A.phaseRealChartMap_smooth i hi hW) _ hj hn z
  exact ⟨hh.2.2.1,hh.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching_oai.{u_1}
