-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:53.047781+00:00
-- url     : https://prove2.me/submissions/84b219b3-264d-4eba-9ec3-74e91c0a370f

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_preserving_circular_primitive_boundary
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_geometric_normal_extension
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_primitive_boundary_crossing

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma dot_normalize_zero {v w : Vec} (h : w ⬝ᵥ v = 0) : w ⬝ᵥ normalize v = 0 := by
  simp [normalize, dotProduct_smul, h]

lemma normalize_of_unit {v : Vec} (hv : v ⬝ᵥ v = 1) : normalize v = v := by
  simp [normalize, hv]

lemma first_zero {u v : Vec} (hu : u ⬝ᵥ u = 1) : first u v 0 = u := by
  simpa [first, blend] using normalize_of_unit hu

lemma first_one {u v : Vec} (hv : v ⬝ᵥ v = 1) : first u v 1 = v := by
  simpa [first, blend] using normalize_of_unit hv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

lemma first_smoothAt_of_nonzero {u v : E → Vec} {t : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (ht : ContDiffAt ℝ ∞ t x)
    (hn : blend (u x) (v x) (t x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => first (u z) (v z) (t z)) x :=
  normalize_smoothAt (((contDiffAt_const.sub ht).smul hu).add (ht.smul hv)) hn

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preferred and complementary normals of a regular five-profile. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma profilePreferred_unit {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    profilePreferred J ⬝ᵥ profilePreferred J = 1 := normalize_unit hJ.2

lemma profilePreferred_perp {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    J 0 ⬝ᵥ profilePreferred J = 0 ∧ J 1 ⬝ᵥ profilePreferred J = 0 := by
  have hh := realNormalPart_perp (J 0) (J 1) (J 2) hJ.1
  exact ⟨dot_normalize_zero hh.1,dot_normalize_zero hh.2⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
attribute [-instance] _root_.instVAddIntReal_solutions
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseNormalNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local exact normal defines a genuine smooth unit normal on an
open surface neighborhood of the closed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseNormalLift_coordinates (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (ν : SmallModes.Base → NormalFrame.Vec) (p : M) :
    spaceCoordinates (A.phaseNormalLift i e ν p) = ν (baseEquiv (e (chart (i : M) p))) :=
  spaceCoordinates.apply_symm_apply _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondFormNormalFields
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

lemma realSecondForm_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base}
    (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (v w : Base) : ContDiffOn ℝ ∞ (realSecondForm F v w) U := by
  intro x hx
  exact (contDiffAt_realNormalPart
    (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt
    (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt
    (hD x hx)).contDiffWithinAt

lemma realSecondForm_variable_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base}
    (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    {v : Base → Base} (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun x => realSecondForm F (v x) (v x) x) U := by
  have hx := realSecondForm_smoothOn hF hD dx dx
  have hxy := realSecondForm_smoothOn hF hD dx dy
  have hy := realSecondForm_smoothOn hF hD dy dy
  have hvx : ContDiffOn ℝ ∞ (fun x => (v x).1) U := contDiff_fst.comp_contDiffOn hv
  have hvy : ContDiffOn ℝ ∞ (fun x => (v x).2) U := contDiff_snd.comp_contDiffOn hv
  have hh := (((hvx.pow 2).smul hx).add
    ((((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Base => (2:ℝ)) U).mul hvx).mul hvy).smul hxy)).add ((hvy.pow 2).smul hy)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [realSecondForm_quadratic hF]
  rfl

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

lemma profilePreferred_field_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {U : Set Base} (hreg : ∀ x ∈ U, realBoundaryProfile F z x ∈ regularBoundaryProfiles) :
    ContDiffOn ℝ ∞ (fun x => profilePreferred (realBoundaryProfile F z x)) U := by
  intro x hx
  exact ((contDiffAt_profilePreferred (hreg x hx)).comp x
    (realBoundaryProfile_smooth hF z).contDiffAt).contDiffWithinAt

lemma realSecondForm_field_perp {F : RField 4} {x : Base}
    (hD : gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0) (v w : Base) :
    coordDeriv dx F x ⬝ᵥ realSecondForm F v w x = 0 ∧
    coordDeriv dy F x ⬝ᵥ realSecondForm F v w x = 0 :=
  realNormalPart_perp _ _ _ hD

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteCrossingNeighborhoods
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose disjoint crossing neighborhoods inside prescribed open sets,
avoiding every curve that does not participate in that crossing. -/
noncomputable section
open Set
namespace ClosedSurfaceR4
variable {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι] [Fintype κ]

theorem finite_crossing_neighborhoods (x : ι → X) (hx : Function.Injective x)
    (left right : ι → κ) (C : κ → Set X) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (V : ι → Set X) (hV : ∀ i, IsOpen (V i)) (hxV : ∀ i, x i ∈ V i) :
    ∃ O : ι → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, x i ∈ O i) ∧
      (∀ i, O i ⊆ V i) ∧ Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      ∀ i k y, y ∈ O i → y ∈ C k → k = left i ∨ k = right i := by
  classical
  obtain ⟨W,hW,hdisj⟩ := (Set.finite_range x).t2_separation
  let O : ι → Set X := fun i => W (x i) ∩ V i ∩
    ⋂ k : κ, if k = left i ∨ k = right i then univ else (C k)ᶜ
  have hopen (i : ι) : IsOpen (O i) := by
    apply ((hW (x i)).2.inter (hV i)).inter
    apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact (hC k).isOpen_compl
  have hmem (i : ι) : x i ∈ O i := by
    refine ⟨⟨(hW (x i)).1,hxV i⟩,?_⟩
    apply mem_iInter.mpr
    intro k
    split_ifs with h
    · trivial
    · exact fun hc => h (honly i k hc)
  refine ⟨O,hopen,hmem,(fun i y hy => hy.1.2),?_,?_⟩
  · intro i j hij
    exact (hdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hx h))).mono
      (fun y hy => hy.1.1) (fun y hy => hy.1.1)
  · intro i k y hy hyC
    by_contra h
    have hy' := mem_iInter.mp hy.2 k
    simp only [h,ite_false, if_false,mem_compl_iff] at hy'
    exact hy' hyC

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteDisjointAdjustment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine the finitely many crossing adjustments on pairwise disjoint
neighborhoods. The patched field agrees exactly with the selected local field. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.VelocityFrame
variable {E F ι : Type*}

lemma finiteDisjointAdjustment_smoothOn
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {U : Set E} (hn : ContDiffOn ℝ ∞ n U)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) U) :
    ContDiffOn ℝ ∞ (finiteDisjointAdjustment s n g) U := by
  exact hn.add (ContDiffOn.sum fun i hi => (hg i hi).sub hn)

lemma finiteDisjointAdjustment_of_mem [AddCommGroup F] [DecidableEq ι] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E}
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (O i) (O j))
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    {i : ι} (hi : i ∈ s) {x : E} (hx : x ∈ O i) :
    finiteDisjointAdjustment s n g x = g i x := by
  have hz : ∀ j ∈ s, j ≠ i → g j x-n x = 0 := by
    intro j hj hji
    apply sub_eq_zero.mpr
    apply hext j hj x
    intro hxj
    exact Set.disjoint_left.mp (hdisj hj hi hji) hxj hx
  unfold finiteDisjointAdjustment
  rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi])]
  abel

lemma finiteDisjointAdjustment_of_exterior [AddCommGroup F] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E}
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    {x : E} (hx : ∀ i ∈ s, x ∉ O i) :
    finiteDisjointAdjustment s n g x = n x := by
  unfold finiteDisjointAdjustment
  have hz : ∑ i ∈ s, (g i x-n x) = 0 := Finset.sum_eq_zero fun i hi => by
    rw [hext i hi x (hx i hi),sub_self]
  rw [hz,add_zero]

lemma finiteDisjointAdjustment_property [AddCommGroup F] [DecidableEq ι] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E} {U : Set E} {P : E → F → Prop}
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (O i) (O j))
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    (hn : ∀ x ∈ U, P x (n x))
    (hg : ∀ i ∈ s, ∀ x ∈ U ∩ O i, P x (g i x)) :
    ∀ x ∈ U, P x (finiteDisjointAdjustment s n g x) := by
  intro x hx
  by_cases hex : ∃ i ∈ s, x ∈ O i
  · obtain ⟨i,hi,hxi⟩ := hex
    rw [finiteDisjointAdjustment_of_mem hdisj hext hi hxi]
    exact hg i hi x ⟨hx,hxi⟩
  · have hout : ∀ i ∈ s, x ∉ O i := by
      intro i hi hxi
      exact hex ⟨i,hi,hxi⟩
    rw [finiteDisjointAdjustment_of_exterior hext hout]
    exact hn x hx

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingNormalPath
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preferred-normal adjustment at a crossing: a normalized straight path
stays away from both forbidden antipodes and ends with positive pairings. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma nonzero_of_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : v ≠ 0 := by
  intro hz
  rw [hz,zero_dotProduct] at h
  exact (lt_irrefl _ h)

lemma normalize_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : 0 < normalize v ⬝ᵥ m := by
  have hv := nonzero_of_dot_pos h
  have hnorm : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr (dot_self_pos hv)
  simpa only [normalize,smul_dotProduct,smul_eq_mul] using mul_pos (inv_pos.mpr hnorm) h

lemma crossing_blend_nonzero {n p m : Vec} {t : ℝ} (hn : n ⬝ᵥ n = 1)
    (hnm : n ⬝ᵥ m = 0) (hp : 0 < p ⬝ᵥ m) (ht : t ∈ Icc (0 : ℝ) 1) :
    blend n (normalize p) t ≠ 0 := by
  by_cases ht0 : t = 0
  · intro hz
    have hzero : n = 0 := by simpa only [blend,ht0,sub_zero,one_smul,zero_smul,add_zero] using hz
    rw [hzero,zero_dotProduct] at hn
    norm_num at hn
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    apply nonzero_of_dot_pos (m := m)
    simp only [blend,add_dotProduct,smul_dotProduct,smul_eq_mul,hnm,mul_zero,zero_add]
    exact mul_pos htp (normalize_dot_pos hp)

theorem crossing_normal_path {n p q m : Vec} (hn : n ⬝ᵥ n = 1)
    (hnm : n ⬝ᵥ m = 0) (hp : 0 < p ⬝ᵥ m) (hq : 0 < q ⬝ᵥ m)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    first n (normalize p) t ⬝ᵥ first n (normalize p) t = 1 ∧
    first n (normalize p) t ≠ -normalize p ∧
    first n (normalize p) t ≠ -normalize q := by
  have hb := crossing_blend_nonzero hn hnm hp ht
  have hbm : 0 ≤ blend n (normalize p) t ⬝ᵥ m := by
    simp only [blend,add_dotProduct,smul_dotProduct,smul_eq_mul,hnm,mul_zero,zero_add]
    exact mul_nonneg ht.1 (normalize_dot_pos hp).le
  have hfm : 0 ≤ first n (normalize p) t ⬝ᵥ m := by
    change 0 ≤ normalize (blend n (normalize p) t) ⬝ᵥ m
    simp only [normalize,smul_dotProduct,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hbm
  refine ⟨normalize_unit hb,?_,?_⟩
  · intro he
    rw [he,neg_dotProduct] at hfm
    linarith [normalize_dot_pos hp]
  · intro he
    rw [he,neg_dotProduct] at hfm
    linarith [normalize_dot_pos hq]

theorem crossing_normal_path_endpoint {n p q m : Vec}
    (hp : 0 < p ⬝ᵥ m) (hpq : 0 < p ⬝ᵥ q) :
    0 < p ⬝ᵥ first n (normalize p) 1 ∧ 0 < q ⬝ᵥ first n (normalize p) 1 := by
  rw [first_one (normalize_unit (nonzero_of_dot_pos hp))]
  constructor
  · rw [dotProduct_comm]
    exact normalize_dot_pos (dot_self_pos (nonzero_of_dot_pos hp))
  · rw [dotProduct_comm]
    exact normalize_dot_pos hpq

lemma crossing_normal_path_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n p m : E → Vec} {t : E → ℝ} {x : E}
    (hn : ContDiffAt ℝ ∞ n x) (hp : ContDiffAt ℝ ∞ p x) (ht : ContDiffAt ℝ ∞ t x)
    (hnn : n x ⬝ᵥ n x = 1) (hnm : n x ⬝ᵥ m x = 0)
    (hpm : 0 < p x ⬝ᵥ m x) (ht01 : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => first (n y) (normalize (p y)) (t y)) x :=
  first_smoothAt_of_nonzero hn (normalize_smoothAt hp (nonzero_of_dot_pos hpm)) ht
    (crossing_blend_nonzero hnn hnm hpm ht01)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SupportedCrossingAdjustment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localize a crossing-normal path by a smooth cutoff.  The resulting
section stays smooth even where the first pure vector vanishes outside
the cutoff support. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem supported_crossing_adjustment {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) {n p q m : E → Vec} {χ : E → ℝ}
    (hn : ContDiffOn ℝ ∞ n U) (hp : ContDiffOn ℝ ∞ p W)
    (hχ : ContDiff ℝ ∞ χ) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχsupport : tsupport χ ⊆ W) (hnunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1)
    (hgeom : ∀ x ∈ W, n x ⬝ᵥ m x = 0 ∧ 0 < p x ⬝ᵥ m x ∧
      0 < q x ⬝ᵥ m x ∧ 0 < p x ⬝ᵥ q x) :
    let g := fun x => first (n x) (normalize (p x)) (χ x)
    ContDiffOn ℝ ∞ g U ∧
      (∀ x ∈ U, g x ⬝ᵥ g x = 1) ∧
      (∀ x ∈ U, x ∉ tsupport χ → g x = n x) ∧
      (∀ x ∈ W, g x ≠ -normalize (p x) ∧ g x ≠ -normalize (q x)) ∧
      (∀ x ∈ W, χ x = 1 → 0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x) ∧
      (∀ x ∈ U, ∀ v : Vec, v ⬝ᵥ n x = 0 → v ⬝ᵥ p x = 0 → v ⬝ᵥ g x = 0) := by
  dsimp only
  have hzero (x : E) (hx : x ∉ tsupport χ) : χ x = 0 := by
    by_contra he
    exact hx (subset_tsupport χ (Function.mem_support.mpr he))
  have heq (x : E) (hxU : x ∈ U) (hx : x ∉ tsupport χ) :
      first (n x) (normalize (p x)) (χ x) = n x := by
    rw [hzero x hx,first_zero (hnunit x hxU)]
  refine ⟨?_,?_,heq,?_,?_,?_⟩
  · intro x hxU
    by_cases hxW : x ∈ W
    · exact (crossing_normal_path_smoothAt
        (hn.contDiffAt (hU.mem_nhds hxU)) (hp.contDiffAt (hW.mem_nhds hxW))
        hχ.contDiffAt (hnunit x hxU) (hgeom x hxW).1 (hgeom x hxW).2.1
        (hχrange x)).contDiffWithinAt
    · have hx : x ∉ tsupport χ := fun h => hxW (hχsupport h)
      apply ((hn.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx,hU.mem_nhds hxU] with y hy hyU
      simp only [Pi.zero_apply] at hy
      rw [hy,first_zero (hnunit y hyU)]
  · intro x hxU
    by_cases hxW : x ∈ W
    · exact (crossing_normal_path (hnunit x hxU) (hgeom x hxW).1
        (hgeom x hxW).2.1 (hgeom x hxW).2.2.1 (hχrange x)).1
    · rw [heq x hxU (fun h => hxW (hχsupport h))]
      exact hnunit x hxU
  · intro x hx
    exact (crossing_normal_path (hnunit x (hWU hx)) (hgeom x hx).1
      (hgeom x hx).2.1 (hgeom x hx).2.2.1 (hχrange x)).2
  · intro x hx hχx
    rw [hχx]
    exact crossing_normal_path_endpoint (hgeom x hx).2.1 (hgeom x hx).2.2.2
  · intro x _ v hvn hvp
    change v ⬝ᵥ normalize (blend (n x) (normalize (p x)) (χ x)) = 0
    apply dot_normalize_zero
    simp only [blend,dotProduct_add,dotProduct_smul,smul_eq_mul,hvn,
      show v ⬝ᵥ normalize (p x) = 0 from dot_normalize_zero hvp,mul_zero,add_zero]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a pointwise common half-plane to a neighborhood, with an
explicit smooth transverse vector field. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem crossing_halfplane_neighborhood {U : Set E} (hU : IsOpen U)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1) {x : E} (hx : x ∈ U) {w : Vec}
    (hnw : n x ⬝ᵥ w = 0) (hpw : 0 < p x ⬝ᵥ w) (hqw : 0 < q x ⬝ᵥ w)
    (hpq : 0 < p x ⬝ᵥ q x) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ m : E → Vec, ContDiffOn ℝ ∞ m U ∧
        ∀ y ∈ W, n y ⬝ᵥ m y = 0 ∧ 0 < p y ⬝ᵥ m y ∧
          0 < q y ⬝ᵥ m y ∧ 0 < p y ⬝ᵥ q y := by
  let m : E → Vec := fun y => w-(n y ⬝ᵥ w) • n y
  have hm : ContDiffOn ℝ ∞ m U :=
    contDiffOn_const.sub ((dot_smoothOn hn contDiffOn_const).smul hn)
  have hmx : m x = w := by simp [m,hnw]
  have hP : ∀ᶠ y in 𝓝 x, 0 < p y ⬝ᵥ m y :=
    ((dot_smoothOn hp hm).contDiffAt (hU.mem_nhds hx)).continuousAt
      (Ioi_mem_nhds (by simpa only [hmx] using hpw))
  have hQ : ∀ᶠ y in 𝓝 x, 0 < q y ⬝ᵥ m y :=
    ((dot_smoothOn hq hm).contDiffAt (hU.mem_nhds hx)).continuousAt
      (Ioi_mem_nhds (by simpa only [hmx] using hqw))
  have hPQ : ∀ᶠ y in 𝓝 x, 0 < p y ⬝ᵥ q y :=
    ((dot_smoothOn hp hq).contDiffAt (hU.mem_nhds hx)).continuousAt (Ioi_mem_nhds hpq)
  have hnb : {y | y ∈ U ∧ 0 < p y ⬝ᵥ m y ∧ 0 < q y ⬝ᵥ m y ∧ 0 < p y ⬝ᵥ q y} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hP,hQ,hPQ] with y hy hyP hyQ hyPQ
    exact ⟨hy,hyP,hyQ,hyPQ⟩
  obtain ⟨W,hsub,hW,hxW⟩ := mem_nhds_iff.mp hnb
  refine ⟨W,hW,hxW,fun y hy => (hsub hy).1,m,hm,?_⟩
  intro y hy
  obtain ⟨hyU,hyP,hyQ,hyPQ⟩ := hsub hy
  refine ⟨?_,hyP,hyQ,hyPQ⟩
  simp only [m,dotProduct_sub,dotProduct_smul,smul_eq_mul,hunit y hyU,mul_one,sub_self]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalCrossingAdjustment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the local normal change at one crossing with support in any
prescribed neighborhood. No normal path or cutoff is assumed. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_crossing_adjustment {U O : Set E} (hU : IsOpen U) (hO : IsOpen O)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1) {x : E} (hx : x ∈ U) (hxO : x ∈ O)
    {w : Vec} (hnw : n x ⬝ᵥ w = 0) (hpw : 0 < p x ⬝ᵥ w)
    (hqw : 0 < q x ⬝ᵥ w) (hpq : 0 < p x ⬝ᵥ q x) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, y ∉ O → g y = n y) ∧
      (∀ y ∈ U, n y ≠ -normalize (p y) → g y ≠ -normalize (p y)) ∧
      (∀ y ∈ U, n y ≠ -normalize (q y) → g y ≠ -normalize (q y)) ∧
      (∀ y ∈ U, ∀ v : Vec, v ⬝ᵥ n y = 0 → v ⬝ᵥ p y = 0 → v ⬝ᵥ g y = 0) ∧
      0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x := by
  obtain ⟨W,hW,hxW,hWU,m,_,hgeom⟩ :=
    crossing_halfplane_neighborhood hU hn hp hq hunit hx hnw hpw hqw hpq
  obtain ⟨χ,hχ,_,hχrange,hχsupport,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_singleton : IsCompact ({x} : Set E)) (hW.inter hO)
    (by intro y hy; simpa only [mem_inter_iff,mem_singleton_iff.mp hy] using And.intro hxW hxO)
  have hs : tsupport χ ⊆ W := hχsupport.trans inter_subset_left
  obtain ⟨hg,hgu,hge,hga,hgpos,hgperp⟩ := supported_crossing_adjustment hU hW hWU
    hn (hp.mono hWU) hχ hχrange hs hunit hgeom
  let g : E → Vec := fun y => first (n y) (normalize (p y)) (χ y)
  have hpos := hgpos x hxW (hχone x (mem_singleton x))
  refine ⟨g,hg,hgu,?_,?_,?_,hgperp,hpos⟩
  · intro y hy hyO
    exact hge y hy (fun h => hyO (hχsupport h).2)
  · intro y hy hanti
    by_cases hyW : y ∈ W
    · exact (hga y hyW).1
    · exact fun he => hanti ((hge y hy (fun h => hyW (hs h))).symm.trans he)
  · intro y hy hanti
    by_cases hyW : y ∈ W
    · exact (hga y hyW).2
    · exact fun he => hanti ((hge y hy (fun h => hyW (hs h))).symm.trans he)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalCrossingChoice
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise turn alternative supplies the actual supported normal
adjustment, including the case where the original normal already works. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_crossing_adjustment_of_choice {U O : Set E} (hU : IsOpen U) (hO : IsOpen O)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1) {x : E} (hx : x ∈ U) (hxO : x ∈ O)
    (hchoice : (0 < p x ⬝ᵥ n x ∧ 0 < q x ⬝ᵥ n x) ∨
      (0 < p x ⬝ᵥ q x ∧ ∃ w : Vec, n x ⬝ᵥ w = 0 ∧
        0 < p x ⬝ᵥ w ∧ 0 < q x ⬝ᵥ w)) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, y ∉ O → g y = n y) ∧
      (∀ y ∈ U, n y ≠ -normalize (p y) → g y ≠ -normalize (p y)) ∧
      (∀ y ∈ U, n y ≠ -normalize (q y) → g y ≠ -normalize (q y)) ∧
      (∀ y ∈ U, ∀ v : Vec, v ⬝ᵥ n y = 0 → v ⬝ᵥ p y = 0 → v ⬝ᵥ g y = 0) ∧
      0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x := by
  rcases hchoice with hpos | ⟨hpq,w,hnw,hpw,hqw⟩
  · exact ⟨n,hn,hunit,fun _ _ _ => rfl,fun _ _ h => h,fun _ _ h => h,
      fun _ _ _ h _ => h,hpos⟩
  · exact local_crossing_adjustment hU hO hn hp hq hunit hx hxO hnw hpw hqw hpq

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteCrossingNormals
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous normal adjustments at the finitely many later crossings.
Disjoint supports preserve the other curves and the exterior normal exactly. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_crossing_normals {U : Set E} (hU : IsOpen U)
    {n : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1)
    (v : κ → E → Vec) (hv : ∀ k, ContDiffOn ℝ ∞ (v k) U)
    (left right : ι → κ) (x : ι → E) (hx : ∀ i, x i ∈ U)
    (O : ι → Set E) (hO : ∀ i, IsOpen (O i)) (hxo : ∀ i, x i ∈ O i)
    (hdisj : Pairwise fun i j => Disjoint (O i) (O j))
    (C : κ → Set E)
    (hcurves : ∀ i k y, y ∈ O i → y ∈ C k → k = left i ∨ k = right i)
    (hchoice : ∀ i,
      (0 < v (left i) (x i) ⬝ᵥ n (x i) ∧ 0 < v (right i) (x i) ⬝ᵥ n (x i)) ∨
      (0 < v (left i) (x i) ⬝ᵥ v (right i) (x i) ∧
        ∃ w : Vec, n (x i) ⬝ᵥ w = 0 ∧
          0 < v (left i) (x i) ⬝ᵥ w ∧ 0 < v (right i) (x i) ⬝ᵥ w)) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, (∀ i, y ∉ O i) → g y = n y) ∧
      (∀ k y, y ∈ U → y ∈ C k → n y ≠ -normalize (v k y) →
        g y ≠ -normalize (v k y)) ∧
      (∀ y ∈ U, ∀ w : Vec, w ⬝ᵥ n y = 0 →
        (∀ k, w ⬝ᵥ v k y = 0) → w ⬝ᵥ g y = 0) ∧
      ∀ i, 0 < v (left i) (x i) ⬝ᵥ g (x i) ∧
        0 < v (right i) (x i) ⬝ᵥ g (x i) := by
  classical
  choose f hfs hfu hfe hfl hfr hfn hfp using fun i =>
    local_crossing_adjustment_of_choice hU (hO i) hn (hv (left i)) (hv (right i))
      hunit (hx i) (hxo i) (hchoice i)
  let f' : ι → E → Vec := fun i y => if y ∈ U then f i y else n y
  have hfeq (i : ι) {y : E} (hy : y ∈ U) : f' i y = f i y := by simp only [f',hy,ite_true, if_true]
  have hfext : ∀ i ∈ (Finset.univ : Finset ι), ∀ y ∉ O i, f' i y = n y := by
    intro i _ y hy
    by_cases hyU : y ∈ U
    · rw [hfeq i hyU]
      exact hfe i y hyU hy
    · simp only [f',hyU,ite_false, if_false]
  have hd : ((Finset.univ : Finset ι) : Set ι).Pairwise fun i j => Disjoint (O i) (O j) :=
    fun i _ j _ hij => hdisj hij
  let g := finiteDisjointAdjustment Finset.univ n f'
  have heq (i : ι) {y : E} (hy : y ∈ U) (hyO : y ∈ O i) : g y = f i y :=
    (finiteDisjointAdjustment_of_mem hd hfext (Finset.mem_univ i) hyO).trans (hfeq i hy)
  have hprop {P : E → Vec → Prop} (hnP : ∀ y ∈ U, P y (n y))
      (hfP : ∀ i y, y ∈ U ∩ O i → P y (f i y)) : ∀ y ∈ U, P y (g y) := by
    apply finiteDisjointAdjustment_property hd hfext hnP
    intro i _ y hy
    rw [hfeq i hy.1]
    exact hfP i y hy
  refine ⟨g,?_,?_,?_,?_,?_,?_⟩
  · apply finiteDisjointAdjustment_smoothOn hn
    intro i _
    apply (hfs i).congr
    intro y hy
    exact hfeq i hy
  · exact hprop (P := fun _ a => a ⬝ᵥ a = 1) hunit (fun i y hy => hfu i y hy.1)
  · intro y _ hy
    exact finiteDisjointAdjustment_of_exterior hfext (fun i _ => hy i)
  · intro k y hy hyC hanti
    apply hprop (P := fun z a => z ∈ C k → n z ≠ -normalize (v k z) → a ≠ -normalize (v k z))
      (fun _ _ _ h => h) ?_ y hy hyC hanti
    intro i z hz hzC hzanti
    rcases hcurves i k z hz.2 hzC with rfl | rfl
    · exact hfl i z hz.1 hzanti
    · exact hfr i z hz.1 hzanti
  · intro y hy w hwn hwv
    exact hprop (P := fun z a => w ⬝ᵥ n z = 0 → (∀ k, w ⬝ᵥ v k z = 0) → w ⬝ᵥ a = 0)
      (fun _ _ h _ => h)
      (fun i z hz h hzv => hfn i z hz.1 w h (hzv (left i))) y hy hwn hwv
  · intro i
    rw [heq i (hx i) (hxo i)]
    exact hfp i

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualFiniteCrossingNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite crossing construction applied to the actual second form of
one immersion, with its canonical transverse preferred normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem actual_finite_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {U V : Set Base} (hV : IsOpen V)
    (hreg : ∀ y ∈ U, realBoundaryProfile F z y ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiffOn ℝ ∞ (Y k) U)
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxU : ∀ i, x i ∈ U) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (hchoice : ∀ i,
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i)) ∧
       0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i))) ∨
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ w))
    (hU : IsOpen U) :
    ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, ∀ w : Base, coordDeriv w F y ⬝ᵥ g y = 0) ∧
      (∀ y ∈ U, y ∉ V → g y = profilePreferred (realBoundaryProfile F z y)) ∧
      (∀ k y, y ∈ U → y ∈ C k →
        profilePreferred (realBoundaryProfile F z y) ≠
          -normalize (realSecondForm F (Y k y) (Y k y) y) →
        g y ≠ -normalize (realSecondForm F (Y k y) (Y k y) y)) ∧
      ∀ i, 0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  let n : Base → Vec := fun y => profilePreferred (realBoundaryProfile F z y)
  let P : κ → Base → Vec := fun k y => realSecondForm F (Y k y) (Y k y) y
  have hD : ∀ y ∈ U, gramDet (coordDeriv dx F y) (coordDeriv dy F y) ≠ 0 :=
    fun y hy => (hreg y hy).1
  have hPs : ∀ k, ContDiffOn ℝ ∞ (P k) U :=
    fun k => realSecondForm_variable_smoothOn hF hD (hY k)
  have hns : ContDiffOn ℝ ∞ n U := profilePreferred_field_smoothOn hF z hreg
  have hnu : ∀ y ∈ U, n y ⬝ᵥ n y = 1 := fun y hy => profilePreferred_unit (hreg y hy)
  obtain ⟨O,hO,hxo,hOV,hdisj,hcurve⟩ := finite_crossing_neighborhoods x hxinj left right C hC honly
    (fun _ => V) (fun _ => hV) hxV
  obtain ⟨g,hg,hgu,hge,hga,hgn,hgp⟩ := finite_crossing_normals hU hns hnu P hPs left right x hxU
    O hO hxo hdisj C hcurve hchoice
  refine ⟨g,hg,hgu,?_,?_,hga,hgp⟩
  · intro y hy w
    have hnperp := profilePreferred_perp (hreg y hy)
    have hperp (d : Base) (hd : coordDeriv d F y ⬝ᵥ n y = 0)
        (hsecond : ∀ k, coordDeriv d F y ⬝ᵥ P k y = 0) : coordDeriv d F y ⬝ᵥ g y = 0 :=
      hgn y hy _ hd hsecond
    have hxg := hperp dx hnperp.1
      (fun k => (realSecondForm_field_perp (hD y hy) (Y k y) (Y k y)).1)
    have hyg := hperp dy hnperp.2
      (fun k => (realSecondForm_field_perp (hD y hy) (Y k y) (Y k y)).2)
    rw [coordDeriv_eq_basis F w y]
    simp only [add_dotProduct,smul_dotProduct,smul_eq_mul,hxg,hyg,mul_zero,add_zero]
  · intro y hy hyV
    exact hge y hy (fun i h => hyV (hOV i h))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CompactCrossingNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn regularity on a compact disk and finitely many actual crossing
choices into one smooth normal on an open neighborhood of the disk. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem compact_actual_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {T V : Set Base} (hV : IsOpen V)
    (hreg : ∀ p ∈ T, realBoundaryProfile F z p ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiff ℝ ∞ (Y k))
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxT : ∀ i, x i ∈ T) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (havoid : ∀ k p, p ∈ T → p ∈ C k →
      normalize (realSecondForm F (Y k p) (Y k p) p) ≠ -profilePreferred (realBoundaryProfile F z p))
    (hchoice : ∀ i,
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i)) ∧
       0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i))) ∨
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ w)) :
    ∃ U : Set Base, IsOpen U ∧ T ⊆ U ∧ ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ p ∈ U, g p ⬝ᵥ g p = 1) ∧
      (∀ p ∈ U, ∀ v : Base, coordDeriv v F p ⬝ᵥ g p = 0) ∧
      (∀ p ∈ U, p ∉ V → g p = profilePreferred (realBoundaryProfile F z p)) ∧
      (∀ k p, p ∈ T → p ∈ C k → g p ≠ -normalize (realSecondForm F (Y k p) (Y k p) p)) ∧
      ∀ i, 0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  let U := realBoundaryProfile F z ⁻¹' regularBoundaryProfiles
  have hU : IsOpen U := isOpen_regularBoundaryProfiles.preimage (realBoundaryProfile_smooth hF z).continuous
  have hTU : T ⊆ U := hreg
  obtain ⟨g,hg,hunit,hnormal,hout,havoid',hpos⟩ := actual_finite_crossing_normal hF z hV
    (fun _ hp => hp) Y (fun k => (hY k).contDiffOn) left right x hxinj
    (fun i => hTU (hxT i)) hxV C hC honly hchoice hU
  refine ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,?_,hpos⟩
  intro k p hpT hpC
  apply havoid' k p (hTU hpT) hpC
  intro hbad
  apply havoid k p hpT hpC
  rw [hbad,neg_neg]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingChoiceScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Crossing normal choices are invariant under the positive squares arising
when a nonvertical curve direction is written in slope coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma crossing_choice_scale {n p q : Vec} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hchoice : (0 < p ⬝ᵥ n ∧ 0 < q ⬝ᵥ n) ∨
      (0 < p ⬝ᵥ q ∧ ∃ w : Vec, n ⬝ᵥ w = 0 ∧ 0 < p ⬝ᵥ w ∧ 0 < q ⬝ᵥ w)) :
    (0 < (r • p) ⬝ᵥ n ∧ 0 < (s • q) ⬝ᵥ n) ∨
      (0 < (r • p) ⬝ᵥ (s • q) ∧ ∃ w : Vec, n ⬝ᵥ w = 0 ∧
        0 < (r • p) ⬝ᵥ w ∧ 0 < (s • q) ⬝ᵥ w) := by
  rcases hchoice with ⟨hp,hq⟩ | ⟨hpq,w,hnw,hpw,hqw⟩
  · left
    simpa only [smul_dotProduct,smul_eq_mul] using And.intro (mul_pos hr hp) (mul_pos hs hq)
  · right
    refine ⟨?_,w,hnw,?_,?_⟩
    · simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul,mul_assoc] using mul_pos hs (mul_pos hr hpq)
    · simpa only [smul_dotProduct,smul_eq_mul] using mul_pos hr hpw
    · simpa only [smul_dotProduct,smul_eq_mul] using mul_pos hs hqw

lemma realSecondForm_smul_self {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (r : ℝ) (v p : Base) :
    realSecondForm F (r • v) (r • v) p = r^2 • realSecondForm F v v p := by
  rw [realSecondForm_quadratic hF,PhaseGeometry.secondQuadratic_smul,
    ← realSecondForm_quadratic hF]

lemma realSecondForm_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (b c : ℝ) (p : Base) (hb : b ≠ 0) :
    realSecondForm F (b,c) (b,c) p = b^2 • realSecondForm F (1,c/b) (1,c/b) p := by
  have hv : (b,c) = b • ((1,c/b) : Base) := by
    apply Prod.ext
    · simp
    · change c = b*(c/b)
      field_simp
  rw [hv,realSecondForm_smul_self hF]

lemma crossing_choice_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : Vec) (v w : Base) (hv : v.1 ≠ 0) (hw : w.1 ≠ 0)
    (hchoice :
      (0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ n ∧
       0 < realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ⬝ᵥ n) ∨
      (0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ
        realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ∧
       ∃ a : Vec, n ⬝ᵥ a = 0 ∧
        0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ a ∧
        0 < realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ⬝ᵥ a)) :
    (0 < realSecondForm F v v p ⬝ᵥ n ∧ 0 < realSecondForm F w w p ⬝ᵥ n) ∨
      (0 < realSecondForm F v v p ⬝ᵥ realSecondForm F w w p ∧
       ∃ a : Vec, n ⬝ᵥ a = 0 ∧
        0 < realSecondForm F v v p ⬝ᵥ a ∧ 0 < realSecondForm F w w p ⬝ᵥ a) := by
  have h := crossing_choice_scale (sq_pos_of_ne_zero hv) (sq_pos_of_ne_zero hw) hchoice
  rw [← realSecondForm_firstSlope hF v.1 v.2 p hv,
    ← realSecondForm_firstSlope hF w.1 w.2 p hw] at h
  exact h

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingInvariantScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both ordered crossing invariants scale by the positive product of
squared changes in the two tangent directions. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma normalize_pos_smul (v : Vec) {c : ℝ} (hc : 0 < c) :
    VelocityFrame.normalize (c • v) = VelocityFrame.normalize v := by
  have hs : Real.sqrt ((c • v) ⬝ᵥ (c • v)) = c*Real.sqrt (v ⬝ᵥ v) := by
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
    rw [← mul_assoc,← pow_two,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le]
  simp only [VelocityFrame.normalize,hs,mul_inv_rev,smul_smul]
  congr 1
  field_simp

lemma realSecondForm_smul_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (r s : ℝ) (v w p : Base) :
    realSecondForm F (r • v) (s • w) p = (r*s) • realSecondForm F v w p := by
  rw [realSecondForm_bilinear hF,realSecondForm_bilinear hF]
  ext j
  simp [realSecondTensor]
  ring

lemma gramDet_smul_directions (X Y : Vec) (r s : ℝ) :
    NormalFrame.gramDet (r • X) (s • Y) = r^2*s^2*NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma orderedCrossing_smul_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {r s : ℝ} (hr : r ≠ 0) (v w p : Base) (κ : ℝ) :
    orderedCrossing F (r • v) (s • w) p κ = r^2*s^2*orderedCrossing F v w p κ := by
  have hd (t : ℝ) (u : Base) : coordDeriv (t • u) F p = t • coordDeriv u F p := by
    simp [coordDeriv]
  simp only [orderedCrossing,realSecondForm_smul_directions hF,
    show r*r=r^2 by ring,normalize_pos_smul _ (sq_pos_of_ne_zero hr),
    hd,gramDet_smul_directions,smul_dotProduct,smul_eq_mul]
  ring

lemma orderedCrossing_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) (κ : ℝ) (hv : v.1 ≠ 0) (hw : w.1 ≠ 0) :
    orderedCrossing F v w p κ = v.1^2*w.1^2*
      orderedCrossing F (1,v.2/v.1) (1,w.2/w.1) p κ := by
  have hh (u : Base) (hu : u.1 ≠ 0) : u.1 • ((1,u.2/u.1) : Base) = u := by
    apply Prod.ext
    · simp
    · change u.1*(u.2/u.1)=u.2
      field_simp
  convert orderedCrossing_smul_directions hF hv ((1,v.2/v.1) : Base)
    ((1,w.2/w.1) : Base) p κ (s := w.1) using 1
  all_goals try with_reducible_and_instances rfl
  rw [hh v hv,hh w hw]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactSlopeNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual preferred normal from the slope-coordinate
estimates, retaining both ordered invariants in the original directions. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem compact_slope_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {T V : Set Base} (hV : IsOpen V)
    (hreg : ∀ p ∈ T, realBoundaryProfile F z p ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiff ℝ ∞ (Y k))
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxT : ∀ i, x i ∈ T) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (havoid : ∀ k p, p ∈ T → p ∈ C k →
      normalize (realSecondForm F (Y k p) (Y k p) p) ≠ -profilePreferred (realBoundaryProfile F z p))
    (hv : ∀ i, (Y (left i) (x i)).1 ≠ 0 ∧ (Y (right i) (x i)).1 ≠ 0)
    (d : ℝ) (hd : ∀ i, |(Y (left i) (x i)).2/(Y (left i) (x i)).1| ≤ d ∧
      |(Y (right i) (x i)).2/(Y (right i) (x i)).1| ≤ d)
    (curv : Base → ℝ)
    (hcross : ∀ i, ∀ r s : ℝ, |r| ≤ d → |s| ≤ d →
      0 < orderedCrossing F (1,r) (1,s) (x i) (curv (x i)) ∧
      0 < orderedCrossing F (1,s) (1,r) (x i) (curv (x i)) ∧
      ((0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ profilePreferred (realBoundaryProfile F z (x i)) ∧
        0 < realSecondForm F (1,s) (1,s) (x i) ⬝ᵥ profilePreferred (realBoundaryProfile F z (x i))) ∨
       (0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ realSecondForm F (1,s) (1,s) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (1,s) (1,s) (x i) ⬝ᵥ w))) :
    ∃ U : Set Base, IsOpen U ∧ T ⊆ U ∧ ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ p ∈ U, g p ⬝ᵥ g p = 1) ∧
      (∀ p ∈ U, ∀ v : Base, coordDeriv v F p ⬝ᵥ g p = 0) ∧
      (∀ p ∈ U, p ∉ V → g p = profilePreferred (realBoundaryProfile F z p)) ∧
      (∀ k p, p ∈ T → p ∈ C k → g p ≠ -normalize (realSecondForm F (Y k p) (Y k p) p)) ∧
      ∀ i,
        0 < orderedCrossing F (Y (left i) (x i)) (Y (right i) (x i)) (x i) (curv (x i)) ∧
        0 < orderedCrossing F (Y (right i) (x i)) (Y (left i) (x i)) (x i) (curv (x i)) ∧
        0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  have hdata (i : ι) := hcross i _ _ (hd i).1 (hd i).2
  obtain ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,havoid',hpos⟩ := compact_actual_crossing_normal
    hF z hV hreg Y hY left right x hxinj hxT hxV C hC honly havoid
    (fun i => crossing_choice_firstSlope hF (x i) (profilePreferred (realBoundaryProfile F z (x i)))
      _ _ (hv i).1 (hv i).2 (hdata i).2.2)
  refine ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,havoid',?_⟩
  intro i
  have hp := mul_pos (sq_pos_of_ne_zero (hv i).1) (sq_pos_of_ne_zero (hv i).2)
  refine ⟨?_,?_,(hpos i).1,(hpos i).2⟩
  · rw [orderedCrossing_firstSlope hF _ _ _ _ (hv i).1 (hv i).2]
    exact mul_pos hp (hdata i).1
  · rw [orderedCrossing_firstSlope hF _ _ _ _ (hv i).2 (hv i).1]
    exact mul_pos (by simpa [mul_comm] using hp) (hdata i).2.1

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentPreservingNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_preservingCircularNormalDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_preservingCircularNormalFiberSpace
local instance independent_preservingCircularNormalDualSmul_r1ebd36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_preservingCircularNormalFiberNormed
local instance independent_preservingCircularNormalSectionNormed_r1ebd36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_preservingCircularNormalSectionSpace_r1ebd36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_preserving_circular_primitive_normal [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      0 < ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx
        (A₀.phaseRealChartMap i e.symm F)) x ⬝ᵥ
        normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x))*b j x +
        Real.sqrt (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x ⬝ᵥ
          realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x)*c j x)^2 + (coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)*(b j x)^2)

    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
    (hxE : ∀ j, x j ∈ E)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
    (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
    (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
    (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)
 :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      (∃ U₀ : Set SmallModes.Base, IsOpen U₀ ∧ baseEquiv '' C ⊆ U₀ ∧
        ∃ ν : SmallModes.Base → NormalFrame.Vec, ContDiffOn ℝ ∞ ν U₀ ∧
          (∀ p ∈ U₀, ν p ⬝ᵥ ν p = 1) ∧
          (∀ p ∈ U₀, ∀ v : SmallModes.Base,
            SmallModes.coordDeriv v (A₀.phaseRealChartMap i e.symm W) p ⬝ᵥ ν p = 0) ∧
          (∀ p ∈ U₀, p ∉ V → ν p =
            profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z p)) ∧
          (∀ j p, p ∈ Curves j → ν p ≠ -normalize
            (realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j p,c j p) (b j p,c j p) p)) ∧
          ∀ j,
            let H := A₀.phaseRealChartMap i e.symm W
            let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
              (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) (x j)
            0 < orderedCrossing H (b (left j) (x j),c (left j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) κ ∧
            0 < orderedCrossing H (b (right j) (x j),c (right j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) κ ∧
            0 < realSecondForm H (b (left j) (x j),c (left j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) ⬝ᵥ ν (x j) ∧
            0 < realSecondForm H (b (right j) (x j),c (right j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) ⬝ᵥ ν (x j)) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  intro ε hε ζ hζ
  obtain ⟨z,hz,hzζ,hz1,W,hW,hdata,hreg,havoid,hcross,hrest⟩ :=
    data.independent_preserving_circular_primitive_boundary A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      ha hT hU hTU hn hI hN hHess haT hboundary hCurves hCurvesT hP hlocal hE hET haE
      slopeBound hSlope hb hc hbc S hSc hTS hST K hK hKS hKA hone haoff ℓ hℓx hℓy
      h htarget hC hCS hCurveC hactiveC hEC hold ε hε ζ hζ
  let H := A₀.phaseRealChartMap i e.symm W
  let Y : ι → SmallModes.Base → SmallModes.Base := fun j p => (b j p,c j p)
  have hmem (j : ι) (p : SmallModes.Base) (hp : p ∈ Curves j) : p ∈ baseEquiv '' C :=
    ⟨baseEquiv.symm p,hCurveC j p hp,baseEquiv.apply_symm_apply p⟩
  obtain ⟨U₀,hU₀,hCU₀,ν,hν,hνunit,hνnormal,hνout,hνavoid,hνcross⟩ :=
    compact_slope_crossing_normal (T := baseEquiv '' C) (A₀.phaseRealChartMap_smooth i hi hW.1) z hV
      (by rintro _ ⟨p,hp,rfl⟩; exact hreg p hp) Y (fun j => (hb j).prodMk (hc j))
      left right x hxinj
      (fun j => ⟨baseEquiv.symm (x j),hEC _ (hxE j),baseEquiv.apply_symm_apply _⟩)
      hxV Curves (fun j => (hCurves j).isClosed) honly
      (fun j p _ hp => (havoid j p hp).2) hfirst slopeBound hslopes
      (coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
        (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy))
      (fun j => hcross (x j) (hxE j))
  refine ⟨z,hz,hzζ,hz1,W,hW,hdata,hreg,havoid,hcross,?_,hrest⟩
  exact ⟨U₀,hU₀,hCU₀,ν,hν,hνunit,hνnormal,hνout,
    (fun j p hp => hνavoid j p (hmem j p hp) hp),hνcross⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentGeometricNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_geometricCircularNormalDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_geometricCircularNormalFiberSpace
local instance independent_geometricCircularNormalDualSmul_r1ebd36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_geometricCircularNormalFiberNormed
local instance independent_geometricCircularNormalSectionNormed_r1ebd36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_geometricCircularNormalSectionSpace_r1ebd36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_geometric_circular_primitive_normal [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (ha0 : ∀ p, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      let H := A₀.phaseRealChartMap i e.symm F
      let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
        (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) x
      0 < orderedCrossing H SmallModes.dy (b j x,c j x) x κ)

    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
    (hxE : ∀ j, x j ∈ E)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
    (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
    (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
    (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)
 :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      (∃ U₀ : Set SmallModes.Base, IsOpen U₀ ∧ baseEquiv '' C ⊆ U₀ ∧
        ∃ ν : SmallModes.Base → NormalFrame.Vec, ContDiffOn ℝ ∞ ν U₀ ∧
          (∀ p ∈ U₀, ν p ⬝ᵥ ν p = 1) ∧
          (∀ p ∈ U₀, ∀ v : SmallModes.Base,
            SmallModes.coordDeriv v (A₀.phaseRealChartMap i e.symm W) p ⬝ᵥ ν p = 0) ∧
          (∀ p ∈ U₀, p ∉ V → ν p =
            profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z p)) ∧
          (∀ j p, p ∈ Curves j → ν p ≠ -normalize
            (realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j p,c j p) (b j p,c j p) p)) ∧
          ∀ j,
            let H := A₀.phaseRealChartMap i e.symm W
            let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
              (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) (x j)
            0 < orderedCrossing H (b (left j) (x j),c (left j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) κ ∧
            0 < orderedCrossing H (b (right j) (x j),c (right j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) κ ∧
            0 < realSecondForm H (b (left j) (x j),c (left j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) ⬝ᵥ ν (x j) ∧
            0 < realSecondForm H (b (right j) (x j),c (right j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) ⬝ᵥ ν (x j)) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hFiso : IsSmoothIsometricImmersion M g F := ⟨hF,fun p v w => by rw [hmetric]; rfl⟩
  have hs : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      0 < ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx
        (A₀.phaseRealChartMap i e.symm F)) x ⬝ᵥ
        normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x))*b j x +
        Real.sqrt (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x ⬝ᵥ
          realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x)*c j x)^2 + (coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)*(b j x)^2 := by
    intro j x hx hz
    have hcx := hCurveC j x hx
    have hd := RealModes.gramDet_ne_zero_of_injective _ (hI x (hTU (hCurvesT j hx)))
    rw [← A₀.phase_primitive_boundary_crossing i e he hi hFiso h hχ ha htarget
      (hCS hcx).2 (hactiveC _ hcx) hz (Filter.Eventually.of_forall ha0) hd
      (hboundary x (hCurvesT j hx) hz).1 (b j x) (c j x)]
    exact hold j x hx hz
  exact data.independent_preserving_circular_primitive_normal A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    ha hT hU hTU hn hI hN hHess (fun p _ => ha0 p) hboundary hCurves hCurvesT hP hlocal
    hE hET haE slopeBound hSlope hb hc hbc S hSc hTS hST K hK hKS hKA hone haoff
    ℓ hℓx hℓy h htarget hC hCS hCurveC hactiveC hEC hs left right x hxinj hxE
    hV hxV honly hfirst hslopes

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentGlobalNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_globalCircularNormalDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_globalCircularNormalFiberSpace
local instance independent_globalCircularNormalDualSmul_r1ebd36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_globalCircularNormalFiberNormed
local instance independent_globalCircularNormalSectionNormed_r1ebd36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_globalCircularNormalSectionSpace_r1ebd36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_global_circular_primitive_normal_oai [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (ha0 : ∀ p, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      let H := A₀.phaseRealChartMap i e.symm F
      let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
        (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) x
      0 < orderedCrossing H SmallModes.dy (b j x,c j x) x κ)

    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
    (hxE : ∀ j, x j ∈ E)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
    (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
    (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
    (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)    (B : SmoothingAtlas M) (curves : ι → PhaseBoundaryCurve B)
    (n₀ : PreferredNormal F)
    (hglobal : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize ((curves j).second F p))
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A₀.weight i p ≠ 0)
    (E₀ : Set M) (hE₀ : E₀.Finite) (hE₀f : Disjoint E₀ (frontier D))
    (hsupport : A₀.phaseSurfaceSupport i e K = closure D)
    (hDC : ∀ p ∈ closure D, e (chart (i : M) p) ∈ C)
    (hcurveChart : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      baseEquiv (e (chart (i : M) p)) ∈ Curves j)
    (hvector : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      (b j (baseEquiv (e (chart (i : M) p))),c j (baseEquiv (e (chart (i : M) p)))) =
        fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase (i : M) e)
          ((curves j).coordinate p) SmallModes.dy)
    (hworldBoundary : ∀ p ∈ frontier D,
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F)
        SmallModes.dy SmallModes.dy (baseEquiv (e (chart (i : M) p)))))
    (haFrontier : ∀ p ∈ frontier D, a (baseEquiv (e (chart (i : M) p))) = 0)
    (hpositive : ∀ j p, p ∈ (curves j).carrier → p ∈ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p))
    (hVfrontier : ∀ p ∈ frontier D, baseEquiv (e (chart (i : M) p)) ∉ V)
    (hσD : ∀ j, (surfacePhaseChart (i : M) e).symm (x j) ∈ E₀ ∩ D) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        (∀ j p, p ∈ (curves j).carrier → (curves j).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves j).second W p)) ∧
        (∀ p ∈ E₀, p ∉ D → N.vector p = A₀.unitProjectedNormalField W n₀.vector p) ∧
        (∀ j,
          let H := A₀.phaseRealChartMap i e.symm W
          let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
            (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) (x j)
          let p := (surfacePhaseChart (i : M) e).symm (x j)
          0 < orderedCrossing H (b (left j) (x j),c (left j) (x j))
            (b (right j) (x j),c (right j) (x j)) (x j) κ ∧
          0 < orderedCrossing H (b (right j) (x j),c (right j) (x j))
            (b (left j) (x j),c (left j) (x j)) (x j) κ ∧
          0 < realSecondForm H (b (left j) (x j),c (left j) (x j))
            (b (left j) (x j),c (left j) (x j)) (x j) ⬝ᵥ spaceCoordinates (N.vector p) ∧
          0 < realSecondForm H (b (right j) (x j),c (right j) (x j))
            (b (right j) (x j),c (right j) (x j)) (x j) ⬝ᵥ spaceCoordinates (N.vector p)) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
          ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hFiso : IsSmoothIsometricImmersion M g F := ⟨hF,fun p v w => by rw [hmetric]; rfl⟩
  obtain ⟨ρ,hρ,hextend⟩ := A₀.geometric_normal_extension B hFiso n₀ houter
    curves hglobal i e he hi hD hDr hDs hDe hDw E₀ hE₀ hE₀f
    (fun j p => (b j p,c j p)) (fun j => (hb j).continuous.prodMk (hc j).continuous)
    hvector hworldBoundary hpositive (fun j p hp hpf =>
      hold j _ (hcurveChart j p hp (frontier_subset_closure hpf)) (haFrontier p hpf))
  intro ε hε ζ hζ
  let ε₀ := min ε (ρ/4)
  let ζ₀ := min ζ (ρ/4)
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  have hζ₀ : 0 < ζ₀ := lt_min hζ (by positivity)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hdata,hreg,havoid,hcross,hlocal,hrest⟩ :=
    data.independent_geometric_circular_primitive_normal A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      ha hT hU hTU hn hI hN hHess ha0 hboundary hCurves hCurvesT hP hlocal
      hE hET haE slopeBound hSlope hb hc hbc S hSc hTS hST K hK hKS hKA hone haoff
      ℓ hℓx hℓy h htarget hC hCS hCurveC hactiveC hEC hold left right x hxinj hxE
      hV hxV honly hfirst hslopes ε₀ hε₀ ζ₀ hζ₀
  obtain ⟨U₀,hU₀,hCU₀,ν,hν,hunit,hnormal,hcanonical,hνavoid,hνcross⟩ := hlocal
  obtain ⟨G,hG,hGF,V₀,hV₀,hWV,hVouter,hVsupport⟩ := hrest
  have hsmall : ε₀+z^8 < ρ := by
    have hz8 : z^8 ≤ z := calc
      z^8 = z*z^7 := by ring
      _ ≤ z*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hz.le hz1) hz.le
      _ = z := mul_one _
    have heps : ε₀ ≤ ρ/4 := min_le_right _ _
    have hzz : z < ρ/4 := hzζ.trans_le (min_le_right _ _)
    linarith
  have hGF₂ : A₀.WeightedBound 1 2 ε₀ (G-F) := fun j => (hGF j).mono_order (by decide)
  obtain ⟨N,hNav,hNmatch⟩ := hextend G V₀ W hG hV₀ h hW ε₀ (z^8) hε₀.le
    (pow_nonneg hz.le _) hsmall hGF₂ hWV
    (fun p hp => hVsupport p (by rwa [hsupport])) z U₀ hU₀ ν hν hunit hnormal
    (fun p hp => hCU₀ ⟨e (chart (i : M) p),hDC p hp,rfl⟩)
    (fun p hp => hcanonical _ (hCU₀ ⟨e (chart (i : M) p),hDC p (frontier_subset_closure hp),rfl⟩)
      (hVfrontier p hp))
    (fun j p hp hpD => ⟨(havoid j _ (hcurveChart j p hp (subset_closure hpD))).1,
      hνavoid j _ (hcurveChart j p hp (subset_closure hpD))⟩)
  refine ⟨z,hz,hzζ.trans_le (min_le_left _ _),hz1,W,hW,hdata,N,hNav,
    (fun p hp hpD => (hNmatch p hp).2 hpD),?_,G,hG,?_,V₀,hV₀,hWV,hVouter,hVsupport⟩
  · intro j
    have hxT : x j ∈ (surfacePhaseChart (i : M) e).target := by
      constructor
      · change baseEquiv.symm (x j) ∈ e.target
        exact (hCS (hEC _ (hxE j))).2
      · change e.symm (baseEquiv.symm (x j)) ∈ (chart (i : M)).target
        have ha := hactiveC _ (hEC _ (hxE j))
        by_contra hh
        simp only [SmoothingAtlas.chartWeight,indicator_of_notMem hh] at ha
        exact ha rfl
    have heq : spaceCoordinates (N.vector ((surfacePhaseChart (i : M) e).symm (x j))) = ν (x j) := by
      rw [(hNmatch _ (hσD j).1).1 (hσD j).2,A₀.phaseNormalLift_coordinates]
      exact congrArg ν ((surfacePhaseChart (i : M) e).right_inv hxT)
    dsimp only
    rw [heq]
    exact hνcross j
  · exact fun j => (hGF j).mono_const (min_le_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal_oai.{u_1, u_2, u_3} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal_oai.{u_1, u_2, u_3}
