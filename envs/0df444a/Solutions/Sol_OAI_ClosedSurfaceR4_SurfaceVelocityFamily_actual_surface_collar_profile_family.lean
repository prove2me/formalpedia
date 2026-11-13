-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:38:34.516927+00:00
-- url     : https://prove2.me/submissions/26c00d48-e0a6-4cc5-b818-44ec4f0e82d6

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_constructed_surface_collar_family

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalFrame
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.NormalFrame

lemma unitPerp_unit {X Y B : Vec} (hD : gramDet X Y ≠ 0) (hB : B ≠ 0)
    (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0) : unitPerp X Y B ⬝ᵥ unitPerp X Y B = 1 := by
  have hp := perp_sq_pos hD hB hX hY
  have hs : Real.sqrt (perpProduct X Y B ⬝ᵥ perpProduct X Y B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he := Real.sq_sqrt hp.le
  simp only [unitPerp, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  nlinarith [he]

end ClosedSurfaceR4.NormalFrame

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



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
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
open ClosedSurfaceR4.WeightedEstimates

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma convexQuadraticPhase_hasFDerivAt (ell : Base) (L : ℝ) (p : Base) :
    HasFDerivAt (convexQuadraticPhase ell L) (phaseLinear (ell + L • p)) p := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hh := (phaseLinear ell).hasFDerivAt (x := p) |>.add
    (((h1.pow 2).add (h2.pow 2)).const_mul (L / 2))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, phaseLinear_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    two_smul, smul_eq_mul]
  ring

lemma convexQuadraticPhase_coordDeriv (ell : Base) (L : ℝ) (p v : Base) :
    coordDeriv v (convexQuadraticPhase ell L) p = phaseLinear (ell + L • p) v := by
  exact congrArg (fun f : Base →L[ℝ] ℝ => f v)
    (convexQuadraticPhase_hasFDerivAt ell L p).fderiv

lemma convexQuadraticPhase_phaseDerivative (ell : Base) (L : ℝ) (p : Base) :
    phaseDerivative (convexQuadraticPhase ell L) p = ell + L • p := by
  unfold phaseDerivative
  rw [(convexQuadraticPhase_hasFDerivAt ell L p).fderiv]
  ext <;> simp [phaseLinear_apply, dx, dy]

lemma convexQuadraticPhase_second (ell : Base) (L : ℝ) (p v w : Base) :
    coordDeriv v (coordDeriv w (convexQuadraticPhase ell L)) p =
      L * (v.1*w.1 + v.2*w.2) := by
  have he : coordDeriv w (convexQuadraticPhase ell L) =
      fun p => phaseLinear ell w + L * phaseLinear w p := by
    funext q
    rw [convexQuadraticPhase_coordDeriv]
    simp only [phaseLinear_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [he]
  have hh := (hasFDerivAt_const (phaseLinear ell w) p).add
    ((phaseLinear w).hasFDerivAt (x := p) |>.const_mul L)
  change (fderiv ℝ ((fun _ : Base => phaseLinear ell w) +
    fun p => L * phaseLinear w p) p) v = _
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, zero_add, phaseLinear_apply]
  ring

lemma convexQuadraticPhase_hessian (h : Base → PhaseMean.Tensor) (ell : Base) (L : ℝ)
    (p v w : Base) :
    coordinateMetricHessian h (convexQuadraticPhase ell L) p v w =
      L * (v.1*w.1 + v.2*w.2) - phaseLinear (ell + L • p)
        (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w) := by
  rw [coordinateMetricHessian, convexQuadraticPhase_second,
    convexQuadraticPhase_phaseDerivative]

lemma coordinateMetricHessian_fst_dy (h : Base → PhaseMean.Tensor) (p : Base) :
    coordinateMetricHessian h (Prod.fst : Base → ℝ) p dy dy =
      -(metricConnectionAt (h p,fderiv ℝ h p) 2).1 := by
  have he : convexQuadraticPhase dx 0 = (Prod.fst : Base → ℝ) := by
    funext q
    simp [convexQuadraticPhase, phaseLinear_apply, dx]
  have hh := convexQuadraticPhase_hessian h dx 0 p dy dy
  rw [he] at hh
  simpa [connectionContract, phaseLinear_apply, dx, dy] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealMetricDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma normalize_nonzero {v : Vec} (hv : v ≠ 0) : normalize v ≠ 0 := by
  intro hz
  have hu := normalize_unit hv
  rw [hz] at hu
  norm_num at hu

lemma blend_nonzero_of_not_opposite {u v : Vec} {t : ℝ}
    (hv : v ≠ 0) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : t = 0 → u ≠ 0)
    (hanti : t < 1 → ∀ r : ℝ, 0 < r → u ≠ -r • v) : blend u v t ≠ 0 := by
  by_cases ht0 : t = 0
  · simpa [blend, ht0] using hu ht0
  by_cases ht1 : t = 1
  · simpa [blend, ht1] using hv
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hden : 0 < 1 - t := sub_pos.mpr htlt
  intro hz
  apply hanti htlt (t / (1 - t)) (div_pos htpos hden)
  ext i
  have hi : (1 - t) * u i + t * v i = 0 := congrFun hz i
  change u i = -(t / (1 - t)) * v i
  field_simp [hden.ne']
  linear_combination hi

lemma first_perp {u v w : Vec} (hu : w ⬝ᵥ u = 0) (hv : w ⬝ᵥ v = 0) (t : ℝ) :
    w ⬝ᵥ first u v t = 0 := by
  apply dot_normalize_zero
  simp [blend, dotProduct_add, dotProduct_smul, hu, hv]

lemma normalize_of_unit {v : Vec} (hv : v ⬝ᵥ v = 1) : normalize v = v := by
  simp [normalize, hv]

theorem frame_orthonormal_of_nonzero {Y C u v : Vec} {t : ℝ}
    (hD : gramDet Y C ≠ 0) (hn : blend u v t ≠ 0)
    (hYu : Y ⬝ᵥ u = 0) (hYv : Y ⬝ᵥ v = 0)
    (hCu : C ⬝ᵥ u = 0) (hCv : C ⬝ᵥ v = 0) :
    first u v t ⬝ᵥ first u v t = 1 ∧
      second Y C u v t ⬝ᵥ second Y C u v t = 1 ∧
      first u v t ⬝ᵥ second Y C u v t = 0 ∧
      Y ⬝ᵥ first u v t = 0 ∧ C ⬝ᵥ first u v t = 0 ∧
      Y ⬝ᵥ second Y C u v t = 0 ∧ C ⬝ᵥ second Y C u v t = 0 := by
  have hfirst := normalize_unit hn
  have hnonzero := normalize_nonzero hn
  have hY := first_perp hYu hYv t
  have hC := first_perp hCu hCv t
  have hsecond := unitPerp_unit hD hnonzero hY hC
  have horth := unitPerp_orthogonal Y C (first u v t)
  exact ⟨hfirst, hsecond, horth.2.2, hY, hC, horth.1, horth.2.1⟩

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate nondegeneracy of the moving velocity plane and its normal projection. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma velocity_gram_formula {X Y B C : Vec} {a b : ℝ}
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B) :
    gramDet Y C = a ^ 2 * gramDet X Y + (Y ⬝ᵥ Y) * (B ⬝ᵥ B) := by
  rw [hC]
  simp only [gramDet, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm B X, dotProduct_comm B Y, dotProduct_comm Y X,
    hXB, hYB, mul_zero, add_zero, zero_add]
  ring

lemma velocity_gram_pos {X Y B C : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B) : 0 < gramDet Y C := by
  rw [velocity_gram_formula hXB hYB hC]
  exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero ha) (gramDet_pos hD))
    (mul_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg (Y i)))
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i))))

lemma projected_normal_kernel {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hp : realNormalPart Y C n = 0) : n = 0 := by
  let c := ((C ⬝ᵥ C) * (Y ⬝ᵥ n) - (Y ⬝ᵥ C) * (C ⬝ᵥ n)) / gramDet Y C
  let d := ((Y ⬝ᵥ Y) * (C ⬝ᵥ n) - (Y ⬝ᵥ C) * (Y ⬝ᵥ n)) / gramDet Y C
  have hspan : n = c • Y + d • C := by
    apply sub_eq_zero.mp
    calc
      n - (c • Y + d • C) = n - c • Y - d • C := by abel
      _ = 0 := hp
  have hx : c * (X ⬝ᵥ Y) + d * (a * (X ⬝ᵥ X) + b * (X ⬝ᵥ Y)) = 0 := by
    have he := congrArg (fun w => X ⬝ᵥ w) hspan
    rw [hXn, hC] at he
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hXB, add_zero] using he.symm
  have hy : c * (Y ⬝ᵥ Y) + d * (a * (X ⬝ᵥ Y) + b * (Y ⬝ᵥ Y)) = 0 := by
    have he := congrArg (fun w => Y ⬝ᵥ w) hspan
    rw [hYn, hC] at he
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hYB, add_zero,
      dotProduct_comm Y X] using he.symm
  have hd : d * a * gramDet X Y = 0 := by
    unfold gramDet
    linear_combination (Y ⬝ᵥ Y) * hx - (X ⬝ᵥ Y) * hy
  have hd0 : d = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hD)).resolve_right ha
  have hYY : Y ⬝ᵥ Y ≠ 0 := by
    intro hz
    have hY : Y = 0 := dotProduct_self_eq_zero.mp hz
    apply hD
    simp [gramDet, hY]
  have hc0 : c = 0 := by
    rw [hd0, zero_mul, add_zero] at hy
    exact (mul_eq_zero.mp hy).resolve_right hYY
  simpa only [hc0, hd0, zero_smul, add_zero] using hspan

lemma projected_normal_ne_zero {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0) (hn : n ≠ 0) :
    realNormalPart Y C n ≠ 0 :=
  fun hp => hn (projected_normal_kernel hD ha hXB hYB hC hXn hYn hp)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalNonvanishing
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old second derivative has a nonzero normal component after changing velocity. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma gram_ne_zero_of_projection {X Y : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPX : P X ≠ 0) (hY : Y ≠ 0) :
    gramDet X Y ≠ 0 := by
  have hYY : Y ⬝ᵥ Y ≠ 0 := (dotProduct_self_eq_zero).not.mpr hY
  intro hD
  let W := (Y ⬝ᵥ Y) • X - (X ⬝ᵥ Y) • Y
  have hW : W ⬝ᵥ W = (Y ⬝ᵥ Y) * gramDet X Y := by
    simp only [W, gramDet, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hW0 : W = 0 := dotProduct_self_eq_zero.mp (by rw [hW, hD, mul_zero])
  have hpW : (Y ⬝ᵥ Y) • P X = 0 := by
    have he := congrArg P hW0
    simpa only [W, hP.map_sub, hP.map_smul, hPY, smul_zero, sub_zero, hP.map_zero] using he
  exact hPX ((smul_eq_zero.mp hpW).resolve_left hYY)

lemma normalPart_ne_zero_of_projection {X Y C : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPC : P C = 0) (hPX : P X ≠ 0)
    (hD : gramDet Y C ≠ 0) : realNormalPart X Y C ≠ 0 := by
  intro hz
  let c := ((Y ⬝ᵥ Y) * (X ⬝ᵥ C) - (X ⬝ᵥ Y) * (Y ⬝ᵥ C)) / gramDet X Y
  let d := ((X ⬝ᵥ X) * (Y ⬝ᵥ C) - (X ⬝ᵥ Y) * (X ⬝ᵥ C)) / gramDet X Y
  have hspan : C = c • X + d • Y := by
    apply sub_eq_zero.mp
    calc
      C - (c • X + d • Y) = C - c • X - d • Y := by abel
      _ = 0 := hz
  have hc : c = 0 := by
    have he := congrArg P hspan
    have he' : c • P X = 0 := by
      simpa only [hPC, hP.map_add, hP.map_smul, hPY, smul_zero, add_zero] using he.symm
    exact (smul_eq_zero.mp he').resolve_right hPX
  have hC : C = d • Y := by simpa only [hc, zero_smul, zero_add] using hspan
  apply hD
  rw [hC]
  simp only [gramDet, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma leadingTangent_projection {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) :
    realNormalPart Y C (leadingTangent X Y C V) = V := by
  have hP := realNormalPart_linear Y C
  have hpX := realNormalPart_perp Y C X hD
  change realNormalPart Y C (X - realNormalPart Y C X + V) = V
  rw [hP.map_add, hP.map_sub,
    realNormalPart_of_perp Y C (realNormalPart Y C X) hpX.1 hpX.2,
    realNormalPart_of_perp Y C V hYV hCV, sub_self, zero_add]

/-- Neither the leading tangent pair nor the normal component of `C` degenerates. -/
theorem leading_normal_nondegenerate {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) (hV : V ≠ 0) :
    gramDet (leadingTangent X Y C V) Y ≠ 0 ∧
      realNormalPart (leadingTangent X Y C V) Y C ≠ 0 := by
  have hP := realNormalPart_linear Y C
  have hPY := realNormalPart_self_left Y C hD
  have hPC := realNormalPart_self_right Y C hD
  have hPX : realNormalPart Y C (leadingTangent X Y C V) ≠ 0 := by
    rwa [leadingTangent_projection hD hYV hCV]
  have hY : Y ≠ 0 := by
    intro hz
    apply hD
    simp [gramDet, hz]
  exact ⟨gram_ne_zero_of_projection hP hPY hPX hY,
    normalPart_ne_zero_of_projection hP hPY hPC hPX hD⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and compact positive lower bounds for the limiting normal component. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y C V : E → Vec} {U : Set E}

lemma leadingTangent_smoothOn (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hV : ContDiffOn ℝ ∞ V U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => leadingTangent (X x) (Y x) (C x) (V x)) U := by
  intro x hx
  have hm := hU.mem_nhds hx
  exact (((hX.contDiffAt hm).sub (contDiffAt_realNormalPart
    (hY.contDiffAt hm) (hC.contDiffAt hm) (hX.contDiffAt hm) (hD x hx))).add
      (hV.contDiffAt hm)).contDiffWithinAt

lemma leadingNormal_smoothOn (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hV : ContDiffOn ℝ ∞ V U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hYV : ∀ x ∈ U, Y x ⬝ᵥ V x = 0) (hCV : ∀ x ∈ U, C x ⬝ᵥ V x = 0)
    (hV0 : ∀ x ∈ U, V x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => leadingNormal (X x) (Y x) (C x) (V x)) U := by
  have hT := leadingTangent_smoothOn hU hX hY hC hV hD
  intro x hx
  have hm := hU.mem_nhds hx
  exact (contDiffAt_realNormalPart (hT.contDiffAt hm) (hY.contDiffAt hm)
    (hC.contDiffAt hm) (leading_normal_nondegenerate (hD x hx)
      (hYV x hx) (hCV x hx) (hV0 x hx)).1).contDiffWithinAt

lemma normalSize_positive {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) (hV : V ≠ 0) :
    0 < normalSize X Y C V :=
  Real.sqrt_pos.mpr (dot_self_pos (leading_normal_nondegenerate hD hYV hCV hV).2)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular derivative contributes only to the complementary normal component. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma direction_unit {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) : direction e₁ e₂ α ⬝ᵥ direction e₁ e₂ α = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [direction, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq α]

lemma angularDirection_unit {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) :
    angularDirection e₁ e₂ α ⬝ᵥ angularDirection e₁ e₂ α = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [angularDirection, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq α]

lemma direction_angular_perp {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) :
    direction e₁ e₂ α ⬝ᵥ angularDirection e₁ e₂ α = 0 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [direction, angularDirection, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  ring

lemma angularDirection_perp {e₁ e₂ w : Vec} (h₁ : w ⬝ᵥ e₁ = 0) (h₂ : w ⬝ᵥ e₂ = 0) (α : ℝ) :
    w ⬝ᵥ angularDirection e₁ e₂ α = 0 := by
  simp [angularDirection, dotProduct_add, dotProduct_smul, h₁, h₂]

lemma dot_normalPart_eq {X Y w m : Vec} (hX : m ⬝ᵥ X = 0) (hY : m ⬝ᵥ Y = 0) :
    m ⬝ᵥ realNormalPart X Y w = m ⬝ᵥ w := by
  simp [realNormalPart, dotProduct_sub, dotProduct_smul, hX, hY]

lemma dot_leadingTangent_zero {X Y C V m : Vec}
    (hY : m ⬝ᵥ Y = 0) (hC : m ⬝ᵥ C = 0) (hV : m ⬝ᵥ V = 0) :
    m ⬝ᵥ leadingTangent X Y C V = 0 := by
  simp only [leadingTangent, dotProduct_add, dotProduct_sub, dot_normalPart_eq hY hC,
    sub_self, hV, add_zero]

lemma angularDirection_normal_perp {X Y C e₁ e₂ : Vec} (R α : ℝ)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    angularDirection e₁ e₂ α ⬝ᵥ normalize (leadingNormal X Y C (R • direction e₁ e₂ α)) = 0 := by
  have hY : angularDirection e₁ e₂ α ⬝ᵥ Y = 0 :=
    (dotProduct_comm _ _).trans (angularDirection_perp hY₁ hY₂ α)
  have hC : angularDirection e₁ e₂ α ⬝ᵥ C = 0 :=
    (dotProduct_comm _ _).trans (angularDirection_perp hC₁ hC₂ α)
  have hV : angularDirection e₁ e₂ α ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    rw [dotProduct_smul, dotProduct_comm (angularDirection _ _ _) (direction _ _ _),
      direction_angular_perp h₁ h₂ horth, smul_zero]
  have hT := dot_leadingTangent_zero (X := X) hY hC hV
  apply dot_normalize_zero
  change angularDirection e₁ e₂ α ⬝ᵥ realNormalPart
    (leadingTangent X Y C (R • direction e₁ e₂ α)) Y C = 0
  rw [dot_normalPart_eq hT hY, hC]

/-- The first normal coefficient does not contain the angular derivative. -/
lemma first_normal_derivative_independent {W m n : Vec} (hmn : m ⬝ᵥ n = 0) (R d : ℝ) :
    (W + (R * d) • m) ⬝ᵥ n = W ⬝ᵥ n := by
  simp [add_dotProduct, smul_dotProduct, hmn]

/-- The complementary normal coefficient contains that derivative with coefficient `R`. -/
lemma second_normal_derivative {W m : Vec} (hm : m ⬝ᵥ m = 1) (R d : ℝ) :
    (W + (R * d) • m) ⬝ᵥ m = R * d + W ⬝ᵥ m := by
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hm, mul_one]
  ring

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneBasis
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates in the actual two-dimensional velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma velocity_frame_independent {Y C e₁ e₂ : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0) :
    LinearIndependent ℝ ![Y, C, e₁, e₂] := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have he : a 0 • Y + (a 1 • C + (a 2 • e₁ + a 3 • e₂)) = 0 := by
    simpa [Fin.sum_univ_succ] using ha
  have hy := congrArg (fun w => Y ⬝ᵥ w) he
  have hc := congrArg (fun w => C ⬝ᵥ w) he
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hY1, hY2, hC1, hC2,
    mul_zero, add_zero, dotProduct_zero, dotProduct_comm C Y] at hy hc
  have haD : a 0 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (C ⬝ᵥ C) * hy - (Y ⬝ᵥ C) * hc
  have hbD : a 1 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (Y ⬝ᵥ Y) * hc - (Y ⬝ᵥ C) * hy
  have ha0 := (mul_eq_zero.mp haD).resolve_right hD
  have ha1 := (mul_eq_zero.mp hbD).resolve_right hD
  have hz : a 2 • e₁ + a 3 • e₂ = 0 := by simpa [ha0, ha1] using he
  have h2 := congrArg (fun w => e₁ ⬝ᵥ w) hz
  have h3 := congrArg (fun w => e₂ ⬝ᵥ w) hz
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, mul_one, mul_zero, add_zero, zero_add, dotProduct_zero] at h2 h3
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact h2
  · exact h3

lemma orthogonal_frame_eq_zero {Y C e₁ e₂ w : Vec}
    (hlin : LinearIndependent ℝ ![Y, C, e₁, e₂])
    (hY : Y ⬝ᵥ w = 0) (hC : C ⬝ᵥ w = 0)
    (h1 : e₁ ⬝ᵥ w = 0) (h2 : e₂ ⬝ᵥ w = 0) : w = 0 := by
  have hs := hlin.span_eq_top_of_card_eq_finrank (by simp [Vec])
  have hw : w ∈ Submodule.span ℝ (Set.range ![Y, C, e₁, e₂]) := by
    rw [hs]
    trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  apply dotProduct_self_eq_zero.mp
  calc
    w ⬝ᵥ w = (∑ i, a i • (![Y, C, e₁, e₂] i)) ⬝ᵥ w := by rw [ha]
    _ = 0 := by simp [Fin.sum_univ_succ, add_dotProduct, smul_dotProduct, hY, hC, h1, h2]

theorem plane_coordinates_reconstruct {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) = v := by
  apply sub_eq_zero.mp
  apply orthogonal_frame_eq_zero (velocity_frame_independent hD h₁ h₂ h12 hY1 hY2 hC1 hC2)
  all_goals simp [planeLift_apply, planeCoordinates, dotProduct_sub, dotProduct_add,
    dotProduct_smul, hY1, hY2, hC1, hC2, hYv, hCv, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, dotProduct_comm e₁ v, dotProduct_comm e₂ v]

lemma plane_coordinates_length {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    (v ⬝ᵥ e₁) ^ 2 + (v ⬝ᵥ e₂) ^ 2 = v ⬝ᵥ v := by
  have hr := plane_coordinates_reconstruct hD h₁ h₂ h12 hY1 hY2 hC1 hC2 hYv hCv
  have hd := congrArg (fun w => w ⬝ᵥ w) hr
  simpa [planeLift_apply, planeCoordinates, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, h₁, h₂, h12, dotProduct_comm e₂ e₁, pow_two] using hd

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma velocityRadius_smoothOn {v : E → Vec} {a : E → ℝ} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, v x ≠ 0 ∨ a x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => velocityRadius (v x) (a x)) U := by
  apply ((dot_smoothOn hv hv).add (ha.pow 2)).sqrt
  intro x hx
  have hp := velocityRadius_pos (hn x hx)
  exact (Real.sqrt_pos.mp hp).ne'

end ClosedSurfaceR4.VelocityFrame

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

lemma profileComplement_unit {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    profileComplement J ⬝ᵥ profileComplement J = 1 :=
  unitPerp_unit hJ.1 (normalize_nonzero hJ.2)
    (profilePreferred_perp hJ).1 (profilePreferred_perp hJ).2

lemma profileComplement_perp (J : BoundaryProfile) :
    J 0 ⬝ᵥ profileComplement J = 0 ∧ J 1 ⬝ᵥ profileComplement J = 0 ∧
      profilePreferred J ⬝ᵥ profileComplement J = 0 := unitPerp_orthogonal _ _ _

/-- Every unit normal orthogonal to the preferred normal reads the same
absolute complementary coefficient, regardless of the orientation choice. -/
lemma profileComplement_abs_dot {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles)
    {u : Vec} (hu : u ⬝ᵥ u = 1) (hXu : J 0 ⬝ᵥ u = 0) (hYu : J 1 ⬝ᵥ u = 0)
    (hnu : profilePreferred J ⬝ᵥ u = 0) (W : Vec) :
    |W ⬝ᵥ profileComplement J| = |W ⬝ᵥ u| := by
  have hp := profilePreferred_perp hJ
  have hm := profileComplement_perp J
  have hr := plane_coordinates_reconstruct hJ.1 (profilePreferred_unit hJ)
    (profileComplement_unit hJ) hm.2.2 hp.1 hm.1 hp.2 hm.2.1 hXu hYu
  have he : (u ⬝ᵥ profileComplement J) • profileComplement J = u := by
    simpa only [planeLift_apply,_root_.OAI.ClosedSurfaceR4.VelocityFrame.planeCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
      dotProduct_comm u (profilePreferred J),hnu,zero_smul,zero_add] using hr
  have hl := plane_coordinates_length hJ.1 (profilePreferred_unit hJ)
    (profileComplement_unit hJ) hm.2.2 hp.1 hm.1 hp.2 hm.2.1 hXu hYu
  have hs : (u ⬝ᵥ profileComplement J)^2 = 1 := by
    simpa only [dotProduct_comm u (profilePreferred J),hnu,zero_pow (by decide : 2 ≠ 0),
      zero_add,hu] using hl
  have ha : |u ⬝ᵥ profileComplement J| = 1 := by
    nlinarith [sq_abs (u ⬝ᵥ profileComplement J),abs_nonneg (u ⬝ᵥ profileComplement J)]
  calc
    |W ⬝ᵥ profileComplement J| = |u ⬝ᵥ profileComplement J| * |W ⬝ᵥ profileComplement J| := by rw [ha,one_mul]
    _ = |W ⬝ᵥ ((u ⬝ᵥ profileComplement J) • profileComplement J)| := by
      rw [dotProduct_smul,smul_eq_mul,abs_mul]
    _ = |W ⬝ᵥ u| := by rw [he]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar limits controlling the boundary argument for a circular
velocity, in the canonical normal frame read from the five profiles. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma circularBoundaryProfile_regular {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    circularBoundaryProfile X Y C W e₁ e₂ R α β ∈ regularBoundaryProfiles := by
  have hYV : Y ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    simp [direction,dotProduct_smul,dotProduct_add,hY₁,hY₂]
  have hCV : C ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    simp [direction,dotProduct_smul,dotProduct_add,hC₁,hC₂]
  have hV : R • direction e₁ e₂ α ≠ 0 := by
    apply smul_ne_zero hR
    intro hh
    have hu := direction_unit h₁ h₂ horth α
    rw [hh] at hu
    norm_num at hu
  exact leading_normal_nondegenerate hD hYV hCV hV

/-- The mixed coefficient agrees in absolute value with the geometric
angular component; the scaled longitudinal coefficient is `R * β`. -/
theorem circularBoundaryProfile_coefficients {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    |profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 2| =
      |W ⬝ᵥ angularDirection e₁ e₂ α| ∧
    |profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 3| = |R*β| := by
  let J := circularBoundaryProfile X Y C W e₁ e₂ R α β
  have hJ : J ∈ regularBoundaryProfiles :=
    circularBoundaryProfile_regular hD hR h₁ h₂ horth hY₁ hY₂ hC₁ hC₂
  let u := angularDirection e₁ e₂ α
  have hu : u ⬝ᵥ u = 1 := angularDirection_unit h₁ h₂ horth α
  have hy : Y ⬝ᵥ u = 0 := angularDirection_perp hY₁ hY₂ α
  have hc : C ⬝ᵥ u = 0 := angularDirection_perp hC₁ hC₂ α
  have hv : u ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    rw [dotProduct_smul,dotProduct_comm u (direction e₁ e₂ α),
      direction_angular_perp h₁ h₂ horth,smul_zero]
  have hx : J 0 ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact dot_leadingTangent_zero ((dotProduct_comm _ _).trans hy)
      ((dotProduct_comm _ _).trans hc) hv
  have hn : profilePreferred J ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact angularDirection_normal_perp R α h₁ h₂ horth hY₁ hY₂ hC₁ hC₂
  have hW := profileComplement_abs_dot hJ hu hx hy hn W
  have hA := profileComplement_abs_dot hJ hu hx hy hn ((R*β) • u)
  refine ⟨hW,?_⟩
  change |((R*β) • u) ⬝ᵥ profileComplement J| = |R*β|
  rw [hA,smul_dotProduct,hu,smul_eq_mul,mul_one]

lemma circularBoundaryProfile_turn_iff {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 3 = 0 ↔ β = 0 := by
  have h := (circularBoundaryProfile_coefficients (X := X) (W := W) (α := α) (β := β) hD hR h₁ h₂ horth hY₁ hY₂ hC₁ hC₂).2
  rw [← abs_eq_zero, h,abs_eq_zero,mul_eq_zero]
  simp [hR]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalEstimates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal-component bounds independent of the chosen angular derivative. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma unit_coordinate_abs_le {m : Vec} (hm : m ⬝ᵥ m = 1) (i : Fin 4) : |m i| ≤ 1 := by
  have hs : m i ^ 2 ≤ m ⬝ᵥ m := by
    simpa only [dotProduct, pow_two] using
      (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
        mul_self_nonneg (m j)) (Finset.mem_univ i))
  rw [hm] at hs
  exact (sq_le_one_iff_abs_le_one _).mp hs

lemma abs_dot_unit_le (W : Vec) {m : Vec} (hm : m ⬝ᵥ m = 1) :
    |W ⬝ᵥ m| ≤ 4 * ‖W‖ := by
  calc
    |W ⬝ᵥ m| ≤ ∑ i : Fin 4, |W i * m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, |W i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (unit_coordinate_abs_le hm i)
    _ ≤ 4 * ‖W‖ := by
      simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
        Pi.sum_norm_apply_le_norm W

theorem second_normal_error_bound {W m : Vec} (hm : m ⬝ᵥ m = 1) (R d : ℝ) :
    |(W + (R * d) • m) ⬝ᵥ m - R * d| ≤ 4 * ‖W‖ := by
  rw [second_normal_derivative hm]
  simpa only [add_sub_cancel_left] using abs_dot_unit_le W hm

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocitySpatialDerivative
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spatial differentiation of the actual circular velocity, separating
all dependence on the angular derivative from the bounded remainder. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem circular_velocity_derivative {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x) (v : E) :
    fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v =
      spatialError Q R e₁ e₂ α x v +
        (R x * fderiv ℝ α x v) • angularDirection (e₁ x) (e₂ x) (α x) := by
  have hd := hQ.hasFDerivAt.add (hR.hasFDerivAt.smul
    ((hα.hasFDerivAt.cos.smul h₁.hasFDerivAt).add
      (hα.hasFDerivAt.sin.smul h₂.hasFDerivAt)))
  change HasFDerivAt (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) _ x at hd
  rw [hd.fderiv]
  ext i
  simp only [spatialError, direction, angularDirection, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul,
    neg_mul]
  ring

lemma norm_direction_le (e₁ e₂ : Vec) (α : ℝ) :
    ‖direction e₁ e₂ α‖ ≤ ‖e₁‖ + ‖e₂‖ := by
  calc
    ‖direction e₁ e₂ α‖ ≤ ‖Real.cos α • e₁‖ + ‖Real.sin α • e₂‖ := norm_add_le _ _
    _ ≤ ‖e₁‖ + ‖e₂‖ := add_le_add
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one α))
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α))

/-- The bound does not contain a derivative of `α`. -/
theorem spatialError_bound (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (α : E → ℝ) (x v : E) :
    ‖spatialError Q R e₁ e₂ α x v‖ ≤
      ‖fderiv ℝ Q x v‖ + |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
        |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖) := by
  unfold spatialError
  calc
    ‖fderiv ℝ Q x v + (fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x) +
        R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)‖
      ≤ ‖fderiv ℝ Q x v‖ + ‖(fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x)‖ +
        ‖R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖fderiv ℝ Q x v‖ + |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
        |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (norm_direction_le _ _ _) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left (norm_direction_le _ _ _) (abs_nonneg _))

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FrozenCircularData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal data as smooth functions of position and angular value.
The first mixed normal coefficient contains no derivative of the angle. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frozenError_smoothOn {Q e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hQ : ContDiffOn ℝ ∞ Q U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U) (d : E) :
    ContDiffOn ℝ ∞ (frozenError Q R e₁ e₂ d) (U ×ˢ univ) := by
  have hDQ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ Q z.1 d) (U ×ˢ univ) :=
    ((hQ.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hDR : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ R z.1 d) (U ×ˢ univ) :=
    ((hR.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hD₁ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ e₁ z.1 d) (U ×ˢ univ) :=
    ((h₁.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hD₂ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ e₂ z.1 d) (U ×ˢ univ) :=
    ((h₂.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  exact (hDQ.add (hDR.smul
    ((contDiffOn_snd.cos.smul (h₁.comp contDiffOn_fst (fun z hz => hz.1))).add
      (contDiffOn_snd.sin.smul (h₂.comp contDiffOn_fst (fun z hz => hz.1)))))).add
    ((hR.comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((contDiffOn_snd.cos.smul hD₁).add (contDiffOn_snd.sin.smul hD₂)))

theorem frozen_normals_smoothOn {X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) :
    ContDiffOn ℝ ∞ (frozenNormal X Y C R e₁ e₂) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (frozenSize X Y C R e₁ e₂) (U ×ˢ univ) := by
  let V : E × ℝ → Vec := fun z => R z.1 • direction (e₁ z.1) (e₂ z.1) z.2
  have hV : ContDiffOn ℝ ∞ V (U ×ˢ univ) :=
    (hR.comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((contDiffOn_snd.cos.smul (h₁.comp contDiffOn_fst (fun z hz => hz.1))).add
        (contDiffOn_snd.sin.smul (h₂.comp contDiffOn_fst (fun z hz => hz.1))))
  have hVY (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : Y z.1 ⬝ᵥ V z = 0 := by
    have hf := hframe z.1 hz.1
    simp [V, direction, dotProduct_add, dotProduct_smul, hf.2.2.2.1, hf.2.2.2.2.2.1]
  have hVC (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : C z.1 ⬝ᵥ V z = 0 := by
    have hf := hframe z.1 hz.1
    simp [V, direction, dotProduct_add, dotProduct_smul, hf.2.2.2.2.1, hf.2.2.2.2.2.2]
  have hV0 (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : V z ≠ 0 := by
    apply smul_ne_zero (hR0 z.1 hz.1)
    have hf := hframe z.1 hz.1
    intro he
    have hu := direction_unit hf.1 hf.2.1 hf.2.2.1 z.2
    rw [he] at hu
    norm_num at hu
  have hN := leadingNormal_smoothOn (hU.prod isOpen_univ)
    (hX.comp contDiffOn_fst (fun z hz => hz.1))
    (hY.comp contDiffOn_fst (fun z hz => hz.1))
    (hC.comp contDiffOn_fst (fun z hz => hz.1)) hV
    (fun z hz => hD z.1 hz.1) hVY hVC hV0
  have hN0 (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) :
      leadingNormal (X z.1) (Y z.1) (C z.1) (V z) ≠ 0 :=
    (leading_normal_nondegenerate (hD z.1 hz.1) (hVY z hz) (hVC z hz) (hV0 z hz)).2
  constructor
  · intro z hz
    exact (normalize_smoothAt (hN.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hN0 z hz)).contDiffWithinAt
  · exact (dot_smoothOn hN hN).sqrt (fun z hz => (dot_self_pos (hN0 z hz)).ne')

theorem frozen_coefficients_smoothOn {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) (d : E) :
    ContDiffOn ℝ ∞ (frozenFirst Q X Y C R e₁ e₂ d) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (frozenSize X Y C R e₁ e₂) (U ×ˢ univ) := by
  obtain ⟨hN, hS⟩ := frozen_normals_smoothOn hU hX hY hC hR h₁ h₂ hD hframe hR0
  exact ⟨dot_smoothOn (frozenError_smoothOn hU hQ hR h₁ h₂ d) hN, hS⟩

theorem actual_first_eq_frozen {Q X Y C e₁ e₂ : E → Vec} {R α : E → ℝ} {x d : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x d ⬝ᵥ
        frozenNormal X Y C R e₁ e₂ (x, α x) =
      frozenFirst Q X Y C R e₁ e₂ d (x, α x) := by
  rw [circular_velocity_derivative hQ hR h₁ h₂ hα]
  exact first_normal_derivative_independent
    (angularDirection_normal_perp (R x) (α x) hframe.1 hframe.2.1 hframe.2.2.1
      hframe.2.2.2.1 hframe.2.2.2.2.2.1 hframe.2.2.2.2.1 hframe.2.2.2.2.2.2) _ _

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocitySpatialBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact bounds for the actual circular velocity derivative, uniform in
both the angle and its arbitrarily large derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_spatialError_bound_on {Q : E → Vec} {R : E → ℝ} {e₁ e₂ : E → Vec}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : E → ℝ) x, x ∈ K →
      ‖spatialError Q R e₁ e₂ α x v‖ ≤ C := by
  have hDQ : ContinuousOn (fun x => fderiv ℝ Q x v) U :=
    ((hQ.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).continuousOn
  have hDR : ContinuousOn (fun x => fderiv ℝ R x v) U :=
    ((hR.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).continuousOn
  have hD₁ : ContinuousOn (fun x => fderiv ℝ e₁ x v) U :=
    ((h₁.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).continuousOn
  have hD₂ : ContinuousOn (fun x => fderiv ℝ e₂ x v) U :=
    ((h₂.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const).continuousOn
  let L : E → ℝ := fun x => ‖fderiv ℝ Q x v‖ +
    |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
      |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖)
  have hL : ContinuousOn L U :=
    (hDQ.norm.add (hDR.abs.mul (h₁.continuousOn.norm.add h₂.continuousOn.norm))).add
      (hR.continuousOn.abs.mul (hD₁.norm.add hD₂.norm))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hL.mono hKU)
  refine ⟨max 0 C, le_max_left _ _, fun α x hx => ?_⟩
  exact (spatialError_bound Q R e₁ e₂ α x v).trans
    ((le_abs_self (L x)).trans ((hC x hx).trans (le_max_right _ _)))

/-- The other normal coefficient is `R` times the angular derivative plus the same bounded error. -/
theorem circular_second_normal_bound {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x v : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hunit : angularDirection (e₁ x) (e₂ x) (α x) ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) = 1) :
    |fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) - R x * fderiv ℝ α x v| ≤
      4 * ‖spatialError Q R e₁ e₂ α x v‖ := by
  rw [circular_velocity_derivative hQ hR h₁ h₂ hα]
  exact second_normal_error_bound hunit _ _

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityTurnDominance
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large spatial angular derivative gives the required strict lower bound
for the actual complementary normal component of the circular velocity. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem circular_turn_dominates {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x v : E} {r C T : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hunit : angularDirection (e₁ x) (e₂ x) (α x) ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) = 1)
    (hr : 0 < r) (hRx : r ≤ R x) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : ‖spatialError Q R e₁ e₂ α x v‖ ≤ C)
    (hlarge : (T + 4 * C + 1) / r < fderiv ℝ α x v) :
    T + 1 < fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) := by
  have herr := circular_second_normal_bound (v := v) hQ hR h₁ h₂ hα hunit
  have hE := abs_le.mp (herr.trans (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)))
  have hprod : T + 4 * C + 1 < r * fderiv ℝ α x v := by
    have hd := (div_lt_iff₀ hr).mp hlarge
    nlinarith
  have hdpos : 0 < fderiv ℝ α x v := by
    have hpos : 0 < (T + 4 * C + 1) / r := div_pos (by linarith) hr
    exact hpos.trans hlarge
  have hscale := mul_le_mul_of_nonneg_right hRx hdpos.le
  linarith [hE.1]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenBoundaryCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical profile coefficients have the same fixed bounds and turn
mechanism as the explicit circular velocity used to construct the loop. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circularSpatialProfile_first {Q X Y C e₁ e₂ : E → Vec} {R α : E → ℝ}
    {x d : E} (β : ℝ) (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 1 =
      frozenFirst Q X Y C R e₁ e₂ d (x,α x) :=
  actual_first_eq_frozen hQ hR h₁ h₂ hα hframe

/-- Large transverse angular derivative gives a large canonical mixed
coefficient; the threshold uses no derivative of the chosen angular phase. -/
theorem circularSpatialProfile_mixed_dominates {Q X Y C e₁ e₂ : E → Vec}
    {R α : E → ℝ} {x d : E} (β : ℝ) {r B T : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hD : gramDet (Y x) (C x) ≠ 0)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hr : 0 < r) (hRx : r ≤ R x) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hbound : ‖spatialError Q R e₁ e₂ α x d‖ ≤ B)
    (hlarge : (T+4*B+1)/r < fderiv ℝ α x d) :
    T+1 < |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 2| := by
  have hunit := angularDirection_unit hframe.1 hframe.2.1 hframe.2.2.1 (α x)
  have hdom := circular_turn_dominates hQ hR h₁ h₂ hα hunit hr hRx hB hT hbound hlarge
  have he := (circularBoundaryProfile_coefficients (X := X x)
    (W := fderiv ℝ (fun y => Q y+R y • direction (e₁ y) (e₂ y) (α y)) x d)
    (α := α x) (β := β) hD (hr.trans_le hRx).ne'
    hframe.1 hframe.2.1 hframe.2.2.1 hframe.2.2.2.1 hframe.2.2.2.2.2.1
    hframe.2.2.2.2.1 hframe.2.2.2.2.2.2).1
  change T+1 < |profileCoefficients
    (circularBoundaryProfile (X x) (Y x) (C x) _ (e₁ x) (e₂ x) (R x) (α x) β) 2|
  rw [he]
  exact hdom.trans_le (le_abs_self _)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenCoefficientBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric and first-normal bounds precede every choice of large angular
jet: they are uniform over the entire circle of angular values. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma frozenSize_pos {X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {x : E}
    (hD : gramDet (Y x) (C x) ≠ 0) (hR : R x ≠ 0)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (α : ℝ) : 0 < frozenSize X Y C R e₁ e₂ (x,α) := by
  apply normalSize_positive hD
  · simp [direction,dotProduct_smul,dotProduct_add,hframe.2.2.2.1,hframe.2.2.2.2.2.1]
  · simp [direction,dotProduct_smul,dotProduct_add,hframe.2.2.2.2.1,hframe.2.2.2.2.2.2]
  · apply smul_ne_zero hR
    intro he
    have hh := direction_unit hframe.1 hframe.2.1 hframe.2.2.1 α
    rw [he] at hh
    norm_num at hh

theorem compact_frozen_coefficient_bounds {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) (d : E) :
    ∃ sLo sHi B : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ B ∧ ∀ x ∈ K, ∀ α : ℝ,
      sLo ≤ frozenSize X Y C R e₁ e₂ (x,α) ∧
      frozenSize X Y C R e₁ e₂ (x,α) ≤ sHi ∧
      |frozenFirst Q X Y C R e₁ e₂ d (x,α)| ≤ B := by
  obtain ⟨hfirst,hsize⟩ := frozen_coefficients_smoothOn hU hQ hX hY hC hR h₁ h₂ hD hframe hR0 d
  let Z : Set (E × ℝ) := K ×ˢ Icc (-Real.pi) Real.pi
  have hZ : IsCompact Z := hK.prod isCompact_Icc
  have hZU : Z ⊆ U ×ˢ univ := fun z hz => ⟨hKU hz.1,mem_univ _⟩
  have hs : ContinuousOn (frozenSize X Y C R e₁ e₂) Z := hsize.continuousOn.mono hZU
  have hf : ContinuousOn (frozenFirst Q X Y C R e₁ e₂ d) Z := hfirst.continuousOn.mono hZU
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1,1,0,zero_lt_one,zero_lt_one,le_rfl,?_⟩
    simp [hempty]
  have hZne : Z.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,0),hx,by constructor <;> linarith [Real.pi_pos]⟩
  obtain ⟨z,hz,hmin⟩ := hZ.exists_isMinOn hZne hs
  obtain ⟨S,hS⟩ := hZ.exists_bound_of_continuousOn hs
  obtain ⟨B,hB⟩ := hZ.exists_bound_of_continuousOn hf
  refine ⟨frozenSize X Y C R e₁ e₂ z,max 1 S,max 0 B,
    frozenSize_pos (hD z.1 (hKU hz.1)) (hR0 z.1 (hKU hz.1)) (hframe z.1 (hKU hz.1)) z.2,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),le_max_left _ _,?_⟩
  intro x hx α
  let θ := (α : Real.Angle).toReal
  have hθ : θ ∈ Icc (-Real.pi) Real.pi :=
    ⟨(Real.Angle.toReal_mem_Ioc (α : Real.Angle)).1.le,(Real.Angle.toReal_mem_Ioc (α : Real.Angle)).2⟩
  have hcos : Real.cos θ = Real.cos α := (Real.Angle.cos_toReal _).trans (Real.Angle.cos_coe _)
  have hsin : Real.sin θ = Real.sin α := (Real.Angle.sin_toReal _).trans (Real.Angle.sin_coe _)
  have hsizeEq : frozenSize X Y C R e₁ e₂ (x,θ) = frozenSize X Y C R e₁ e₂ (x,α) := by
    simp only [frozenSize,direction,hcos,hsin]
  have hfirstEq : frozenFirst Q X Y C R e₁ e₂ d (x,θ) =
      frozenFirst Q X Y C R e₁ e₂ d (x,α) := by
    simp only [frozenFirst,frozenError,frozenNormal,direction,hcos,hsin]
  have hxθ : (x,θ) ∈ Z := ⟨hx,hθ⟩
  rw [← hsizeEq,← hfirstEq]
  exact ⟨hmin hxθ,(le_abs_self _).trans ((hS _ hxθ).trans (le_max_right _ _)),
    (hB _ hxθ).trans (le_max_right _ _)⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricAcceleration
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The negative tangential acceleration required by the velocity plane is
the actual Christoffel coefficient of the induced metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

lemma inducedCoordinateMetric_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (inducedCoordinateMetric F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dx)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dy)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dy) (contDiff_real_coordDeriv hF dy)

lemma inducedCoordinateMetric_derivative {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v : Base) (i : Fin 3) :
    fderiv ℝ (inducedCoordinateMetric F) p v i =
      coordDeriv v (fun q => inducedCoordinateMetric F q i) p := by
  have he := congrArg (fun L : Base →L[ℝ] ℝ => L v)
    (fderiv_apply ((inducedCoordinateMetric_smooth hF).differentiable (by simp) p) i)
  exact he.symm

lemma induced_connection_yy {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2 =
      (((coordDeriv dy F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p) -
        (coordDeriv dx F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p)) /
          gramDet (coordDeriv dx F p) (coordDeriv dy F p),
       ((coordDeriv dx F p ⬝ᵥ coordDeriv dx F p) *
          (coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p) -
        (coordDeriv dx F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p)) /
          gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have ha : coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2 =
      coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p := by
    simp only [realMetric_partial hF,real_second_coordDeriv_comm hF p dy dx]
    rw [dotProduct_comm (coordDeriv dy F p) (coordDeriv dx (coordDeriv dy F) p)]
    ring
  have hb : coordDeriv dy (realMetric F dy dy) p/2 =
      coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p := by
    rw [realMetric_partial hF,dotProduct_comm (coordDeriv dy (coordDeriv dy F) p)]
    ring
  simp only [metricConnectionAt,Matrix.cons_val_two,inducedCoordinateMetric_derivative hF]
  change ((realMetric F dy dy p *
      (coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2) -
      realMetric F dx dy p * (coordDeriv dy (realMetric F dy dy) p/2)) / _,
    (realMetric F dx dx p * (coordDeriv dy (realMetric F dy dy) p/2) -
      realMetric F dx dy p *
      (coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2)) / _) = _
  rw [ha,hb]
  rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneRays
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary non-antipodality condition survives projection to the velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma no_opposite_ray_of_normalized {B n : Vec} (hB : B ≠ 0)
    (hn : n ⬝ᵥ n = 1) (hanti : normalize B ≠ -n) :
    ∀ r : ℝ, 0 < r → n ≠ -r • B := by
  intro r hr he
  have hp := dot_self_pos hB
  have hs : Real.sqrt (B ⬝ᵥ B) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsq : r ^ 2 * (B ⬝ᵥ B) = 1 := by
    rw [he] at hn
    simpa only [smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_mul_neg,
      ← mul_assoc, ← pow_two, neg_sq] using hn
  have hroot : (r * Real.sqrt (B ⬝ᵥ B)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hp.le, hsq]
  have hpos : 0 < r * Real.sqrt (B ⬝ᵥ B) := mul_pos hr (Real.sqrt_pos.mpr hp)
  have heq : r * Real.sqrt (B ⬝ᵥ B) = 1 := by nlinarith
  have hr' : r = (Real.sqrt (B ⬝ᵥ B))⁻¹ := by
    apply mul_right_cancel₀ hs
    rw [heq, inv_mul_cancel₀ hs]
  apply hanti
  rw [he, neg_smul, neg_neg, hr']
  rfl

lemma projected_second_form {X Y B C : Vec} {a b : ℝ}
    (hD : gramDet Y C ≠ 0) (hC : C = a • X + b • Y + B) :
    realNormalPart Y C B = -a • realNormalPart Y C X := by
  have hlin := realNormalPart_linear Y C
  have he := congrArg (realNormalPart Y C) hC
  rw [realNormalPart_self_right _ _ hD] at he
  simp only [hlin.map_add, hlin.map_smul, realNormalPart_self_left _ _ hD,
    smul_zero, add_zero] at he
  simpa only [neg_smul] using (eq_neg_of_add_eq_zero_right he.symm)

lemma projection_preserves_no_opposite_ray {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hanti : ∀ r : ℝ, 0 < r → n ≠ -r • B) :
    ∀ r : ℝ, 0 < r → realNormalPart Y C B ≠ -r • realNormalPart Y C n := by
  intro r hr hrel
  have hlin := realNormalPart_linear Y C
  have himage : realNormalPart Y C (B + r • n) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hrel]
    simp [neg_smul]
  have hz : B + r • n = 0 := projected_normal_kernel hD ha hXB hYB hC
    (by simp [dotProduct_add, dotProduct_smul, hXB, hXn])
    (by simp [dotProduct_add, dotProduct_smul, hYB, hYn]) himage
  apply hanti (1 / r) (one_div_pos.mpr hr)
  ext i
  have hi : B i + r * n i = 0 := congrFun hz i
  change n i = -(1 / r) * B i
  field_simp [hr.ne']
  linear_combination hi

lemma projected_tangent_no_opposite_ray {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a < 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hanti : ∀ r : ℝ, 0 < r → n ≠ -r • B) :
    ∀ r : ℝ, 0 < r → realNormalPart Y C X ≠ -r • realNormalPart Y C n := by
  have hD' := (velocity_gram_pos hD ha.ne hXB hYB hC).ne'
  have hsecond := projected_second_form hD' hC
  intro r hr hx
  have he : realNormalPart Y C B = -((-a) * r) • realNormalPart Y C n := by
    rw [hsecond, hx, smul_smul]
    congr 1
    ring
  exact projection_preserves_no_opposite_ray hD ha.ne hXB hYB hC hXn hYn hanti
    ((-a) * r) (mul_pos (neg_pos.mpr ha) hr) he

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ProjectedVelocityFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual frame formed from the projected tangent and preferred normal. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma projected_blend_nonzero {X Y B C n : Vec} {a b t : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a < 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0) (hn : n ⬝ᵥ n = 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hB : t < 1 → B ≠ 0)
    (hanti : t < 1 → normalize B ≠ -n) :
    blend (realNormalPart Y C X) (realNormalPart Y C n) t ≠ 0 := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz] at hn
    norm_num at hn
  have hpn := projected_normal_ne_zero hD ha.ne hXB hYB hC hXn hYn hn0
  have hD' := (velocity_gram_pos hD ha.ne hXB hYB hC).ne'
  apply blend_nonzero_of_not_opposite hpn ht
  · intro ht0 hpX
    have ht1 : t < 1 := by rw [ht0]; norm_num
    have hpb := projected_normal_ne_zero hD ha.ne hXB hYB hC hXB hYB (hB ht1)
    apply hpb
    rw [projected_second_form hD' hC, hpX, smul_zero]
  · intro ht1
    exact projected_tangent_no_opposite_ray hD ha hXB hYB hC hXn hYn
      (no_opposite_ray_of_normalized (hB ht1) hn (hanti ht1))

theorem projected_frame_orthonormal {X Y C n : Vec} {t : ℝ}
    (hD : gramDet Y C ≠ 0)
    (hn : blend (realNormalPart Y C X) (realNormalPart Y C n) t ≠ 0) :
    projectedFirst X Y C n t ⬝ᵥ projectedFirst X Y C n t = 1 ∧
      projectedSecond X Y C n t ⬝ᵥ projectedSecond X Y C n t = 1 ∧
      projectedFirst X Y C n t ⬝ᵥ projectedSecond X Y C n t = 0 ∧
      Y ⬝ᵥ projectedFirst X Y C n t = 0 ∧ C ⬝ᵥ projectedFirst X Y C n t = 0 ∧
      Y ⬝ᵥ projectedSecond X Y C n t = 0 ∧ C ⬝ᵥ projectedSecond X Y C n t = 0 := by
  have hx := realNormalPart_perp Y C X hD
  have hn' := realNormalPart_perp Y C n hD
  exact frame_orthonormal_of_nonzero hD hn hx.1 hn'.1 hx.2 hn'.2

lemma projectedFirst_zero (X Y C n : Vec) :
    projectedFirst X Y C n 0 = normalize (realNormalPart Y C X) := by
  simp [projectedFirst, first, blend]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem projected_frame_smoothOn {X Y C n : E → Vec} {t : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hn : ContDiffOn ℝ ∞ n U) (ht : ContDiffOn ℝ ∞ t U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hblend : ∀ x ∈ U, blend (realNormalPart (Y x) (C x) (X x))
      (realNormalPart (Y x) (C x) (n x)) (t x) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => projectedFirst (X x) (Y x) (C x) (n x) (t x)) U ∧
      ContDiffOn ℝ ∞ (fun x => projectedSecond (X x) (Y x) (C x) (n x) (t x)) U := by
  have hfirst (x : E) (hx : x ∈ U) :
      ContDiffAt ℝ ∞ (fun z => projectedFirst (X z) (Y z) (C z) (n z) (t z)) x := by
    have hy := hY.contDiffAt (hU.mem_nhds hx)
    have hc := hC.contDiffAt (hU.mem_nhds hx)
    exact first_smoothAt_of_nonzero
      (contDiffAt_realNormalPart hy hc (hX.contDiffAt (hU.mem_nhds hx)) (hD x hx))
      (contDiffAt_realNormalPart hy hc (hn.contDiffAt (hU.mem_nhds hx)) (hD x hx))
      (ht.contDiffAt (hU.mem_nhds hx)) (hblend x hx)
  refine ⟨fun x hx => (hfirst x hx).contDiffWithinAt, ?_⟩
  intro x hx
  have hy := hY.contDiffAt (hU.mem_nhds hx)
  have hc := hC.contDiffAt (hU.mem_nhds hx)
  have hpx := realNormalPart_perp (Y x) (C x) (X x) (hD x hx)
  have hpn := realNormalPart_perp (Y x) (C x) (n x) (hD x hx)
  exact (contDiffAt_unitPerp hy hc (hfirst x hx) (hD x hx)
    (normalize_nonzero (hblend x hx))
    (first_perp hpx.1 hpn.1 _) (first_perp hpx.2 hpn.2 _)).contDiffWithinAt

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectedFrameConstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the collar interpolation of the velocity frame from boundary
non-antipodality, with no interpolation function assumed. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma nonopposite_region_open {Ω : Set E} (hΩ : IsOpen Ω) {B n : E → Vec}
    (hB : ContDiffOn ℝ ∞ B Ω) (hn : ContDiffOn ℝ ∞ n Ω) :
    IsOpen {x | x ∈ Ω ∧ B x ≠ 0 ∧ normalize (B x) ≠ -n x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hb := hB.contDiffAt (hΩ.mem_nhds hx.1)
  have hn' := hn.contDiffAt (hΩ.mem_nhds hx.1)
  have hanti := ((normalize_smoothAt hb hx.2.1).continuousAt.ne_iff_eventually_ne
    hn'.continuousAt.neg).mp hx.2.2
  filter_upwards [hΩ.mem_nhds hx.1, hb.continuousAt.eventually_ne hx.2.1, hanti] with y hy hb' ha'
  exact ⟨hy, hb', ha'⟩

theorem exists_projected_collar_frame {K Ω : Set E}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {X Y C B n : E → Vec} {μ ν : E → ℝ}
    (hX : ContDiffOn ℝ ∞ X Ω) (hY : ContDiffOn ℝ ∞ Y Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hn : ContDiffOn ℝ ∞ n Ω)
    (hgeom : ∀ x ∈ Ω, gramDet (X x) (Y x) ≠ 0 ∧ μ x < 0 ∧
      X x ⬝ᵥ B x = 0 ∧ Y x ⬝ᵥ B x = 0 ∧
      C x = μ x • X x + ν x • Y x + B x ∧
      X x ⬝ᵥ n x = 0 ∧ Y x ⬝ᵥ n x = 0 ∧ n x ⬝ᵥ n x = 1)
    (hboundary : ∀ x ∈ K, B x ≠ 0 ∧ normalize (B x) ≠ -n x) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ Ω ∧
      ∃ e₁ e₂ : E → Vec, ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
          Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧
          Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) ∧
        (∀ x ∈ W, e₁ x = normalize (RealModes.realNormalPart (Y x) (C x) (X x))) := by
  let U : Set E := {x | x ∈ Ω ∧ B x ≠ 0 ∧ normalize (B x) ≠ -n x}
  have hU : IsOpen U := nonopposite_region_open hΩ hB hn
  have hKU : K ⊆ U := fun x hx => ⟨hKΩ hx, hboundary x hx⟩
  obtain ⟨W, hW, hKW, hWU, χ, ψ, hχ, _, _, _, hχr, _, _, hχs, hχone, _⟩ :=
    CollarVelocity.nested_compact_cutoffs hK hU hKU
  let t : E → ℝ := fun x => 1 - χ x
  have ht : ContDiff ℝ ∞ t := contDiff_const.sub hχ
  have hDt (x : E) (hx : x ∈ Ω) : gramDet (Y x) (C x) ≠ 0 := by
    obtain ⟨hd, hm, hxb, hyb, hc, _, _, _⟩ := hgeom x hx
    exact (velocity_gram_pos hd hm.ne hxb hyb hc).ne'
  have hblend (x : E) (hx : x ∈ Ω) :
      blend (RealModes.realNormalPart (Y x) (C x) (X x))
        (RealModes.realNormalPart (Y x) (C x) (n x)) (t x) ≠ 0 := by
    obtain ⟨hd, hm, hxb, hyb, hc, hxn, hyn, hn1⟩ := hgeom x hx
    have htr : t x ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hl, hu⟩ := hχr x
      exact ⟨by dsimp [t] <;> linarith, by dsimp [t] <;> linarith⟩
    have htu : t x < 1 → x ∈ U := by
      intro hlt
      apply hχs
      apply subset_tsupport χ
      apply Function.mem_support.mpr
      intro hz
      dsimp [t] at hlt
      linarith
    exact projected_blend_nonzero hd hm hxb hyb hc hxn hyn hn1 htr
      (fun h => (htu h).2.1) (fun h => (htu h).2.2)
  obtain ⟨he₁, he₂⟩ := projected_frame_smoothOn hΩ hX hY hC hn ht.contDiffOn hDt hblend
  refine ⟨W, hW, hKW, hWU.trans (fun _ hx => hx.1),
    (fun x => projectedFirst (X x) (Y x) (C x) (n x) (t x)),
    (fun x => projectedSecond (X x) (Y x) (C x) (n x) (t x)),
    he₁, he₂, ?_, ?_⟩
  · exact fun x hx => projected_frame_orthonormal (hDt x hx) (hblend x hx)
  · intro x hx
    have ht0 : t x = 0 := by simp [t, hχone x hx]
    simpa only [ht0] using projectedFirst_zero (X x) (Y x) (C x) (n x)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityLoop
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

lemma jetSection_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetSection F) := contDiff_id.prodMk (contDiff_realTwoJet hF)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructedSurfaceLoop
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the analytic surface-loop input from the geometric frame and
the controlled angle; no periodic velocity family is assumed here. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

lemma jetSlot_smooth (i : Fin 5) :
    ContDiff ℝ ∞ (fun j : CollarVelocity.JetBase => j.2 i) :=
  (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] Vec).contDiff.comp contDiff_snd

lemma jetNormal_smooth {Ω : Set CollarVelocity.JetBase}
    (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0) :
    ContDiffOn ℝ ∞ jetNormal Ω := by
  intro j hj
  exact (contDiffAt_realNormalPart (jetSlot_smooth 1).contDiffAt
    (jetSlot_smooth 4).contDiffAt (jetSlot_smooth 0).contDiffAt (hD j hj)).contDiffWithinAt

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a preferred normal to nearby second jets by orthogonal projection.
All coefficients and normal vectors are explicit functions of the jet. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

private lemma jetDot_smooth (a b : Fin 5) :
    ContDiff ℝ ∞ (fun j : GeometricJet => j.2 a ⬝ᵥ j.2 b) := by
  unfold dotProduct
  apply ContDiff.sum
  intro k _
  exact ((contDiff_apply ℝ ℝ k).comp (jetSlot_smooth a)).mul
    ((contDiff_apply ℝ ℝ k).comp (jetSlot_smooth b))

lemma jetTangentGram_smooth : ContDiff ℝ ∞ jetTangentGram := by
  exact ((jetDot_smooth 0 0).mul
    (jetDot_smooth 1 1)).sub
      ((jetDot_smooth 0 1).pow 2)

lemma jetAccelerationCoefficients_smoothAt {j : GeometricJet}
    (hj : jetTangentGram j ≠ 0) : ContDiffAt ℝ ∞ jetAccelerationCoefficients j := by
  have hd (a b : Fin 5) : ContDiffAt ℝ ∞ (fun z : GeometricJet => z.2 a ⬝ᵥ z.2 b) j :=
    (jetDot_smooth a b).contDiffAt
  exact (((hd 1 1).mul (hd 0 4)).sub ((hd 0 1).mul (hd 1 4))).div
      jetTangentGram_smooth.contDiffAt hj |>.prodMk
    ((((hd 0 0).mul (hd 1 4)).sub ((hd 0 1).mul (hd 0 4))).div
      jetTangentGram_smooth.contDiffAt hj)

lemma jetSecondNormal_smoothAt {j : GeometricJet} (hj : jetTangentGram j ≠ 0) :
    ContDiffAt ℝ ∞ jetSecondNormal j :=
  contDiffAt_realNormalPart (jetSlot_smooth 0).contDiffAt (jetSlot_smooth 1).contDiffAt
    (jetSlot_smooth 4).contDiffAt hj

lemma jetProjectedPreferred_smoothAt {n : Base → Vec} {j : GeometricJet}
    (hn : ContDiffAt ℝ ∞ n j.1) (hj : jetTangentGram j ≠ 0) :
    ContDiffAt ℝ ∞ (jetProjectedPreferred n) j :=
  contDiffAt_realNormalPart (jetSlot_smooth 0).contDiffAt (jetSlot_smooth 1).contDiffAt
    (hn.comp j contDiffAt_fst) hj

lemma jetPreferred_smoothAt {n : Base → Vec} {j : GeometricJet}
    (hn : ContDiffAt ℝ ∞ n j.1) (hj : jetTangentGram j ≠ 0)
    (hproj : jetProjectedPreferred n j ≠ 0) :
    ContDiffAt ℝ ∞ (jetPreferred n) j :=
  normalize_smoothAt (jetProjectedPreferred_smoothAt hn hj) hproj

lemma jetAcceleration_decomposition (j : GeometricJet) :
    j.2 4 = (jetAccelerationCoefficients j).1 • j.2 0 +
      (jetAccelerationCoefficients j).2 • j.2 1 + jetSecondNormal j := by
  unfold jetAccelerationCoefficients jetSecondNormal realNormalPart jetTangentGram
  abel

lemma realNormalPart_eq_self {X Y n : Vec} (hX : X ⬝ᵥ n = 0) (hY : Y ⬝ᵥ n = 0) :
    realNormalPart X Y n = n := by
  simp [realNormalPart,hX,hY]

lemma jetPreferred_on_section {F n : Base → Vec} {p : Base}
    (hX : coordDeriv dx F p ⬝ᵥ n p = 0) (hY : coordDeriv dy F p ⬝ᵥ n p = 0)
    (hn : n p ⬝ᵥ n p = 1) : jetPreferred n (CollarVelocity.jetSection F p) = n p := by
  change normalize (realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (n p)) = n p
  rw [realNormalPart_eq_self hX hY,normalize_of_unit hn]

lemma jetAccelerationCoefficients_on_section {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) : jetAccelerationCoefficients (CollarVelocity.jetSection F p) =
      metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2 := by
  rw [induced_connection_yy hF p]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetDomain
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An open domain of genuine second jets carrying the normal-frame geometry.
The preferred normal is projected from the original spatial normal field. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

lemma preferredJetDomain_open {U : Set Base} (hU : IsOpen U) {n : Base → Vec}
    (hn : ContDiffOn ℝ ∞ n U) : IsOpen (preferredJetDomain U n) := by
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hp := hn.contDiffAt (hU.mem_nhds hj.1)
  have hu := (hU.preimage continuous_fst).mem_nhds hj.1
  have hD := jetTangentGram_smooth.continuous.continuousAt.eventually_ne hj.2.1
  have hmu := (jetAccelerationCoefficients_smoothAt hj.2.1).fst.continuousAt.eventually
    (gt_mem_nhds hj.2.2.1)
  have hproj := (jetProjectedPreferred_smoothAt hp hj.2.1).continuousAt.eventually_ne hj.2.2.2
  filter_upwards [hu,hD,hmu,hproj] with k hk hd hm hp
  exact ⟨hk,hd,hm,hp⟩

lemma preferredJetDomain_geometry {U : Set Base} {n : Base → Vec}
    {j : GeometricJet} (hj : j ∈ preferredJetDomain U n) :
    gramDet (j.2 0) (j.2 1) ≠ 0 ∧ (jetAccelerationCoefficients j).1 < 0 ∧
      j.2 0 ⬝ᵥ jetSecondNormal j = 0 ∧ j.2 1 ⬝ᵥ jetSecondNormal j = 0 ∧
      j.2 4 = (jetAccelerationCoefficients j).1 • j.2 0 +
        (jetAccelerationCoefficients j).2 • j.2 1 + jetSecondNormal j ∧
      j.2 0 ⬝ᵥ jetPreferred n j = 0 ∧ j.2 1 ⬝ᵥ jetPreferred n j = 0 ∧
      jetPreferred n j ⬝ᵥ jetPreferred n j = 1 := by
  have hB := realNormalPart_perp (j.2 0) (j.2 1) (j.2 4) hj.2.1
  have hN := realNormalPart_perp (j.2 0) (j.2 1) (n j.1) hj.2.1
  exact ⟨hj.2.1,hj.2.2.1,hB.1,hB.2,jetAcceleration_decomposition j,
    dot_normalize_zero hN.1,dot_normalize_zero hN.2,normalize_unit hj.2.2.2⟩

lemma actual_jet_mem_preferred_domain {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {U : Set Base} {p : Base} (hp : p ∈ U)
    (hI : Function.Injective (fderiv ℝ F p))
    (hN : coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy) :
    CollarVelocity.jetSection F p ∈ preferredJetDomain U n := by
  have hmu : (jetAccelerationCoefficients (CollarVelocity.jetSection F p)).1 < 0 := by
    rw [jetAccelerationCoefficients_on_section hF]
    rw [coordinateMetricHessian_fst_dy] at hHess
    exact neg_pos.mp hHess
  have hpN : jetProjectedPreferred n (CollarVelocity.jetSection F p) = n p := by
    exact realNormalPart_eq_self hN.1 hN.2.1
  refine ⟨hp,gramDet_ne_zero_of_injective _ hI,hmu,?_⟩
  rw [hpN]
  intro hz
  have hh := hN.2.2
  rw [hz] at hh
  norm_num at hh

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth velocity frame on an open neighborhood of the actual second
jets, equal to the projected tangent frame near the selected boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

lemma preferredJetDomain_velocity_gram {U : Set Base} {n : Base → Vec}
    {j : GeometricJet} (hj : j ∈ preferredJetDomain U n) :
    gramDet (j.2 1) (j.2 4) ≠ 0 := by
  obtain ⟨hD,hmu,hXB,hYB,hC,_,_,_⟩ := preferredJetDomain_geometry hj
  exact (velocity_gram_pos hD hmu.ne hXB hYB hC).ne'

theorem exists_preferred_jet_frame {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {U C₀ : Set Base} (hU : IsOpen U)
    (hn : ContDiffOn ℝ ∞ n U) (hC₀ : IsCompact C₀) (hCU : C₀ ⊆ U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (hboundary : ∀ p ∈ C₀, realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p) :
    ∃ W : Set GeometricJet, IsOpen W ∧ CollarVelocity.jetSection F '' C₀ ⊆ W ∧
      W ⊆ preferredJetDomain U n ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ (preferredJetDomain U n) ∧
        ContDiffOn ℝ ∞ e₂ (preferredJetDomain U n) ∧
        (∀ j ∈ preferredJetDomain U n,
          e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧
          j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
        (∀ j ∈ W, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) := by
  let Ω := preferredJetDomain U n
  have hΩ : IsOpen Ω := preferredJetDomain_open hU hn
  have hmem (p : Base) (hp : p ∈ U) : CollarVelocity.jetSection F p ∈ Ω :=
    actual_jet_mem_preferred_domain hF hp (hI p hp) (hN p hp) (hHess p hp)
  have hK : IsCompact (CollarVelocity.jetSection F '' C₀) :=
    hC₀.image (CollarVelocity.jetSection_smooth hF).continuous
  have hKΩ : CollarVelocity.jetSection F '' C₀ ⊆ Ω := by
    rintro _ ⟨p,hp,rfl⟩
    exact hmem p (hCU hp)
  have hBn : ContDiffOn ℝ ∞ jetSecondNormal Ω :=
    fun j hj => (jetSecondNormal_smoothAt hj.2.1).contDiffWithinAt
  have hNn : ContDiffOn ℝ ∞ (jetPreferred n) Ω := by
    intro j hj
    exact (jetPreferred_smoothAt (hn.contDiffAt (hU.mem_nhds hj.1)) hj.2.1 hj.2.2.2).contDiffWithinAt
  have hb : ∀ j ∈ CollarVelocity.jetSection F '' C₀,
      jetSecondNormal j ≠ 0 ∧ normalize (jetSecondNormal j) ≠ -jetPreferred n j := by
    rintro _ ⟨p,hp,rfl⟩
    have he : jetSecondNormal (CollarVelocity.jetSection F p) = realSecondForm F dy dy p := rfl
    rw [he,jetPreferred_on_section (hN p (hCU hp)).1 (hN p (hCU hp)).2.1 (hN p (hCU hp)).2.2]
    exact hboundary p hp
  obtain ⟨W,hW,hKW,hWΩ,e₁,e₂,he₁,he₂,hframe,hfirst⟩ := exists_projected_collar_frame
    hK hΩ hKΩ (jetSlot_smooth 0).contDiffOn (jetSlot_smooth 1).contDiffOn
    (jetSlot_smooth 4).contDiffOn hBn hNn
    (fun j hj => preferredJetDomain_geometry hj) hb
  refine ⟨W,hW,hKW,hWΩ,e₁,e₂,he₁,he₂,hframe,?_⟩
  intro j hj
  have he : e₁ j = normalize (jetNormal j) := hfirst j hj
  refine ⟨?_,he⟩
  intro hz
  have hu := (hframe j (hWΩ hj)).1
  rw [he,hz] at hu
  norm_num [VelocityFrame.normalize] at hu

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedJetDomain
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The velocity radius stays nonzero on an open neighborhood of the
actual compact jet set, including the zero-amplitude boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

lemma supportedJetDomain_open {U : Set Base} (hU : IsOpen U) {n : Base → Vec}
    (hn : ContDiffOn ℝ ∞ n U) {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    IsOpen (supportedJetDomain U n a) := by
  have hΩ := preferredJetDomain_open hU hn
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hjΩ := hj.1
  have hv : ContDiffAt ℝ ∞ jetNormal j :=
    contDiffAt_realNormalPart (jetSlot_smooth 1).contDiffAt (jetSlot_smooth 4).contDiffAt
      (jetSlot_smooth 0).contDiffAt (preferredJetDomain_velocity_gram hjΩ)
  have hamp : ContinuousAt (fun j : GeometricJet => a j.1) j :=
    (ha.continuous.comp continuous_fst).continuousAt
  rcases hj.2 with hv0 | ha0
  · filter_upwards [hΩ.mem_nhds hjΩ,hv.continuousAt.eventually_ne hv0] with k hk hvk
    exact ⟨hk,Or.inl hvk⟩
  · filter_upwards [hΩ.mem_nhds hjΩ,hamp.eventually_ne ha0] with k hk hak
    exact ⟨hk,Or.inr hak⟩

lemma actual_jet_mem_supported_domain {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {a : Base → ℝ} {U : Set Base} {p : Base} (hp : p ∈ U)
    (hI : Function.Injective (fderiv ℝ F p))
    (hN : coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (hboundary : a p = 0 → realSecondForm F dy dy p ≠ 0) :
    CollarVelocity.jetSection F p ∈ supportedJetDomain U n a := by
  have hj := actual_jet_mem_preferred_domain hF hp hI hN hHess
  refine ⟨hj,?_⟩
  by_cases ha : a p = 0
  · left
    have hg := preferredJetDomain_velocity_gram hj
    have hgeom := preferredJetDomain_geometry hj
    have hb := hboundary ha
    have hproj := projected_normal_ne_zero hgeom.1 hgeom.2.1.ne hgeom.2.2.1 hgeom.2.2.2.1
      hgeom.2.2.2.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hb
    have he := projected_second_form hg hgeom.2.2.2.2.1
    intro hv
    apply hproj
    rw [he]
    change -((jetAccelerationCoefficients (CollarVelocity.jetSection F p)).1) •
      jetNormal (CollarVelocity.jetSection F p) = 0
    rw [hv,smul_zero]
  · exact Or.inr ha

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularProfileThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed coefficient bounds and a spatial turn threshold, chosen before
any angular function or any of its derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_profile_threshold {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hRpos : ∀ x ∈ U, 0 < R x) (d : E) :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ H : ℝ, 0 ≤ H → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (α : E → ℝ) x, x ∈ K → DifferentiableAt ℝ α x → ∀ β : ℝ,
        circularSpatialProfile Q X Y C R e₁ e₂ α β x d ∈ regularBoundaryProfiles ∧
        sLo ≤ profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 0 ∧
        profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 0 ≤ sHi ∧
        |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 1| ≤ D ∧
        (Λ < fderiv ℝ α x d →
          H+2 < |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 2|) := by
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hcoef⟩ := compact_frozen_coefficient_bounds
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe (fun x hx => (hRpos x hx).ne') d
  obtain ⟨B,hB,herror⟩ := compact_spatialError_bound_on hU hK hKU hQ hR h₁ h₂ d
  have hrcont : ContinuousOn R K := hR.continuousOn.mono hKU
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,fun H _ => ⟨1,zero_lt_one,?_⟩⟩
    simp [hE]
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne hrcont
  have hr : 0 < R p := hRpos p (hKU hp)
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,fun H hH =>
    ⟨(H+1+4*B+1)/(R p),div_pos (by positivity) hr,?_⟩⟩
  intro α x hx hα β
  have hxU := hKU hx
  have hf := hframe x hxU
  have hQx := (hQ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hRx := (hR.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h1x := (h₁.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h2x := (h₂.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hreg : circularSpatialProfile Q X Y C R e₁ e₂ α β x d ∈ regularBoundaryProfiles :=
    circularBoundaryProfile_regular (hD x hxU) (hRpos x hxU).ne'
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.2
  refine ⟨hreg,?_,?_,?_,?_⟩
  · exact (hcoef x hx (α x)).1
  · exact (hcoef x hx (α x)).2.1
  · rw [circularSpatialProfile_first β hQx hRx h1x h2x hα hf]
    exact (hcoef x hx (α x)).2.2
  · intro hlarge
    have hh := circularSpatialProfile_mixed_dominates (X := X) (Y := Y) (C := C) β hQx hRx h1x h2x hα
      (hD x hxU) hf hr (hmin hx) hB (by linarith : 0 ≤ H+1) (herror α x hx) hlarge
    linarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFamilyProfile
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five boundary profiles for a smooth family of circular velocities. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_slice_first {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {x : E} {t : ℝ} (hf : DifferentiableAt ℝ f (x,t)) (d : E) :
    fderiv ℝ (fun y => f (y,t)) x d = fderiv ℝ f (x,t) (d,0) := by
  have hslice : HasFDerivAt (fun y : E => (y,t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact congrArg (fun L : E →L[ℝ] F => L d) (hf.hasFDerivAt.comp x hslice).fderiv

lemma circularFamilyProfile_spatial {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α (x,t)) (d : E) :
    circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t) =
      circularSpatialProfile Q X Y C R e₁ e₂ (fun y => α (y,t))
        (fderiv ℝ α (x,t) (0,1)) x d := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t))
  have hd := (hQ.hasFDerivAt.comp (x,t) hf).add ((hR.hasFDerivAt.comp (x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (x,t) hf))))
  change HasFDerivAt (fun w : E × ℝ =>
    Q w.1 + R w.1 • direction (e₁ w.1) (e₂ w.1) (α w)) _ (x,t) at hd
  unfold circularFamilyProfile circularSpatialProfile
  rw [fderiv_slice_first hd.differentiableAt]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFamilyThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the actual joint position/phase profile. All constants are
fixed before the angular function and its transverse derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circularFamilyProfile_turn_iff (Q X Y C e₁ e₂ : E → Vec) (R : E → ℝ)
    (α : E × ℝ → ℝ) (d x : E) (t : ℝ)
    (hD : gramDet (Y x) (C x) ≠ 0) (hR : R x ≠ 0)
    (hf : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 3 = 0 ↔
      fderiv ℝ α (x,t) (0,1) = 0 := by
  exact circularBoundaryProfile_turn_iff hD hR hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ClosedIntervalTurns
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-turn estimates on a half-open period also hold at the closed
endpoint needed for compact profile estimates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes

lemma closed_interval_turns {U K : Set Base} (hU : IsOpen U) (hKU : K ⊆ U)
    {α : Base × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (U ×ˢ univ))
    (hper : ∀ x ∈ U, Function.Periodic (fun t => α (x,t)) 1)
    {τ : Base → ℝ} {Λ : ℝ}
    (hturn : ∀ x ∈ K, ∀ t ∈ Ico (0 : ℝ) 1,
      deriv (fun s => α (x,s)) t = 0 ↔ t = 0 ∨ t = τ x)
    (hlarge : ∀ x ∈ K,
      Λ < fderiv ℝ (fun y => α (y,0)) x dy ∧
      Λ < fderiv ℝ (fun y => α (y,τ x)) x dy) :
    ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      fderiv ℝ α (x,t) (0,1) = 0 → Λ < fderiv ℝ α (x,t) (dy,0) := by
  intro x hx t ht hz
  have hxU := hKU hx
  have hs (t : ℝ) : fderiv ℝ (fun y => α (y,t)) x dy = fderiv ℝ α (x,t) (dy,0) :=
    fderiv_slice_first
      ((hα.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hxU,mem_univ t⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) dy
  rw [← hs]
  rcases lt_or_eq_of_le ht.2 with ht1 | rfl
  · have hd : deriv (fun s => α (x,s)) t = 0 := by
      rw [(LocalPeriodicCalculus.angle_hasDerivAt hU hα hxU t).deriv]
      exact hz
    rcases (hturn x hx t ⟨ht.1,ht1⟩).mp hd with rfl | rfl
    · exact (hlarge x hx).1
    · exact (hlarge x hx).2
  · have he : (fun y => α (y,1)) =ᶠ[𝓝 x] (fun y => α (y,0)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      simpa only [zero_add] using hper y hy 0
    rw [he.fderiv_eq]
    exact (hlarge x hx).1

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalCircularFamilyThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the actual joint position/phase profile. All constants are
fixed before the angular function and its transverse derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_family_threshold_local {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hRpos : ∀ x ∈ U, 0 < R x) (d : E) :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ H : ℝ, 0 ≤ H → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ V : Set E, IsOpen V → K ⊆ V → V ⊆ U →
      ∀ α : E × ℝ → ℝ, ContDiffOn ℝ ∞ α (V ×ˢ univ) →
      ∀ x ∈ K, ∀ t : ℝ,
      let J := circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)
      J ∈ regularBoundaryProfiles ∧
      sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
      |profileCoefficients J 1| ≤ D ∧
      (Λ < fderiv ℝ α (x,t) (d,0) → H+2 < |profileCoefficients J 2|) := by
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hbounds⟩ := compact_circular_profile_threshold
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe hRpos d
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Λ,hΛ,hprofile⟩ := hbounds H hH
  refine ⟨Λ,hΛ,?_⟩
  intro V hV hKV _ α hα x hx t
  have hxU := hKU hx
  have hαat : DifferentiableAt ℝ α (x,t) :=
    (hα.contDiffAt ((hV.prod isOpen_univ).mem_nhds
      (show (x,t) ∈ V ×ˢ univ from ⟨hKV hx,mem_univ t⟩))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hαslice : DifferentiableAt ℝ (fun y => α (y,t)) x :=
    hαat.comp x (differentiableAt_id.prodMk (differentiableAt_const t))
  have heq := circularFamilyProfile_spatial (X := X) (Y := Y) (C := C)
    ((hQ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hR.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₁.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₂.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hαat d
  dsimp only
  rw [heq]
  obtain ⟨hreg,hlo,hhi,hd,hlarge⟩ := hprofile (fun y => α (y,t)) x hx hαslice
    (fderiv ℝ α (x,t) (0,1))
  refine ⟨hreg,hlo,hhi,hd,?_⟩
  intro hderiv
  apply hlarge
  rw [fderiv_slice_first hαat]
  exact hderiv

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceCircularThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freeze the circular coefficient bounds on the original surface before
choosing its supported angle and its smaller jet neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

theorem compact_surface_circular_threshold {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U K : Set Base} {Ω : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hK : IsCompact K) (hKΩ : CollarVelocity.jetSection F '' K ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ H : ℝ, 0 ≤ H → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ Z : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' K ⊆ Z →
        (Z : Set GeometricJet) ⊆ Ω →
      ∀ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) →
      ∀ x ∈ K, ∀ t : ℝ,
        let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
        J ∈ regularBoundaryProfiles ∧
        sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
        |profileCoefficients J 1| ≤ D ∧
        (Λ < fderiv ℝ (fun z => α (CollarVelocity.jetSection F z.1,z.2)) (x,t) (dy,0) →
          H+2 < |profileCoefficients J 2|) := by
  let V : Set Base := CollarVelocity.jetSection F ⁻¹' Ω
  have hσ := CollarVelocity.jetSection_smooth hF
  have hV : IsOpen V := Ω.isOpen.preimage hσ.continuous
  have hKV : K ⊆ V := fun x hx => hKΩ (mem_image_of_mem _ hx)
  have hmaps : MapsTo (CollarVelocity.jetSection F) V Ω := fun _ hx => hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ hx).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (CollarVelocity.jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (CollarVelocity.jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ hx).2
  have hR := velocityRadius_smoothOn hv ha.contDiffOn hnonzero
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hc := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hbounds⟩ := compact_circular_family_threshold_local
    hV hK hKV (hx.sub hv) hx hy hc hR
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hD
    (fun x hx => hframe (CollarVelocity.jetSection F x) hx)
    (fun x hx => velocityRadius_pos (hnonzero x hx)) dy
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Λ,hΛ,hbound⟩ := hbounds H hH
  refine ⟨Λ,hΛ,?_⟩
  intro Z hKZ hZΩ α hα x hx t
  let W : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hW : IsOpen W := Z.isOpen.preimage hσ.continuous
  have hKW : K ⊆ W := fun x hx => hKZ (mem_image_of_mem _ hx)
  have hWV : W ⊆ V := fun _ hx => hZΩ hx
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (W ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  exact hbound W hW hKW hWV _ hα' x hx t

lemma surfaceCircularProfile_turn_iff {F n : Base → Vec} {a : Base → ℝ}
    {U : Set Base} {Ω : Set GeometricJet} (hΩ : Ω ⊆ supportedJetDomain U n a)
    {e₁ e₂ : GeometricJet → Vec}
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (α : GeometricJet × ℝ → ℝ) {x : Base} (hx : CollarVelocity.jetSection F x ∈ Ω) (t : ℝ) :
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 ↔
      fderiv ℝ (fun z => α (CollarVelocity.jetSection F z.1,z.2)) (x,t) (0,1) = 0 := by
  exact circularFamilyProfile_turn_iff _ _ _ _ _ _ _ _ _ _ _
    (preferredJetDomain_velocity_gram (hΩ hx).1)
    (velocityRadius_pos (hΩ hx).2).ne' (hframe _ hx)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ActualSurfaceCollarFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preferred frame and its domain are fixed before prescribing the
transverse turn size in the actual supported loop construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates

theorem actual_surface_collar_family {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    :
    ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
      (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      (∃ B : Set GeometricJet, IsOpen B ∧
        CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ B ∧
        ∀ j ∈ B, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set Base, IsOpen V ∧ {p ∈ T | a p = 0} ⊆ V ∧
      ∀ (K P : Set Base), IsCompact K → K ⊆ T → (∀ p ∈ K, 0 < a p) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ turn : ℝ, ∃ Z : TopologicalSpace.Opens GeometricJet,
        CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          (∀ x ∈ V, ∀ t, |α (CollarVelocity.jetSection F x,t)| < ε) ∧
          ∃ τ : Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K,
              turn < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x dy ∧
              turn < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x dy := by
  let C₀ : Set Base := {p ∈ T | a p = 0}
  have hC : IsCompact C₀ := hT.inter_right (isClosed_eq ha.continuous continuous_const)
  have hCU : C₀ ⊆ U := fun _ hp => hTU hp.1
  obtain ⟨W,hW,hCW,hWΩ,e₁,e₂,he₁,he₂,hframe,hcollar⟩ := exists_preferred_jet_frame
    hF hU hn hC hCU hI hN hHess (fun p hp => hboundary p hp.1 hp.2)
  let Ω := supportedJetDomain U n a
  have hΩ : IsOpen Ω := supportedJetDomain_open hU hn ha
  let L := CollarVelocity.jetSection F '' T
  let Cj := CollarVelocity.jetSection F '' C₀
  have hL : IsCompact L := hT.image (CollarVelocity.jetSection_smooth hF).continuous
  have hCj : IsCompact Cj := hC.image (CollarVelocity.jetSection_smooth hF).continuous
  have hLΩ : L ⊆ Ω := by
    rintro _ ⟨p,hp,rfl⟩
    exact actual_jet_mem_supported_domain hF (hTU hp) (hI p (hTU hp))
      (hN p (hTU hp)) (hHess p (hTU hp)) (fun h => (hboundary p hp h).1)
  let V₀ : Set GeometricJet := W ∩ Ω
  have hV₀ : IsOpen V₀ := hW.inter hΩ
  have hCV₀ : Cj ⊆ V₀ := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨hCW (mem_image_of_mem _ hp),hLΩ (mem_image_of_mem _ hp.1)⟩
  have hAmp : ∀ j ∈ L \ Cj, 0 < a j.1 := by
    rintro j ⟨⟨p,hp,rfl⟩,hj⟩
    apply lt_of_le_of_ne (haT p hp)
    intro hz
    exact hj (mem_image_of_mem _ ⟨hp,hz.symm⟩)
  have hCL : Cj ⊆ L := image_mono (fun _ hp => hp.1)
  have hV₀Ω : V₀ ⊆ Ω := inter_subset_right
  have he1 : ContDiffOn ℝ ∞ e₁ Ω := he₁.mono (fun _ hj => hj.1)
  have he2 : ContDiffOn ℝ ∞ e₂ Ω := he₂.mono (fun _ hj => hj.1)
  have hfr := fun j (hj : j ∈ Ω) => hframe j hj.1
  obtain ⟨W₀,hW₀,hCW₀,_,hfamily⟩ := constructed_surface_collar_family hF hCj hL hCL
    hV₀ hΩ hCV₀ hV₀Ω hLΩ he1 he2 (ha.comp contDiff_fst).contDiffOn
    (fun j hj => preferredJetDomain_velocity_gram hj.1) hfr
    (fun j hj => hcollar j hj.1) (fun j hj => hj.2) hAmp
    (by rintro _ ⟨p,hp,rfl⟩; exact hp.2)
  refine ⟨⟨Ω,hΩ⟩,hLΩ,Subset.rfl,e₁,e₂,he1,he2,hfr,⟨W,hW,hCW,hcollar⟩,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,_,hfamily'⟩ := hfamily ε hε
  refine ⟨CollarVelocity.jetSection F ⁻¹' V,hV.preimage (CollarVelocity.jetSection_smooth hF).continuous,
    (fun p hp => hCV (mem_image_of_mem _ hp)),?_⟩
  intro K P hK hKT haK hP hPK hlocal turn
  obtain ⟨O,hO,hKO,_,hOpos⟩ := CollarVelocity.compact_open_thickening hK
    (isOpen_lt continuous_const ha.continuous) haK
  have hCO : ∀ j ∈ Cj, j.1 ∉ closure O := by
    rintro _ ⟨p,hp,rfl⟩ hx
    have hh := hOpos hx
    change 0 < a p at hh
    rw [hp.2] at hh
    exact lt_irrefl _ hh
  obtain ⟨Z,hLZ,hZΩ,l,hl,hzero,α,hα,hper,hvel,hsmall,τ,hturn,hlarge⟩ :=
    hfamily' K O P hK (fun _ hx => mem_image_of_mem _ (hKT hx)) hO hKO hCO hP hPK hlocal turn
  refine ⟨Z,hLZ,hZΩ,l,hl,?_,α,hα,hper,hvel,?_,τ,hturn,hlarge⟩
  · obtain ⟨W',hW',hCW',_,hzero'⟩ := hzero
    exact ⟨W',hW',hCW',hzero'⟩
  · exact fun x hx t => hsmall _ hx t

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ActualSurfaceCollarProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preferred frame and its domain are fixed before prescribing the
transverse turn size in the actual supported loop construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation

theorem actual_surface_collar_profile_family_oai {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    :
    ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
      (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      (∃ B : Set GeometricJet, IsOpen B ∧
        CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ B ∧
        ∀ j ∈ B, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) ∧
      ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set Base, IsOpen V ∧ {p ∈ T | a p = 0} ⊆ V ∧
      ∀ (K P : Set Base), IsCompact K → K ⊆ T → (∀ p ∈ K, 0 < a p) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ H : ℝ, 0 ≤ H → ∃ Z : TopologicalSpace.Opens GeometricJet,
        CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          (∀ x ∈ V, ∀ t, |α (CollarVelocity.jetSection F x,t)| < ε) ∧
          (∀ x ∈ T, ∀ t : ℝ,
            let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
            J ∈ regularBoundaryProfiles ∧ sLo ≤ profileCoefficients J 0 ∧
              profileCoefficients J 0 ≤ sHi ∧ |profileCoefficients J 1| ≤ D) ∧
          ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
            profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 →
              H+2 < |profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 2| := by
  obtain ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hcollar,hfamily⟩ :=
    actual_surface_collar_family hF ha hT hU hTU hn hI hN hHess haT hboundary
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hthreshold⟩ :=
    compact_surface_circular_threshold hF ha hΩ hT hTΩ h₁ h₂ hframe
  refine ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hcollar,sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hfamily'⟩ := hfamily ε hε
  refine ⟨V,hV,hCV,?_⟩
  intro K P hK hKT haK hP hPK hlocal H hH
  obtain ⟨Λ,_,hprofile⟩ := hthreshold H hH
  obtain ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,τ,hturn,hlarge⟩ :=
    hfamily' K P hK hKT haK hP hPK hlocal Λ
  refine ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,?_,?_⟩
  · intro x hx t
    obtain ⟨hreg,hlo,hhi,hd,_⟩ := hprofile Z hTZ hZΩ α hα x hx t
    exact ⟨hreg,hlo,hhi,hd⟩
  · let W : Set Base := CollarVelocity.jetSection F ⁻¹' Z
    have hσ := CollarVelocity.jetSection_smooth hF
    have hW : IsOpen W := Z.isOpen.preimage hσ.continuous
    have hKW : K ⊆ W := fun x hx => hTZ (mem_image_of_mem _ (hKT hx))
    have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
        (W ×ˢ univ) :=
      hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
    have hturn' := closed_interval_turns hW hKW hα'
      (fun x hx => hper (CollarVelocity.jetSection F x) hx) hturn hlarge
    intro x hx t ht hz
    apply (hprofile Z hTZ hZΩ α hα x (hKT hx) t).2.2.2.2
    apply hturn' x hx t ht
    exact (surfaceCircularProfile_turn_iff hΩ hframe α
      (hTΩ (mem_image_of_mem _ (hKT hx))) t).mp hz

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family_oai
