-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:38:08.145919+00:00
-- url     : https://prove2.me/submissions/add58422-09ca-4ea0-ab5b-c416b81d00a4

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_profile_family

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
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
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

lemma norm_smul_normalize {v : Vec} (hv : v ≠ 0) :
    Real.sqrt (v ⬝ᵥ v) • normalize v = v := by
  simp [normalize, smul_smul, (Real.sqrt_pos.mpr (dot_self_pos hv)).ne']

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ActualSecondFormFrame
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual orthonormal normal frame and the Gauss-constrained coordinates
of the second fundamental form of a smooth surface in four-space. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

theorem exists_secondFormFrame_with_coordinates {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) :
    ∃ d : SecondFormFrame F p
      (coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p),
      d.n = normalize (realSecondForm F dy dy p) ∧
      d.m = unitPerp (coordDeriv dx F p) (coordDeriv dy F p) d.n ∧
      d.S = Real.sqrt (realSecondForm F dy dy p ⬝ᵥ realSecondForm F dy dy p) ∧
      d.D = realSecondForm F dx dy p ⬝ᵥ d.n ∧
      d.N = realSecondForm F dx dy p ⬝ᵥ d.m ∧
      d.L = realSecondForm F dx dx p ⬝ᵥ d.m := by
  let X := coordDeriv dx F p
  let Y := coordDeriv dy F p
  let B := realSecondForm F dy dy p
  let n := normalize B
  let m := unitPerp X Y n
  let S := Real.sqrt (B ⬝ᵥ B)
  let Bxx := realSecondForm F dx dx p
  let Bxy := realSecondForm F dx dy p
  let D := Bxy ⬝ᵥ n
  let N := Bxy ⬝ᵥ m
  let L := Bxx ⬝ᵥ m
  let k := coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p
  have hperp (v w : Base) : X ⬝ᵥ realSecondForm F v w p = 0 ∧
      Y ⬝ᵥ realSecondForm F v w p = 0 := realNormalPart_perp X Y _ hD
  have hn : n ⬝ᵥ n = 1 := normalize_unit hB
  have hnn : n ≠ 0 := normalize_nonzero hB
  have hXn : X ⬝ᵥ n = 0 := dot_normalize_zero (hperp dy dy).1
  have hYn : Y ⬝ᵥ n = 0 := dot_normalize_zero (hperp dy dy).2
  obtain ⟨hXm,hYm,hnm⟩ := unitPerp_orthogonal X Y n
  have hm : m ⬝ᵥ m = 1 := unitPerp_unit hD hnn hXn hYn
  have hS : 0 < S := Real.sqrt_pos.mpr (VelocityFrame.dot_self_pos hB)
  have hyy : B = S • n := (norm_smul_normalize hB).symm
  have hreconstruct (v w : Base) : realSecondForm F v w p =
      (realSecondForm F v w p ⬝ᵥ n) • n+(realSecondForm F v w p ⬝ᵥ m) • m := by
    have hr := plane_coordinates_reconstruct hD hn hm hnm hXn hXm hYn hYm
      (hperp v w).1 (hperp v w).2
    simpa only [planeLift_apply,VelocityFrame.planeCoordinates,Matrix.cons_val_zero,
      Matrix.cons_val_one] using hr.symm
  have hlength : D^2+N^2 = Bxy ⬝ᵥ Bxy :=
    plane_coordinates_length hD hn hm hnm hXn hXm hYn hYm (hperp dx dy).1 (hperp dx dy).2
  have hgauss : Bxx ⬝ᵥ B-Bxy ⬝ᵥ Bxy = k := gauss_metric_identity hF p hD
  rw [hyy,dotProduct_smul] at hgauss
  change S*(Bxx ⬝ᵥ n)-Bxy ⬝ᵥ Bxy = k at hgauss
  have hcoef : Bxx ⬝ᵥ n = (k+D^2+N^2)/S := by
    apply (eq_div_iff hS.ne').mpr
    nlinarith
  refine ⟨{
    n := n
    m := m
    S := S
    D := D
    N := N
    L := L
    size_pos := hS
    unit_n := hn
    unit_m := hm
    orthogonal := hnm
    tangent_n := ⟨hXn,hYn⟩
    tangent_m := ⟨hXm,hYm⟩
    xx := ?_
    xy := hreconstruct dx dy
    yy := hyy },rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [hreconstruct dx dx]
  change (Bxx ⬝ᵥ n) • n+L • m = _
  rw [hcoef]


end ClosedSurfaceR4.GeometryPreservation

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

lemma contDiffAt_profileComplement {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileComplement J := by
  have hn := realNormalPart_perp (J 0) (J 1) (J 2) hJ.1
  exact contDiffAt_unitPerp
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (contDiffAt_profilePreferred hJ) hJ.1 (normalize_nonzero hJ.2)
    (dot_normalize_zero hn.1) (dot_normalize_zero hn.2)

lemma isOpen_regularBoundaryProfiles : IsOpen regularBoundaryProfiles := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : BoundaryProfile => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_profileNormalPart hJ.1).continuousAt.eventually_ne hJ.2)

lemma contDiffAt_profileCoefficients {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileCoefficients J := by
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : BoundaryProfile => K i) J :=
    (ContinuousLinearMap.proj i : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
  have hdot {f g : BoundaryProfile → Vec}
      (hf : ContDiffAt ℝ ∞ f J) (hg : ContDiffAt ℝ ∞ g J) :
      ContDiffAt ℝ ∞ (fun K => f K ⬝ᵥ g K) J :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hf i).mul (contDiffAt_pi.mp hg i))
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (hdot (contDiffAt_profileNormalPart hJ.1)
      (contDiffAt_profileNormalPart hJ.1)).sqrt (dot_self_pos hJ.2).ne'
  · exact hdot (hslot 3) (contDiffAt_profilePreferred hJ)
  · exact hdot (hslot 3) (contDiffAt_profileComplement hJ)
  · exact hdot (hslot 4) (contDiffAt_profileComplement hJ)

lemma contDiffAt_profileGeometry {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileGeometry J :=
  ((contDiffAt_profilePreferred hJ).prodMk (contDiffAt_profileComplement hJ)).prodMk
    (contDiffAt_profileCoefficients hJ)

/-- Uniformly transfer all five derivative estimates to the actual normal
frame and its scaled coefficients on a compact family of regular profiles. -/
theorem compact_boundary_profile_stability {K : Set BoundaryProfile}
    (hK : IsCompact K) (hregular : K ⊆ regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ H : BoundaryProfile,
      ‖H-J‖ < δ → H ∈ regularBoundaryProfiles ∧
        ‖profileGeometry H-profileGeometry J‖ < ε := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open
    isOpen_regularBoundaryProfiles hregular
  have hc : ContinuousOn profileGeometry (Metric.cthickening r K) :=
    fun J hJ => (contDiffAt_profileGeometry (hsub hJ)).continuousAt.continuousWithinAt
  have hu := hK.cthickening.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro J hJ H hHJ
  have hH : H ∈ Metric.cthickening r K :=
    Metric.thickening_subset_cthickening r K
      (Metric.mem_thickening_iff.mpr ⟨J,hJ,by
        simpa only [dist_eq_norm] using hHJ.trans_le (min_le_left r d)⟩)
  refine ⟨hsub hH,?_⟩
  have hJ' : J ∈ Metric.cthickening r K := Metric.self_subset_cthickening K hJ
  simpa only [dist_eq_norm] using hclose H hH J hJ'
    (by simpa only [dist_eq_norm] using hHJ.trans_le (min_le_right r d))

end ClosedSurfaceR4.GeometryPreservation

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

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFamilyProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
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

lemma circularFamilyProfile_smoothOn {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U : Set E} {α : E × ℝ → ℝ} (hU : IsOpen U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hα : ContDiffOn ℝ ∞ α (U ×ˢ univ))
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0) (d : E) :
    ContDiffOn ℝ ∞ (circularFamilyProfile Q X Y C R e₁ e₂ α d) (U ×ˢ univ) := by
  have hX' : ContDiffOn ℝ ∞ (fun z : E × ℝ => X z.1) (U ×ˢ univ) := hX.comp contDiffOn_fst (fun z hz => hz.1)
  have hY' : ContDiffOn ℝ ∞ (fun z : E × ℝ => Y z.1) (U ×ˢ univ) := hY.comp contDiffOn_fst (fun z hz => hz.1)
  have hC' : ContDiffOn ℝ ∞ (fun z : E × ℝ => C z.1) (U ×ˢ univ) := hC.comp contDiffOn_fst (fun z hz => hz.1)
  have hR' : ContDiffOn ℝ ∞ (fun z : E × ℝ => R z.1) (U ×ˢ univ) := hR.comp contDiffOn_fst (fun z hz => hz.1)
  have h1' : ContDiffOn ℝ ∞ (fun z : E × ℝ => e₁ z.1) (U ×ˢ univ) := h₁.comp contDiffOn_fst (fun z hz => hz.1)
  have h2' : ContDiffOn ℝ ∞ (fun z : E × ℝ => e₂ z.1) (U ×ˢ univ) := h₂.comp contDiffOn_fst (fun z hz => hz.1)
  have hV : ContDiffOn ℝ ∞ (fun z : E × ℝ =>
      R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) (U ×ˢ univ) :=
    hR'.smul ((hα.cos.smul h1').add (hα.sin.smul h2'))
  have hW := ((hQ.comp contDiffOn_fst (fun z hz => hz.1)).add hV).fderiv_of_isOpen
    (hU.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hβ := hα.fderiv_of_isOpen (hU.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hn : ContDiffOn ℝ ∞ (fun z : E × ℝ => realNormalPart (Y z.1) (C z.1) (X z.1))
      (U ×ˢ univ) := by
    intro z hz
    exact (contDiffAt_realNormalPart
      (hY'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hC'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hX'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)) (hD z.1 hz.1)).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hX'.sub hn).add hV
  · exact hY'
  · exact hC'
  · exact hW.clm_apply contDiffOn_const
  · exact (hR'.mul (hβ.clm_apply contDiffOn_const)).smul
      (((hα.sin.neg).smul h1').add (hα.cos.smul h2'))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFrozenCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first two canonical coefficients depend on the angle value and
fixed geometric data; no derivative of the chosen angle remains. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circularFamilyProfile_frozen_coefficients {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α (x,t))
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (d : E) :
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 0 =
      frozenSize X Y C R e₁ e₂ (x,α (x,t)) ∧
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 1 =
      frozenFirst Q X Y C R e₁ e₂ d (x,α (x,t)) := by
  rw [circularFamilyProfile_spatial hQ hR h₁ h₂ hα d]
  refine ⟨rfl,?_⟩
  exact circularSpatialProfile_first _ hQ hR h₁ h₂
    (hα.comp x (differentiableAt_id.prodMk (differentiableAt_const t))) hframe

end ClosedSurfaceR4.GeometryPreservation

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

lemma jetAcceleration_decomposition (j : GeometricJet) :
    j.2 4 = (jetAccelerationCoefficients j).1 • j.2 0 +
      (jetAccelerationCoefficients j).2 • j.2 1 + jetSecondNormal j := by
  unfold jetAccelerationCoefficients jetSecondNormal realNormalPart jetTangentGram
  abel

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetDomain
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SurfaceCircularSmooth
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual circular surface profile on the selected
jet neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

lemma surfaceCircularProfile_smoothOn {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} {Ω Z : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hZΩ : (Z : Set GeometricJet) ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ)) :
    ContDiffOn ℝ ∞ (surfaceCircularProfile F a e₁ e₂ α)
      ((CollarVelocity.jetSection F ⁻¹' Z) ×ˢ univ) := by
  let V : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hσ := CollarVelocity.jetSection_smooth hF
  have hV : IsOpen V := Z.isOpen.preimage hσ.continuous
  have hmaps : MapsTo (CollarVelocity.jetSection F) V Ω := fun _ hx => hZΩ hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ (hZΩ hx)).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (CollarVelocity.jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (CollarVelocity.jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ (hZΩ hx)).2
  have hR := velocityRadius_smoothOn hv ha.contDiffOn hnonzero
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hc := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (V ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  exact circularFamilyProfile_smoothOn hV (hx.sub hv) hx hy hc hR
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hα' hD dy

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingComponents
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar identities used in the later-curve crossing calculation. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma pure_first_identity {S D N L k b c : ℝ} (hS : S ≠ 0) :
    S*(pureComponents S D N L k b c).1 = (D*b+S*c)^2+(k+N^2)*b^2 := by
  dsimp [pureComponents,frameXX,frameXY,frameYY]
  field_simp <;> ring

lemma pure_unit_slope {S D N L k t : ℝ} (hS : S ≠ 0) :
    pureComponents S D N L k 1 t = slopePure S D N L k t := by
  ext <;> dsimp [pureComponents,frameXX,frameXY,frameYY,slopePure] <;> field_simp <;> ring

lemma mixed_sub_left {S D N L k t u : ℝ} (hS : S ≠ 0) :
    slopeMixed S D N L k t u-slopePure S D N L k t =
      (u-t) • (D+S*t,N) := by
  ext <;> dsimp [slopeMixed,slopePure] <;> field_simp <;> ring

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingProjectionBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered mixed projection is bounded independently of the unbounded
longitudinal second-form component. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixed_projection_lower {P Z : E} (hP : P ≠ 0) :
    ‖P‖-‖Z-P‖ ≤ inner ℝ Z (‖P‖⁻¹ • P) := by
  have hp : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hi : -‖Z-P‖*‖P‖ ≤ inner ℝ (Z-P) P := by
    have h := (neg_abs_le (inner ℝ (Z-P) P)).trans' (neg_le_neg (abs_real_inner_le_norm (Z-P) P))
    simpa only [neg_mul] using h
  have he : inner ℝ Z P = inner ℝ (Z-P) P+‖P‖^2 := by
    rw [inner_sub_left,real_inner_self_eq_norm_sq]
    ring
  rw [real_inner_smul_right,he]
  calc
    ‖P‖-‖Z-P‖ = (‖P‖^2-‖Z-P‖*‖P‖)/‖P‖ := by field_simp
    _ ≤ (inner ℝ (Z-P) P+‖P‖^2)/‖P‖ :=
      div_le_div_of_nonneg_right (by linarith) hp.le
    _ = ‖P‖⁻¹*(inner ℝ (Z-P) P+‖P‖^2) := by ring

lemma frameVector_sub (n m : E) (v w : ℝ × ℝ) :
    frameVector n m (v-w) = frameVector n m v-frameVector n m w := by
  simp only [frameVector,Prod.fst_sub,Prod.snd_sub,sub_smul]
  abel

lemma frameVector_smul (n m : E) (a : ℝ) (v : ℝ × ℝ) :
    frameVector n m (a • v) = a • frameVector n m v := by
  simp only [frameVector,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,smul_add,smul_smul]

lemma frameVector_norm_le {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (v : ℝ × ℝ) :
    ‖frameVector n m v‖ ≤ |v.1|+|v.2| := by
  simpa only [frameVector,norm_smul,Real.norm_eq_abs,hn,hm,mul_one] using
    norm_add_le (v.1 • n) (v.2 • m)

lemma frameVector_inner_first {n m : E} (hn : ‖n‖ = 1) (hmn : inner ℝ m n = 0)
    (v : ℝ × ℝ) : inner ℝ (frameVector n m v) n = v.1 := by
  simp only [frameVector,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    hn,one_pow,hmn,mul_one,mul_zero,add_zero]

theorem crossing_projection_lower {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hmn : inner ℝ m n = 0) {S D N L k t u : ℝ} (hS : S ≠ 0)
    (hp : 0 < (slopePure S D N L k t).1) :
    (slopePure S D N L k t).1-|u-t| *(|D+S*t|+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have hip : inner ℝ P n = (slopePure S D N L k t).1 := frameVector_inner_first hn hmn _
  have hP : P ≠ 0 := by
    intro h
    rw [h,inner_zero_left] at hip
    linarith
  have hPn : (slopePure S D N L k t).1 ≤ ‖P‖ := by
    rw [← hip]
    simpa only [hn,mul_one] using real_inner_le_norm P n
  have he : Z-P = (u-t) • frameVector n m (D+S*t,N) := by
    change frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t) = _
    rw [← frameVector_sub,mixed_sub_left hS,frameVector_smul]
  have hdiff : ‖Z-P‖ ≤ |u-t| *(|D+S*t|+|N|) := by
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)
  exact (sub_le_sub hPn hdiff).trans (mixed_projection_lower hP)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformCrossingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform crossing estimates with no dependence on the longitudinal
second-form coefficient. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma crossing_first_lower {S D N L k t sLo sHi K : ℝ}
    (hmin : 0 < sLo) (hSmin : sLo ≤ S) (hSmax : S ≤ sHi) (hK : 0 ≤ K) (hk : -K ≤ k) :
    N^2/sHi-K/sLo ≤ (slopePure S D N L k t).1 := by
  have hS : 0 < S := hmin.trans_le hSmin
  have hN := div_le_div_of_nonneg_left (sq_nonneg N) hS hSmax
  have hK' := div_le_div_of_nonneg_left hK hmin hSmin
  have hk' := div_le_div_of_nonneg_right hk hS.le
  have hsquare := div_nonneg (sq_nonneg (D+S*t)) hS.le
  change _ ≤ (N^2+k+(D+S*t)^2)/S
  rw [add_div,add_div]
  rw [neg_div] at hk'
  linarith

lemma crossing_slope_bound {S D N t u sHi d T : ℝ}
    (hS : 0 ≤ S) (hSmax : S ≤ sHi) (hd : |D| ≤ d)
    (ht : |t| ≤ T) (hu : |u| ≤ T) :
    |u-t| * (|D+S*t|+|N|) ≤ 2*T*(d+sHi*T+|N|) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hsHi : 0 ≤ sHi := hS.trans hSmax
  have hdiff : |u-t| ≤ 2*T := by
    have hh := (abs_sub u t).trans (add_le_add hu ht)
    linarith
  have hlinear : |D+S*t| ≤ d+sHi*T := by
    calc
      |D+S*t| ≤ |D|+|S*t| := abs_add_le _ _
      _ = |D|+S*|t| := by rw [abs_mul,abs_of_nonneg hS]
      _ ≤ d+sHi*T := add_le_add hd (mul_le_mul hSmax ht (abs_nonneg _) hsHi)
  exact mul_le_mul hdiff (add_le_add hlinear le_rfl) (by positivity) (by positivity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_crossing_projection_lower {n m : E}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {S D N L k t u sLo sHi K d T : ℝ}
    (hmin : 0 < sLo) (hSmin : sLo ≤ S) (hSmax : S ≤ sHi)
    (hK : 0 ≤ K) (hk : -K ≤ k) (hd : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T)
    (hlarge : K/sLo < N^2/sHi) :
    0 < (slopePure S D N L k t).1 ∧
    N^2/sHi-K/sLo-2*T*(d+sHi*T+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  have hfirst := crossing_first_lower (N := N) (D := D) (L := L) (t := t) hmin hSmin hSmax hK hk
  have hpos : 0 < (slopePure S D N L k t).1 := by linarith
  refine ⟨hpos,?_⟩
  have hbound := crossing_slope_bound (N := N) (hmin.le.trans hSmin) hSmax hd ht hu
  exact (sub_le_sub hfirst hbound).trans
    (crossing_projection_lower hn hm hmn (hmin.trans_le hSmin).ne' hpos)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the crossing threshold before the longitudinal curvature term. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma quadratic_dominates_linear (A P Q R : ℝ)
    (hA : 0 < A) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ N : ℝ, H < |N| → R < N^2/A-Q-P*|N| := by
  let H := max 1 (A*(P+Q+R+1))
  refine ⟨H,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro N hN
  have hx1 : 1 < |N| := (le_max_left _ _).trans_lt hN
  have hx : 0 < |N| := zero_lt_one.trans hx1
  have hlin : A*(P+Q+R+1) < |N| := (le_max_right _ _).trans_lt hN
  have hdiv : P+Q+R+1 < |N|/A := (lt_div_iff₀ hA).mpr (by simpa only [mul_comm] using hlin)
  have hmul := mul_lt_mul_of_pos_right hdiv hx
  have hsq : |N|/A*|N| = N^2/A := by rw [div_mul_eq_mul_div,← sq, sq_abs]
  rw [hsq] at hmul
  have hsmall : P*|N|+Q+R < (P+Q+R+1)*|N| := by
    nlinarith [mul_nonneg (add_nonneg hQ hR) (sub_nonneg.mpr hx1.le)]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_crossing_threshold (sLo sHi K d T R : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → H < |N| →
      0 < (slopePure S D N L k t).1 ∧
      R < inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let Q := K/sLo+2*T*(d+sHi*T)
  have hQ : 0 ≤ Q := by dsimp [Q] <;> positivity
  obtain ⟨H,hH,hh⟩ := quadratic_dominates_linear sHi (2*T) Q R hmax hQ hR
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  have hlarge := hh N hN
  have he : N^2/sHi-Q-(2*T)*|N| = N^2/sHi-K/sLo-2*T*(d+sHi*T+|N|) := by
    dsimp [Q] <;> ring
  rw [he] at hlarge
  have htail : 0 ≤ 2*T*(d+sHi*T+|N|) := by positivity
  have hfirst : K/sLo < N^2/sHi := by linarith
  obtain ⟨hp,hbound⟩ := uniform_crossing_projection_lower hn hm hmn
    hmin hSmin hSmax hK hk hDb htb hub hfirst
  exact ⟨hp,hlarge.trans_le hbound⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingInvariantThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite threshold gives both ordered crossing inequalities. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma crossing_positive_of_projection {K T k t u p : ℝ}
    (hK : 0 ≤ K) (hk : -K ≤ k) (ht : |t| ≤ T) (hu : |u| ≤ T)
    (hp : Real.sqrt (K*(2*T)^2)+1 < p) : 0 < p^2+k*(t-u)^2 := by
  have hab : |t-u| ≤ 2*T := by
    have hh := (abs_sub t u).trans (add_le_add ht hu)
    linarith
  have hsq : (t-u)^2 ≤ (2*T)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t-u)) hab 2
  have hcurv : -K*(2*T)^2 ≤ k*(t-u)^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hsq hK
    have h₂ := mul_le_mul_of_nonneg_right hk (sq_nonneg (t-u))
    nlinarith
  have hs := Real.sq_sqrt (mul_nonneg hK (sq_nonneg (2*T)))
  have hs0 := Real.sqrt_nonneg (K*(2*T)^2)
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ordered_crossing_threshold (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → H < |N| →
      0 < (slopePure S D N L k t).1 ∧ 0 < (slopePure S D N L k u).1 ∧
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  let R := Real.sqrt (K*(2*T)^2)+1
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  obtain ⟨H,hH,hh⟩ := uniform_crossing_threshold (E := E) sLo sHi K d T R hmin hmax hK hd hT hR
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  obtain ⟨hpt,hqt⟩ := hh n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  obtain ⟨hpu,hqu⟩ := hh n m hn hm hmn S D N L k u t hSmin hSmax hk hDb hub htb hN
  exact ⟨hpt,hpu,crossing_positive_of_projection hK hk htb hub hqt,
    crossing_positive_of_projection hK hk hub htb hqu⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LongitudinalCrossing
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from angular turns, the large longitudinal component alone gives
both ordered crossing inequalities. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma frameVector_inner_second {n m : E} (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    (v : ℝ × ℝ) : inner ℝ (frameVector n m v) m = v.2 := by
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  simp only [frameVector,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    hm,one_pow,hnm,mul_one,mul_zero,zero_add]

lemma crossing_projection_of_nonzero {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u : ℝ} (hS : S ≠ 0)
    (hP : frameVector n m (slopePure S D N L k t) ≠ 0) :
    ‖frameVector n m (slopePure S D N L k t)‖-|u-t| * (|D+S*t|+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have he : Z-P = (u-t) • frameVector n m (D+S*t,N) := by
    change frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t) = _
    rw [← frameVector_sub,mixed_sub_left hS,frameVector_smul]
  have hdiff : ‖Z-P‖ ≤ |u-t| * (|D+S*t|+|N|) := by
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)
  exact (sub_le_sub_left hdiff ‖P‖).trans (mixed_projection_lower hP)

lemma longitudinal_norm_lower {n m : E} (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {S D N L k t B T : ℝ} (hB : 0 ≤ B) (hN : |N| ≤ B) (ht : |t| ≤ T) :
    |L|-2*B*T ≤ ‖frameVector n m (slopePure S D N L k t)‖ := by
  let P := frameVector n m (slopePure S D N L k t)
  have hi : inner ℝ P m = L+2*N*t := frameVector_inner_second hm hmn _
  have hnorm : |L+2*N*t| ≤ ‖P‖ := by
    rw [← hi]
    simpa only [hm,mul_one] using abs_real_inner_le_norm P m
  have hadd := abs_sub (L+2*N*t) (2*N*t)
  have hNt : |2*N*t| ≤ 2*B*T := by
    simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht (abs_nonneg _) (by positivity)
  simp only [add_sub_cancel_right] at hadd
  linarith

theorem longitudinal_projection_threshold (sHi d B T R : ℝ)
    (hsHi : 0 ≤ sHi) (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → H < |L| →
      R < inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let H := R+2*T*(d+sHi*T+2*B)+1
  have hH : 0 < H := by dsimp [H] <;> positivity
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hS hSmax hDb hNb htb hub hL
  have hp := longitudinal_norm_lower (S := S) (D := D) (L := L) (k := k) hm hmn hB hNb htb
  have hP : frameVector n m (slopePure S D N L k t) ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hp
    have hrest : 0 ≤ 2*T*(d+sHi*T) := by positivity
    dsimp [H] at hL
    nlinarith
  have hdiff := crossing_slope_bound hS.le hSmax hDb htb hub (N := N)
  have hbd : |u-t| * (|D+S*t|+|N|) ≤ 2*T*(d+sHi*T+B) :=
    hdiff.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hNb) (by positivity))
  have hproj := crossing_projection_of_nonzero hn hm hS.ne' hP (u := u)
  dsimp [H] at hL
  nlinarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CompactTurnDichotomy
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness converts the two limiting mechanisms at turns and away from
turns into a single small-scale alternative. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation

lemma compact_away_from_turns {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A N₀ : X → ℝ}
    (hA : Continuous A) (hN₀ : Continuous N₀) (H : ℝ)
    (hturn : ∀ x ∈ K, A x = 0 → H+2 < |N₀ x|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, |N₀ x| ≤ H+1 → δ ≤ |A x| := by
  let C := K ∩ {x | |N₀ x| ≤ H+1}
  have hC : IsCompact C := hK.inter_right (isClosed_le hN₀.abs continuous_const)
  by_cases hne : C.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hC.exists_isMinOn hne hA.abs.continuousOn
    have hp : 0 < |A x| := by
      apply abs_pos.mpr
      intro hz
      have hh := hturn x hx.1 hz
      have hxN : |N₀ x| ≤ H+1 := hx.2
      linarith
    exact ⟨|A x|,hp,fun y hy hn => hmin ⟨hy,hn⟩⟩
  · refine ⟨1,by norm_num,?_⟩
    intro x hx hn
    exact False.elim (hne ⟨x,hx,hn⟩)

theorem small_scale_turn_or_longitudinal {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A N₀ : X → ℝ}
    (hA : Continuous A) (hN₀ : Continuous N₀) (H J : ℝ) (hJ : 0 ≤ J)
    (hturn : ∀ x ∈ K, A x = 0 → H+2 < |N₀ x|) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ x ∈ K, ∀ N L : ℝ, |N-N₀ x| < 1 → |z*L-A x| < η →
        H < |N| ∨ J < |L| := by
  obtain ⟨δ,hδ,haway⟩ := compact_away_from_turns hK hA hN₀ H hturn
  let η := δ/(2*(J+1))
  have hη : 0 < η := div_pos hδ (by positivity)
  have heq : η*(J+1) = δ/2 := by
    dsimp [η]
    field_simp
  refine ⟨η,hη,?_⟩
  intro z hz hzη x hx N L hN hL
  by_cases hn : H < |N|
  · exact Or.inl hn
  · right
    by_contra hl
    have hn' : |N| ≤ H := le_of_not_gt hn
    have hl' : |L| ≤ J := le_of_not_gt hl
    have hn₀ : |N₀ x| ≤ H+1 := by
      have hh := abs_sub_le (N₀ x) N 0
      simp only [sub_zero,abs_sub_comm] at hh
      linarith
    have ha := haway x hx hn₀
    have hb : |A x| ≤ |z*L-A x|+z*|L| := by
      have hh := abs_sub_le (A x) (z*L) 0
      simpa only [sub_zero,abs_sub_comm,abs_mul,abs_of_pos hz] using hh
    have hmul := mul_le_mul_of_nonneg_left hl' hz.le
    have hmul' := mul_le_mul_of_nonneg_right hzη.le hJ
    nlinarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_TwoMechanismCrossing
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The turn threshold is fixed before any bound on the loop's transverse
coefficient.  The longitudinal threshold is allowed to depend on that bound. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem longitudinal_ordered_crossing_threshold (sHi K d B T : ℝ)
    (hsHi : 0 ≤ sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ J : ℝ, 0 < J ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → -K ≤ k → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → J < |L| →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  let R := Real.sqrt (K*(2*T)^2)+1
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  obtain ⟨J,hJ,hproj⟩ := longitudinal_projection_threshold
    (E := E) sHi d B T R hsHi hd hB hT hR
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hS hSmax hk hD hN ht hu hL
  exact ⟨crossing_positive_of_projection hK hk ht hu
      (hproj n m hn hm hmn S D N L k t u hS hSmax hD hN ht hu hL),
    crossing_positive_of_projection hK hk hu ht
      (hproj n m hn hm hmn S D N L k u t hS hSmax hD hN hu ht hL)⟩

theorem two_mechanism_crossing_threshold (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ B : ℝ, 0 ≤ B → ∃ J : ℝ, 0 < J ∧
    ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → (H < |N| ∨ J < |L|) →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  obtain ⟨H,hH,hturn⟩ := ordered_crossing_threshold (E := E) sLo sHi K d T
    hmin hmax hK hd hT
  refine ⟨H,hH,?_⟩
  intro B hB
  obtain ⟨J,hJ,hlong⟩ := longitudinal_ordered_crossing_threshold (E := E)
    sHi K d B T hmax.le hK hd hB hT
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hD hN ht hu halt
  rcases halt with hlargeN | hlargeL
  · exact (hturn n m hn hm hmn S D N L k t u hSmin hSmax hk hD ht hu hlargeN).2.2
  · exact hlong n m hn hm hmn S D N L k t u (hmin.trans_le hSmin)
      hSmax hk hD hN ht hu hlargeL

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CompactCrossingPreservation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform positivity at the later crossings from the actual two second-form
limits.  Only the limiting angular speed and mixed component enter compactness. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem compact_crossing_preservation (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ (C : Set X), IsCompact C →
    ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
    (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
    ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → |N-N₀ x| < η → |z*L-A x| < η →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  obtain ⟨H,hH,hthreshold⟩ := two_mechanism_crossing_threshold (E := E)
    sLo sHi K d T hmin hmax hK hd hT
  refine ⟨H,hH,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B
  have hB₀ : 0 ≤ B₀ := le_max_left _ _
  have hbound : ∀ x ∈ C, |N₀ x| ≤ B₀ := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  obtain ⟨J,hJ,hcross⟩ := hthreshold (B₀+1) (by positivity)
  obtain ⟨η₀,hη₀,hdichotomy⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min (by norm_num) hη₀,?_⟩
  intro z hz hzη x hx n m hn hm hmn S D N L k t u hSmin hSmax hk hD ht hu hN hL
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀+1 := by
    have ha := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at ha
    linarith [hbound x hx]
  apply hcross n m hn hm hmn S D N L k t u hSmin hSmax hk hD hNbound ht hu
  exact hdichotomy z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
    (hL.trans_le (min_le_right _ _))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PureRayAvoidance
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative avoidance of the nonpositive first-axis ray for all nonzero
tangent directions, including directions whose first coordinate vanishes. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma slope_first_positive {S D N L k t K : ℝ} (hS : 0 < S)
    (hk : -K ≤ k) (hN : K < N^2) : 0 < (slopePure S D N L k t).1 := by
  change 0 < (N^2+k+(D+S*t)^2)/S
  exact div_pos (by nlinarith [sq_nonneg (D+S*t)]) hS

lemma slope_ray_avoidance_longitudinal {sLo S D N L k t K d B : ℝ}
    (hmin : 0 < sLo) (hS : sLo ≤ S) (hK : 0 ≤ K) (hk : -K ≤ k)
    (hd : |D| ≤ d) (hB : 0 ≤ B) (hN : |N| ≤ B)
    (hL : 2*B*((Real.sqrt K+d)/sLo) < |L|) :
    0 < (slopePure S D N L k t).1 ∨ (slopePure S D N L k t).2 ≠ 0 := by
  by_cases hp : 0 < (slopePure S D N L k t).1
  · exact Or.inl hp
  · right
    intro hz
    have hSpos : 0 < S := hmin.trans_le hS
    have hnum : N^2+k+(D+S*t)^2 ≤ 0 := by
      have hh : (N^2+k+(D+S*t)^2)/S ≤ 0 := le_of_not_gt hp
      simpa only [zero_mul] using (div_le_iff₀ hSpos).mp hh
    have hsq : (D+S*t)^2 ≤ K := by nlinarith [sq_nonneg N]
    have hsqrt := Real.sq_sqrt hK
    have habs : |D+S*t| ≤ Real.sqrt K := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      simpa only [sq_abs,hsqrt] using hsq
    have hSt : S*|t| ≤ Real.sqrt K+d := by
      have hh := abs_sub_le (D+S*t) 0 D
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,abs_mul,abs_of_pos hSpos] at hh
      linarith
    have ht : |t| ≤ (Real.sqrt K+d)/sLo := by
      apply (le_div_iff₀ hmin).mpr
      nlinarith [mul_le_mul_of_nonneg_right hS (abs_nonneg t)]
    have hLt : L = -(2*N*t) := by
      change L+2*N*t = 0 at hz
      linarith
    have hprod : |L| ≤ 2*B*((Real.sqrt K+d)/sLo) := by
      rw [hLt,abs_neg,abs_mul,abs_mul]
      norm_num only [show |(2 : ℝ)| = 2 by norm_num]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht
        (abs_nonneg _) (by positivity)
    linarith

lemma pure_slope_scale {S D N L k b t : ℝ} (hS : S ≠ 0) :
    pureComponents S D N L k b (b*t) = b^2 • slopePure S D N L k t := by
  ext <;> dsimp [pureComponents,frameXX,frameXY,frameYY,slopePure] <;>
    field_simp <;> ring

lemma pure_vertical_positive {S D N L k c : ℝ} (hS : 0 < S) (hc : c ≠ 0) :
    0 < (pureComponents S D N L k 0 c).1 := by
  have h := pure_first_identity (D := D) (N := N) (L := L) (k := k)
    (b := 0) (c := c) hS.ne'
  have hsq : 0 < (S*c)^2 := sq_pos_of_ne_zero (mul_ne_zero hS.ne' hc)
  simp only [mul_zero,zero_add,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] at h
  nlinarith

lemma pure_ray_avoidance_of_slopes {S D N L k b c : ℝ} (hS : 0 < S)
    (hv : b ≠ 0 ∨ c ≠ 0)
    (hslopes : ∀ t : ℝ, 0 < (slopePure S D N L k t).1 ∨
      (slopePure S D N L k t).2 ≠ 0) :
    0 < (pureComponents S D N L k b c).1 ∨
      (pureComponents S D N L k b c).2 ≠ 0 := by
  by_cases hb : b = 0
  · subst b
    exact Or.inl (pure_vertical_positive hS (hv.resolve_left (by simp)))
  · have hc : b*(c/b) = c := by field_simp
    rw [← hc,pure_slope_scale hS.ne']
    rcases hslopes (c/b) with hp | hz
    · exact Or.inl (mul_pos (sq_pos_of_ne_zero hb) hp)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 2 hb) hz)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCurveAvoidance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform nonvanishing and avoidance of the negative preferred normal on
compact curve pieces.  The collar case has an independent positive invariant. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation

lemma pure_first_positive_of_collar {S D N L k b c : ℝ} (hS : 0 < S)
    (hcollar : 0 < (D*b+S*c)^2+k*b^2) :
    0 < (pureComponents S D N L k b c).1 := by
  have hid := pure_first_identity (D := D) (N := N) (L := L) (k := k)
    (b := b) (c := c) hS.ne'
  nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg b)]

theorem compact_curve_avoidance {X : Type*} [TopologicalSpace X]
    (sLo K d : ℝ) (hmin : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ C : Set X, IsCompact C →
    ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
    (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
    ∀ S D N L k b c : ℝ, sLo ≤ S → -K ≤ k → |D| ≤ d →
      (b ≠ 0 ∨ c ≠ 0) → |N-N₀ x| < η → |z*L-A x| < η →
      0 < (pureComponents S D N L k b c).1 ∨
        (pureComponents S D N L k b c).2 ≠ 0 := by
  let H := K+2
  refine ⟨H,by dsimp [H] <;> positivity,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B+1
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀] <;> positivity
  have hbound : ∀ x ∈ C, |N₀ x| ≤ max 0 B := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  let J := 2*B₀*((Real.sqrt K+d)/sLo)+1
  have hJ : 0 < J := by dsimp [J] <;> positivity
  obtain ⟨η₀,hη₀,halt⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min (by norm_num) hη₀,?_⟩
  intro z hz hzη x hx S D N L k b c hS hk hD hv hN hL
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀ := by
    have hh := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at hh
    dsimp [B₀]
    linarith [hbound x hx]
  apply pure_ray_avoidance_of_slopes (hmin.trans_le hS) hv
  intro t
  rcases halt z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
      (hL.trans_le (min_le_right _ _)) with hlargeN | hlargeL
  · apply Or.inl
    apply slope_first_positive (hmin.trans_le hS) hk
    dsimp [H] at hlargeN
    nlinarith [sq_abs N,abs_nonneg N]
  · exact slope_ray_avoidance_longitudinal hmin hS hK hk hD hB₀ hNbound
      (by dsimp [J] at hlargeL <;> linarith)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondFormComponents
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the scalar normal-component calculations to the actual second
fundamental form and its Euclidean unit frame. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes

lemma spaceCoordinates_symm_inner (v w : RVec 4) :
    inner ℝ (spaceCoordinates.symm v) (spaceCoordinates.symm w) = v ⬝ᵥ w := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (spaceCoordinates_dot (spaceCoordinates.symm v) (spaceCoordinates.symm w)).symm

lemma spaceCoordinates_norm_unit {v : RVec 4} (hv : v ⬝ᵥ v = 1) :
    ‖spaceCoordinates.symm v‖ = 1 := by
  have h := spaceCoordinates_symm_inner v v
  rw [real_inner_self_eq_norm_sq,hv] at h
  nlinarith [norm_nonneg (spaceCoordinates.symm v)]

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma pure_components (hF : ContDiff ℝ ∞ F) (b c : ℝ) :
    realSecondForm F (b,c) (b,c) p =
      (pureComponents d.S d.D d.N d.L k b c).1 • d.n+
        (pureComponents d.S d.D d.N d.L k b c).2 • d.m := by
  rw [realSecondForm_bilinear hF]
  simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    d.xx,d.xy,d.yy]
  ext j
  simp only [pureComponents,frameXX,frameXY,frameYY,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma pure_space_components (hF : ContDiff ℝ ∞ F) (b c : ℝ) :
    spaceCoordinates.symm (realSecondForm F (b,c) (b,c) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (pureComponents d.S d.D d.N d.L k b c) := by
  rw [d.pure_components hF]
  simp only [map_add,map_smul,frameVector]

lemma slope_space_components (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    spaceCoordinates.symm (realSecondForm F (1,t) (1,t) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k t) := by
  rw [d.pure_space_components hF,pure_unit_slope d.size_pos.ne']

lemma mixed_space_components (hF : ContDiff ℝ ∞ F) (t u : ℝ) :
    spaceCoordinates.symm (realSecondForm F (1,t) (1,u) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopeMixed d.S d.D d.N d.L k t u) := by
  have hvec : realSecondForm F (1,t) (1,u) p =
      (slopeMixed d.S d.D d.N d.L k t u).1 • d.n+
        (slopeMixed d.S d.D d.N d.L k t u).2 • d.m := by
    rw [realSecondForm_bilinear hF]
    simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      d.xx,d.xy,d.yy]
    ext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,slopeMixed]
    field_simp [d.size_pos.ne']
    ring
  rw [hvec]
  simp only [map_add,map_smul,frameVector]

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualCrossingInvariant
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the actual ordered boundary invariant with the normal-coordinate
formula.  Euclidean normalization is preserved by the coordinate conversion. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes VelocityFrame

lemma spaceCoordinates_norm (v : RVec 4) :
    ‖spaceCoordinates.symm v‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [← spaceCoordinates_symm_inner,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

lemma spaceCoordinates_symm_normalize (v : RVec 4) :
    spaceCoordinates.symm (normalize v) = ‖spaceCoordinates.symm v‖⁻¹ • spaceCoordinates.symm v := by
  simp only [VelocityFrame.normalize,map_smul,spaceCoordinates_norm]

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma orderedCrossing_eq (hF : ContDiff ℝ ∞ F) (κ t u : ℝ)
    (hk : k = κ*NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) :
    orderedCrossing F (1,t) (1,u) p κ =
      modelOrderedCrossing (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        d.S d.D d.N d.L k t u := by
  have hg : NormalFrame.gramDet (coordDeriv (1,t) F p) (coordDeriv (1,u) F p) =
      (u-t)^2*NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F (1,t),coordDeriv_eq_basis F (1,u)]
    simpa only [one_mul,mul_one] using gramDet_change_basis (coordDeriv dx F p)
      (coordDeriv dy F p) 1 t 1 u
  unfold orderedCrossing
  rw [← spaceCoordinates_symm_inner,spaceCoordinates_symm_normalize,
    d.mixed_space_components hF,d.slope_space_components hF,hg]
  unfold modelOrderedCrossing
  congr 1
  rw [hk]
  ring

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ActualCurveAvoidance
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the componentwise ray exclusion into nonvanishing and non-antipodality
for the actual unit normal and second fundamental form. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes VelocityFrame

lemma frameVector_avoids_negative_axis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {v : ℝ × ℝ} (hv : 0 < v.1 ∨ v.2 ≠ 0) :
    frameVector n m v ≠ 0 ∧ ‖frameVector n m v‖⁻¹ • frameVector n m v ≠ -n := by
  let P := frameVector n m v
  have hfirst : inner ℝ P n = v.1 := frameVector_inner_first hn hmn v
  have hsecond : inner ℝ P m = v.2 := frameVector_inner_second hm hmn v
  have hP : P ≠ 0 := by
    intro hz
    rw [hz,inner_zero_left] at hfirst hsecond
    rcases hv with hp | hs
    · linarith
    · exact hs hsecond.symm
  refine ⟨hP,?_⟩
  intro heq
  have hscale : ‖P‖ • (‖P‖⁻¹ • P) = P := by
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hP),one_smul]
  have hPeq : P = (-‖P‖) • n := by
    rw [heq] at hscale
    simpa only [smul_neg,neg_smul] using hscale.symm
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  rw [hPeq,real_inner_smul_left,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at hfirst
  rw [hPeq,real_inner_smul_left,hnm,mul_zero] at hsecond
  rcases hv with hp | hs
  · linarith [norm_nonneg P]
  · exact hs hsecond.symm

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma actual_curve_avoidance (hF : ContDiff ℝ ∞ F) (b c : ℝ)
    (hcomp : 0 < (pureComponents d.S d.D d.N d.L k b c).1 ∨
      (pureComponents d.S d.D d.N d.L k b c).2 ≠ 0) :
    realSecondForm F (b,c) (b,c) p ≠ 0 ∧
      normalize (realSecondForm F (b,c) (b,c) p) ≠ -d.n := by
  have hmn : inner ℝ (spaceCoordinates.symm d.m) (spaceCoordinates.symm d.n) = 0 := by
    rw [spaceCoordinates_symm_inner, dotProduct_comm]
    exact d.orthogonal
  obtain ⟨hneq,hanti⟩ := frameVector_avoids_negative_axis
    (spaceCoordinates_norm_unit d.unit_n) (spaceCoordinates_norm_unit d.unit_m) hmn hcomp
  rw [← d.pure_space_components hF b c] at hneq hanti
  constructor
  · intro hz
    rw [hz,map_zero] at hneq
    exact hneq rfl
  · intro heq
    apply hanti
    have he := congrArg spaceCoordinates.symm heq
    simpa only [spaceCoordinates_symm_normalize,map_neg] using he

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryNormalMatch
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a boundary where the velocity correction vanishes on the exterior,
the limiting first normal coefficient and normal length are the old ones. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma leadingNormal_at_projection (X Y C : Vec) :
    leadingNormal X Y C (realNormalPart Y C X) = realNormalPart X Y C := by
  simp only [leadingNormal, leadingTangent, sub_add_cancel]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ZeroAmplitudeJet
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At zero amplitude the radial velocity has the original value and
first derivative, without an extra exterior-neighborhood hypothesis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma velocityRadius_normalize_jet {v : E → Vec} {a : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ ∞ v x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : v x ≠ 0) (hax : a x = 0) :
    velocityRadius (v x) (a x) • normalize (v x) = v x ∧
      fderiv ℝ (fun y => velocityRadius (v y) (a y) • normalize (v y)) x = fderiv ℝ v x := by
  have hs : ContDiffAt ℝ ∞ (fun y => v y ⬝ᵥ v y) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have ha2 : HasFDerivAt (fun y => a y^2) (0 : E →L[ℝ] ℝ) x := by
    simpa [hax] using (ha.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.pow 2
  have hspos : 0 < v x ⬝ᵥ v x := dot_self_pos hn
  have hrad := (hs.differentiableAt (by simp)).hasFDerivAt.add ha2
  have hrad' := hrad.sqrt (by simpa [hax] using hspos.ne')
  have hnorm := (hs.differentiableAt (by simp)).hasFDerivAt.sqrt hspos.ne'
  have hunit := (normalize_smoothAt hv hn).differentiableAt (by simp)
  constructor
  · simpa only [velocityRadius,hax,zero_pow (by decide : 2 ≠ 0),add_zero] using norm_smul_normalize hn
  · have hsame : fderiv ℝ (fun y => velocityRadius (v y) (a y) • normalize (v y)) x =
        fderiv ℝ (fun y => Real.sqrt (v y ⬝ᵥ v y) • normalize (v y)) x := by
      change fderiv ℝ ((fun y => velocityRadius (v y) (a y)) • (fun y => normalize (v y))) x =
        fderiv ℝ ((fun y => Real.sqrt (v y ⬝ᵥ v y)) • (fun y => normalize (v y))) x
      calc
        _ = _ := (hrad'.smul hunit.hasFDerivAt).fderiv
        _ = _ := by
          simpa [hax,velocityRadius] using (hnorm.smul hunit.hasFDerivAt).fderiv.symm
    have he : (fun y => Real.sqrt (v y ⬝ᵥ v y) • normalize (v y)) =ᶠ[𝓝 x] v := by
      filter_upwards [hv.continuousAt.eventually_ne hn] with y hy
      exact norm_smul_normalize hy
    exact hsame.trans he.fderiv_eq

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ZeroAmplitudeBoundary
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frozen boundary coefficients at zero amplitude are the old mixed
second derivative and old pure normal length. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma zero_amplitude_boundary_coefficients {X Y C v e₁ e₂ : E → Vec} {a : E → ℝ} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hv : ContDiffAt ℝ ∞ v x) (ha : ContDiffAt ℝ ∞ a x)
    (h₁ : ContDiffAt ℝ ∞ e₁ x) (h₂ : ContDiffAt ℝ ∞ e₂ x)
    (hn : v x ≠ 0) (hax : a x = 0)
    (he₁ : e₁ =ᶠ[𝓝 x] fun y => normalize (v y))
    (hproj : v x = realNormalPart (Y x) (C x) (X x))
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (d : E) :
    frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d (x,0) =
      fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x)) ∧
    frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ (x,0) =
      Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ realNormalPart (X x) (Y x) (C x)) := by
  let R := fun y => velocityRadius (v y) (a y)
  have hs : ContDiffAt ℝ ∞ (fun y => v y ⬝ᵥ v y) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hR : ContDiffAt ℝ ∞ R x := (hs.add (ha.pow 2)).sqrt (by
    simpa [hax] using (dot_self_pos hn).ne')
  have hjet := velocityRadius_normalize_jet hv ha hn hax
  have hV : R x • direction (e₁ x) (e₂ x) 0 = realNormalPart (Y x) (C x) (X x) := by
    simpa only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,
      he₁.eq_of_nhds,← hproj] using hjet.1
  have hsmall : (fun y => R y • e₁ y) =ᶠ[𝓝 x] (fun y => R y • normalize (v y)) := by
    filter_upwards [he₁] with y hy
    rw [hy]
  have hd : fderiv ℝ (fun y => R y • e₁ y) x = fderiv ℝ v x :=
    hsmall.fderiv_eq.trans hjet.2
  have hT : fderiv ℝ (fun y => X y-v y + R y • direction (e₁ y) (e₂ y) 0) x = fderiv ℝ X x := by
    simp only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
    rw [fderiv_fun_add (f := fun y => X y-v y) (g := fun y => R y • e₁ y) ((hX.sub hv).differentiableAt (by simp))
      ((hR.smul h₁).differentiableAt (by simp)),
      fderiv_fun_sub (hX.differentiableAt (by simp)) (hv.differentiableAt (by simp)),hd,sub_add_cancel]
  have hN : frozenNormal X Y C R e₁ e₂ (x,0) =
      normalize (realNormalPart (X x) (Y x) (C x)) := by
    change normalize (leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV,leadingNormal_at_projection]
  constructor
  · have hf := actual_first_eq_frozen (Q := X-v) (X := X) (Y := Y) (C := C) (R := R)
      (e₁ := e₁) (e₂ := e₂) (α := fun _ => 0) (d := d)
      ((hX.sub hv).differentiableAt (by simp)) (hR.differentiableAt (by simp))
      (h₁.differentiableAt (by simp)) (h₂.differentiableAt (by simp)) (differentiableAt_const 0) hframe
    rw [← hf,hN]
    exact congrArg (fun A : E →L[ℝ] Vec => A d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x))) hT
  · change Real.sqrt (leadingNormal (X x) (Y x) (C x) _ ⬝ᵥ
      leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV,leadingNormal_at_projection]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactCollarPositivity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict inequalities on a compact curve set propagate to a collar,
uniformly in a compact angular parameter. -/
noncomputable section
open Set
open scoped Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E A : Type*} [TopologicalSpace E] [T2Space E]
  [TopologicalSpace A]

/-- The collar and allowed translation size are chosen before the eventual
angle translation function or its derivatives. -/
theorem compact_collar_positive_small_shift {K C Ω : Set E} {J : Set A}
    (hK : IsCompact K) (hC : IsClosed C) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hJ : IsCompact J) {F : E × (A × ℝ) → ℝ}
    (hF : ContinuousOn F (Ω ×ˢ univ))
    (hpos : ∀ x ∈ K ∩ C, ∀ t ∈ J, 0 < F (x, (t, 0))) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, ∀ h : ℝ, |h| < ε → 0 < F (x, (t, h)) := by
  let O : Set (E × (A × ℝ)) := (Ω ×ˢ univ) ∩ F ⁻¹' Ioi 0
  have hO : IsOpen O := hF.isOpen_inter_preimage (hΩ.prod isOpen_univ) isOpen_Ioi
  have hKC : IsCompact (K ∩ C) := hK.inter_right hC
  have hsub : (K ∩ C) ×ˢ (J ×ˢ ({0} : Set ℝ)) ⊆ O := by
    intro z hz
    have h0 : z.2.2 = 0 := hz.2.2
    refine ⟨⟨hKΩ hz.1.1, mem_univ _⟩, ?_⟩
    rw [show z = (z.1, (z.2.1, 0)) from Prod.ext rfl (Prod.ext rfl h0)]
    exact hpos z.1 hz.1 z.2.1 hz.2.1
  obtain ⟨N, V, hN, hV, hKN, hJV, hNV⟩ :=
    generalized_tube_lemma hKC (hJ.prod isCompact_singleton) hO hsub
  obtain ⟨A₀, I, _, hI, hJA, h0I, hAI⟩ :=
    generalized_tube_lemma hJ isCompact_singleton hV hJV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hI 0 (h0I (mem_singleton 0))
  let W := (K \ N)ᶜ
  refine ⟨W, (hK.isClosed.sdiff hN).isOpen_compl, ?_, ε, hε, ?_⟩
  · intro x hx hbad
    exact hbad.2 (hKN ⟨hbad.1, hx⟩)
  · intro x hx t ht h hh
    have hxN : x ∈ N := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    have hhI : h ∈ I := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hh)
    exact (hNV ⟨hxN, hAI ⟨hJA ht, hhI⟩⟩).2

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_BoundaryInvariantCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform collar positivity for the normal invariant used by later curves. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalInvariant_smoothOn {D S : E × ℝ → ℝ} {b c k : E → ℝ} {Ω : Set E}
    (hD : ContDiffOn ℝ ∞ D (Ω ×ˢ univ)) (hS : ContDiffOn ℝ ∞ S (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω) :
    ContDiffOn ℝ ∞ (normalInvariant D S b c k) (Ω ×ˢ univ) := by
  have hbf : ContDiffOn ℝ ∞ (fun z : E × ℝ => b z.1) (Ω ×ˢ univ) :=
    hb.comp contDiffOn_fst (fun z hz => hz.1)
  have hcf : ContDiffOn ℝ ∞ (fun z : E × ℝ => c z.1) (Ω ×ˢ univ) :=
    hc.comp contDiffOn_fst (fun z hz => hz.1)
  have hkf : ContDiffOn ℝ ∞ (fun z : E × ℝ => k z.1) (Ω ×ˢ univ) :=
    hk.comp contDiffOn_fst (fun z hz => hz.1)
  exact (((hD.mul hbf).add (hS.mul hcf)).pow 2).add (hkf.mul (hbf.pow 2))

theorem boundary_invariant_collar {K C Ω : Set E} {J : Set ℝ}
    (hK : IsCompact K) (hC : IsClosed C) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hJ : IsCompact J) {D S β : E × ℝ → ℝ} {b c k : E → ℝ}
    (hD : ContDiffOn ℝ ∞ D (Ω ×ˢ univ)) (hS : ContDiffOn ℝ ∞ S (Ω ×ˢ univ))
    (hβ : ContDiffOn ℝ ∞ β (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω)
    (hzero : ∀ x ∈ K ∩ C, ∀ t ∈ J, β (x, t) = 0)
    (hboundary : ∀ x ∈ K ∩ C, 0 < normalInvariant D S b c k (x, 0)) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, ∀ h : ℝ, |h| < ε →
        0 < normalInvariant D S b c k (x, β (x, t) + h) := by
  let A : Set (E × (ℝ × ℝ)) := Ω ×ˢ univ
  have hp : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => (z.1, z.2.1)) A :=
    contDiffOn_fst.prodMk (contDiffOn_fst.comp contDiffOn_snd (fun _ _ => mem_univ _))
  have hb' : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => β (z.1, z.2.1)) A :=
    hβ.comp hp (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hh : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => z.2.2) A :=
    contDiffOn_snd.comp contDiffOn_snd (fun _ _ => mem_univ _)
  have hshift : ContDiffOn ℝ ∞
      (fun z : E × (ℝ × ℝ) => (z.1, β (z.1, z.2.1) + z.2.2)) A :=
    contDiffOn_fst.prodMk (hb'.add hh)
  have hF : ContDiffOn ℝ ∞
      (fun z : E × (ℝ × ℝ) => normalInvariant D S b c k
        (z.1, β (z.1, z.2.1) + z.2.2)) A :=
    (normalInvariant_smoothOn hD hS hb hc hk).comp hshift
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  apply compact_collar_positive_small_shift hK hC hΩ hKΩ hJ hF.continuousOn
  intro x hx t ht
  simpa only [hzero x hx t ht, add_zero] using hboundary x hx

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ZeroAmplitudeCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old ordered boundary inequality gives one uniform small-angle collar
before any loop or large transverse derivative is chosen. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes CollarVelocity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_amplitude_invariant_collar {K C₀ Ω : Set E}
    (hK : IsCompact K) (hC₀ : IsClosed C₀) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {X Y C v e₁ e₂ : E → Vec} {a b c k : E → ℝ}
    (hX : ContDiffOn ℝ ∞ X Ω) (hY : ContDiffOn ℝ ∞ Y Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hv : ContDiffOn ℝ ∞ v Ω) (ha : ContDiffOn ℝ ∞ a Ω)
    (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω)
    (hD : ∀ x ∈ Ω, gramDet (Y x) (C x) ≠ 0)
    (hn : ∀ x ∈ Ω, v x ≠ 0 ∨ a x ≠ 0)
    (hproj : ∀ x ∈ Ω, v x = realNormalPart (Y x) (C x) (X x))
    (hframe : ∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hzero : ∀ x ∈ C₀, a x = 0)
    (hadapt : ∀ x ∈ K ∩ C₀, e₁ =ᶠ[𝓝 x] fun y => normalize (v y))
    (d : E)
    (hboundary : ∀ x ∈ K ∩ C₀,
      0 < ((fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x))) * b x +
        Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ
          realNormalPart (X x) (Y x) (C x)) * c x)^2 + k x * b x^2) :
    ∃ W : Set E, IsOpen W ∧ C₀ ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ θ : ℝ, |θ| < ε →
        0 < normalInvariant
          (frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
          (frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂) b c k (x,θ) := by
  have hR := velocityRadius_smoothOn hv ha hn
  obtain ⟨hfirst,hsize⟩ := frozen_coefficients_smoothOn hΩ (hX.sub hv) hX hY hC hR h₁ h₂
    hD hframe (fun x hx => (velocityRadius_pos (hn x hx)).ne') d
  have hbound : ∀ x ∈ K ∩ C₀, 0 < normalInvariant
      (frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
      (frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂) b c k (x,0) := by
    intro x hx
    have hxΩ := hKΩ hx.1
    have hxnb := hΩ.mem_nhds hxΩ
    have hn0 : v x ≠ 0 := (hn x hxΩ).resolve_right (not_not_intro (hzero x hx.2))
    obtain ⟨hf,hs⟩ := zero_amplitude_boundary_coefficients (hX.contDiffAt hxnb)
      (hv.contDiffAt hxnb) (ha.contDiffAt hxnb) (h₁.contDiffAt hxnb) (h₂.contDiffAt hxnb)
      hn0 (hzero x hx.2) (hadapt x hx) (hproj x hxΩ) (hframe x hxΩ) d
    change 0 < (_ * b x + _ * c x)^2 + k x * b x^2
    rw [hf,hs]
    exact hboundary x hx
  obtain ⟨W,hW,hCW,ε,hε,hcol⟩ := boundary_invariant_collar (J := {0})
    (D := frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
    (S := frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂)
    (β := fun _ => 0) hK hC₀ hΩ hKΩ (isCompact_singleton)
    hfirst hsize contDiffOn_const hb hc hk (fun _ _ _ _ => rfl) hbound
  refine ⟨W,hW,hCW,ε,hε,?_⟩
  intro x hx θ hθ
  simpa only [zero_add] using hcol x hx 0 (mem_singleton 0) θ hθ

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceBoundaryCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the zero-amplitude collar estimate to the actual immersion and
its preferred jet frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity

theorem surface_zero_amplitude_collar {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U K C₀ : Set Base} {Ω : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hK : IsCompact K) (hKΩ : jetSection F '' K ⊆ Ω) (hC₀ : IsClosed C₀)
    (hzero : ∀ x ∈ C₀, a x = 0)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    {B : Set GeometricJet} (hB : IsOpen B) (hCB : jetSection F '' C₀ ⊆ B)
    (hBadapt : ∀ j ∈ B, e₁ j = normalize (jetNormal j))
    {b c k : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b (jetSection F ⁻¹' Ω))
    (hc : ContDiffOn ℝ ∞ c (jetSection F ⁻¹' Ω))
    (hk : ContDiffOn ℝ ∞ k (jetSection F ⁻¹' Ω))
    (hboundary : ∀ x ∈ K ∩ C₀,
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x)) * b x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x) * c x)^2 + k x*b x^2) :
    ∃ W : Set Base, IsOpen W ∧ C₀ ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ θ : ℝ, |θ| < ε →
        0 < normalInvariant (surfaceFrozenFirst F a e₁ e₂) (surfaceFrozenSize F a e₁ e₂) b c k (x,θ) := by
  let V : Set Base := jetSection F ⁻¹' Ω
  have hσ := jetSection_smooth hF
  have hV : IsOpen V := Ω.isOpen.preimage hσ.continuous
  have hKV : K ⊆ V := fun x hx => hKΩ (mem_image_of_mem _ hx)
  have hmaps : MapsTo (jetSection F) V Ω := fun _ hx => hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ hx).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ hx).2
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hyy := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  apply zero_amplitude_invariant_collar hK hC₀ hV hKV hx hy hyy hv ha.contDiffOn
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hb hc hk hD hnonzero
    (fun _ _ => rfl) (fun x hx => hframe (jetSection F x) hx) hzero
  · intro x hxc
    filter_upwards [(hB.preimage hσ.continuous).mem_nhds (hCB (mem_image_of_mem _ hxc.2))] with y hy
    exact hBadapt _ hy
  · exact hboundary

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteScalarBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ClosedSurfaceR4

lemma finite_positive_lower {ι : Type*} [Finite ι] {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i by
    obtain ⟨δ,hδ,h⟩ := this Finset.univ
    exact ⟨δ,hδ,fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ,hδ,h⟩ := ih
    refine ⟨min (f i) δ,lt_min (hf i) hδ,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h j hj)

lemma finite_positive_upper {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ i, f i ≤ H := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ H : ℝ, 0 < H ∧ ∀ i ∈ s, f i ≤ H by
    obtain ⟨H,hH,h⟩ := this Finset.univ
    exact ⟨H,hH,fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨H,hH,h⟩ := ih
    refine ⟨max (f i) H,hH.trans_le (le_max_right _ _),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_max_left _ _
    · exact (h j hj).trans (le_max_right _ _)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LongitudinalNormalChoice
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from turns, the two pure normal directions have positive pairing and
lie in the same open half-plane.  This supplies the crossing normal path. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixed_difference_norm_bound {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u sHi d T : ℝ} (hS : 0 < S) (hShi : S ≤ sHi)
    (hD : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T) :
    ‖frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t)‖ ≤ 2*T*(d+sHi*T+|N|) := by
  rw [← frameVector_sub,mixed_sub_left hS.ne',frameVector_smul,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)).trans
    (crossing_slope_bound hS.le hShi hD ht hu)

lemma slopeMixed_symm (S D N L k t u : ℝ) :
    slopeMixed S D N L k t u = slopeMixed S D N L k u t := by
  ext <;> dsimp [slopeMixed] <;> ring

lemma pure_difference_norm_bound {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u sHi d T : ℝ} (hS : 0 < S) (hShi : S ≤ sHi)
    (hD : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T) :
    ‖frameVector n m (slopePure S D N L k u)-
      frameVector n m (slopePure S D N L k t)‖ ≤ 4*T*(d+sHi*T+|N|) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Q := frameVector n m (slopePure S D N L k u)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have hP : ‖Z-P‖ ≤ 2*T*(d+sHi*T+|N|) := mixed_difference_norm_bound hn hm hS hShi hD ht hu
  have hQ : ‖Z-Q‖ ≤ 2*T*(d+sHi*T+|N|) := by
    dsimp [Z,Q]
    rw [slopeMixed_symm]
    exact mixed_difference_norm_bound hn hm hS hShi hD hu ht
  have hsplit : Q-P = (Q-Z)+(Z-P) := by abel
  have hh := norm_add_le (Q-Z) (Z-P)
  rw [← hsplit,norm_sub_rev Q Z] at hh
  change ‖Q-P‖ ≤ _
  linarith

lemma inner_pos_of_difference_lt_norm {P Q : E} (h : ‖Q-P‖ < ‖P‖) :
    0 < inner ℝ P Q := by
  have hP : P ≠ 0 := by intro hz; rw [hz,norm_zero] at h; exact (not_lt_of_ge (norm_nonneg _) h)
  have hb := mixed_projection_lower (Z := Q) hP
  have hp : 0 < inner ℝ Q (‖P‖⁻¹ • P) := by linarith
  rw [real_inner_smul_right] at hp
  have hi : 0 < ‖P‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hP)
  rw [real_inner_comm]
  nlinarith

lemma double_product_bound {N t B T : ℝ} (hB : 0 ≤ B) (hN : |N| ≤ B) (ht : |t| ≤ T) :
    |2*N*t| ≤ 2*B*T := by
  simp only [abs_mul,show |(2 : ℝ)| = 2 by norm_num]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht
    (abs_nonneg _) (by positivity)

theorem longitudinal_normal_choice (sHi d B T : ℝ) (hsHi : 0 ≤ sHi)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ J : ℝ, 0 < J ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → J < |L| →
      let P := frameVector n m (slopePure S D N L k t)
      let Q := frameVector n m (slopePure S D N L k u)
      0 < inner ℝ P Q ∧ ∃ w : E, inner ℝ n w = 0 ∧ 0 < inner ℝ P w ∧ 0 < inner ℝ Q w := by
  let J := 2*B*T+4*T*(d+sHi*T+B)+1
  have hJ : 0 < J := by dsimp [J] <;> positivity
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hS hShi hD hN ht hu hL
  dsimp only
  let P := frameVector n m (slopePure S D N L k t)
  let Q := frameVector n m (slopePure S D N L k u)
  have hpn := longitudinal_norm_lower (S := S) (D := D) (N := N) (L := L) (k := k) hm hmn hB hN ht
  have hdiff := pure_difference_norm_bound (N := N) (L := L) (k := k) hn hm hS hShi hD ht hu
  have hdiff' : ‖Q-P‖ ≤ 4*T*(d+sHi*T+B) := hdiff.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hN) (by positivity))
  have hnear : ‖Q-P‖ < ‖P‖ := by dsimp [J] at hL <;> linarith
  refine ⟨inner_pos_of_difference_lt_norm hnear,?_⟩
  have htm : inner ℝ P m = L+2*N*t := frameVector_inner_second hm hmn _
  have hum : inner ℝ Q m = L+2*N*u := frameVector_inner_second hm hmn _
  have htb := abs_le.mp (double_product_bound hB hN ht)
  have hub := abs_le.mp (double_product_bound hB hN hu)
  have hbig : 2*B*T < |L| := by
    dsimp [J] at hL
    have hh : 0 ≤ 4*T*(d+sHi*T+B) := by positivity
    linarith
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  by_cases hL0 : 0 ≤ L
  · refine ⟨m,hnm,?_,?_⟩
    · change 0 < inner ℝ P m
      change inner ℝ P m = L+2*N*t at htm
      rw [abs_of_nonneg hL0] at hbig
      linarith
    · change 0 < inner ℝ Q m
      change inner ℝ Q m = L+2*N*u at hum
      rw [abs_of_nonneg hL0] at hbig
      linarith
  · refine ⟨-m,by simp [hnm],?_,?_⟩
    · change 0 < inner ℝ P (-m)
      change inner ℝ P m = L+2*N*t at htm
      rw [inner_neg_right]
      rw [abs_of_neg (lt_of_not_ge hL0)] at hbig
      linarith
    · change 0 < inner ℝ Q (-m)
      change inner ℝ Q m = L+2*N*u at hum
      rw [inner_neg_right]
      rw [abs_of_neg (lt_of_not_ge hL0)] at hbig
      linarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceFrozenCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the first two coefficients of the actual surface profiles with
those used to choose the boundary collar before the loop. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

lemma surfaceCircularProfile_frozen_coefficients {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} {Ω Z : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hZΩ : (Z : Set GeometricJet) ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    {x : Base} (hxZ : CollarVelocity.jetSection F x ∈ Z) (t : ℝ) :
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 0 =
      surfaceFrozenSize F a e₁ e₂ (x,α (CollarVelocity.jetSection F x,t)) ∧
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 1 =
      surfaceFrozenFirst F a e₁ e₂ (x,α (CollarVelocity.jetSection F x,t)) := by
  let V : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hσ := CollarVelocity.jetSection_smooth hF
  have hV : IsOpen V := Z.isOpen.preimage hσ.continuous
  have hmaps : MapsTo (CollarVelocity.jetSection F) V Ω := fun _ hx => hZΩ hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ (hZΩ hx)).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (CollarVelocity.jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (CollarVelocity.jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ (hZΩ hx)).2
  have hR := velocityRadius_smoothOn hv ha.contDiffOn hnonzero
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hc := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (V ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  have hnb := hV.mem_nhds hxZ
  exact circularFamilyProfile_frozen_coefficients
    (X := coordDeriv dx F) (Y := coordDeriv dy F) (C := coordDeriv dy (coordDeriv dy F))
    (((hx.sub hv).contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hR.contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (((h₁.comp hσ.contDiffOn hmaps).contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (((h₂.comp hσ.contDiffOn hmaps).contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hα'.contDiffAt ((hV.prod isOpen_univ).mem_nhds (show (x,t) ∈ V ×ˢ univ from ⟨hxZ,mem_univ t⟩))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hframe _ (hZΩ hxZ)) dy

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

lemma realNormalPart_dot_of_normal (X Y W n : Vec)
    (hX : X ⬝ᵥ n = 0) (hY : Y ⬝ᵥ n = 0) :
    realNormalPart X Y W ⬝ᵥ n = W ⬝ᵥ n := by
  simp only [realNormalPart,sub_dotProduct,smul_dotProduct,hX,hY,
    smul_eq_mul,mul_zero,sub_zero]

/-- The scaled longitudinal coefficient is read from `z Fxx`, so this
identification is uniform even when `Fxx` itself diverges. -/
theorem exists_profile_secondFormFrame {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (z : ℝ) (p : Base) (hJ : realBoundaryProfile F z p ∈ regularBoundaryProfiles) :
    ∃ d : SecondFormFrame F p
      (coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p),
      d.n = profilePreferred (realBoundaryProfile F z p) ∧
      d.m = profileComplement (realBoundaryProfile F z p) ∧
      profileCoefficients (realBoundaryProfile F z p) = ![d.S,d.D,d.N,z*d.L] := by
  obtain ⟨d,hn,hm,hS,hD,hN,hL⟩ := exists_secondFormFrame_with_coordinates hF p hJ.1 hJ.2
  have hn' : d.n = profilePreferred (realBoundaryProfile F z p) := hn
  have hm' : d.m = profileComplement (realBoundaryProfile F z p) := by
    simpa only [profileComplement,realBoundaryProfile,Matrix.cons_val_zero,
      Matrix.cons_val_one,hn'] using hm
  refine ⟨d,hn',hm',?_⟩
  have hdn := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dy F) p) d.n d.tangent_n.1 d.tangent_n.2
  have hnm := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dy F) p) d.m d.tangent_m.1 d.tangent_m.2
  have hlm := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dx F) p) d.m d.tangent_m.1 d.tangent_m.2
  ext j
  fin_cases j
  · exact hS.symm
  · change coordDeriv dx (coordDeriv dy F) p ⬝ᵥ
      profilePreferred (realBoundaryProfile F z p) = d.D
    rw [← hn',hD]
    exact hdn.symm
  · change coordDeriv dx (coordDeriv dy F) p ⬝ᵥ
      profileComplement (realBoundaryProfile F z p) = d.N
    rw [← hm',hN]
    exact hnm.symm
  · change (z • coordDeriv dx (coordDeriv dx F) p) ⬝ᵥ
      profileComplement (realBoundaryProfile F z p) = z*d.L
    rw [← hm',hL,smul_dotProduct]
    exact congrArg (fun a => z*a) hlm.symm

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualProfileCrossing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the compact turn/nonturn argument all the way to the two
ordered crossing invariants of an actual smooth surface. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma profileCoefficient_sub_le (H J : BoundaryProfile) (i : Fin 4) :
    |profileCoefficients H i-profileCoefficients J i| ≤
      ‖profileGeometry H-profileGeometry J‖ := by
  have h := (norm_le_pi_norm ((profileGeometry H-profileGeometry J).2) i).trans
    (norm_snd_le (profileGeometry H-profileGeometry J))
  simpa only [profileGeometry,Prod.snd_sub,Pi.sub_apply,Real.norm_eq_abs] using h

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The turn threshold is chosen from the fixed metric and slope bounds,
before the loop and its mixed/longitudinal derivatives are supplied. -/
theorem compact_actual_profile_crossings (sLo sHi K d T : ℝ)
    (hsLo : 0 < sLo) (hsHi : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, profileCoefficients (J x) 0 ≤ sHi) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
        κ*gramDet (coordDeriv dx F p) (coordDeriv dy F p) →
      -K ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ t u : ℝ, |t| ≤ T → |u| ≤ T →
        0 < orderedCrossing F (1,t) (1,u) p κ ∧
        0 < orderedCrossing F (1,u) (1,t) p κ := by
  obtain ⟨H,hH,hcross⟩ := compact_crossing_preservation (E := Space) (X := X)
    (sLo/2) (sHi+1) K (d+1) T (half_pos hsLo) (by linarith) hK (by linarith) hT
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hlo hhi hD hturn
  have hc : Continuous (fun x => profileCoefficients (J x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_profileCoefficients (hreg x)).continuousAt.comp hJ.continuousAt
  let A : X → ℝ := fun x => profileCoefficients (J x) 3
  let N₀ : X → ℝ := fun x => profileCoefficients (J x) 2
  have hA : Continuous A := (continuous_apply 3).comp hc
  have hN₀ : Continuous N₀ := (continuous_apply 2).comp hc
  obtain ⟨η₀,hη₀,hpreserve⟩ := hcross univ isCompact_univ A N₀ hA hN₀
    (fun x _ hx => hturn x hx)
  let ε := min 1 (min (sLo/2) η₀)
  have hε : 0 < ε := lt_min zero_lt_one (lt_min (half_pos hsLo) hη₀)
  obtain ⟨δ,hδ,hprofile⟩ := compact_boundary_profile_stability
    (isCompact_univ.image hJ) (by rintro _ ⟨x,_,rfl⟩; exact hreg x) ε hε
  refine ⟨min δ η₀,lt_min hδ hη₀,?_⟩
  intro z hz hzη x F hF p herror κ hk hcurv t u ht hu
  obtain ⟨hactual,hnear⟩ := hprofile (J x) (mem_image_of_mem J (mem_univ x))
    (realBoundaryProfile F z p) (herror.trans_le (min_le_left _ _))
  obtain ⟨f,hn,hm,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hdiff (j : Fin 4) :
      |(![f.S,f.D,f.N,z*f.L] j)-profileCoefficients (J x) j| < ε := by
    rw [← hcoef]
    exact (profileCoefficient_sub_le _ _ j).trans_lt hnear
  have hS : |f.S-profileCoefficients (J x) 0| < ε := by simpa using hdiff 0
  have hD' : |f.D-profileCoefficients (J x) 1| < ε := by simpa using hdiff 1
  have hN : |f.N-N₀ x| < η₀ := by
    exact (show |f.N-N₀ x| < ε by simpa [N₀] using hdiff 2).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hL : |z*f.L-A x| < η₀ := by
    exact (show |z*f.L-A x| < ε by simpa [A] using hdiff 3).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεS : ε ≤ sLo/2 := (min_le_right 1 _).trans (min_le_left _ _)
  have hsmin : sLo/2 ≤ f.S := by
    have hh := (abs_lt.mp hS).1
    linarith [hlo x]
  have hsmax : f.S ≤ sHi+1 := by
    have hh := (abs_lt.mp hS).2
    linarith [hhi x]
  have hdbound : |f.D| ≤ d+1 := by
    have hh := abs_sub_le f.D (profileCoefficients (J x) 1) 0
    simp only [sub_zero] at hh
    linarith [hD x]
  have hmn : inner ℝ (spaceCoordinates.symm f.m) (spaceCoordinates.symm f.n) = 0 := by
    rw [spaceCoordinates_symm_inner,dotProduct_comm]
    exact f.orthogonal
  have hh := hpreserve z hz (hzη.trans_le (min_le_right _ _)) x (mem_univ x)
    (spaceCoordinates.symm f.n) (spaceCoordinates.symm f.m)
    (spaceCoordinates_norm_unit f.unit_n) (spaceCoordinates_norm_unit f.unit_m) hmn
    f.S f.D f.N f.L _ t u hsmin hsmax hcurv hdbound ht hu hN hL
  rw [f.orderedCrossing_eq hF κ t u hk,f.orderedCrossing_eq hF κ u t hk]
  exact hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualProfileCurve
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonvanishing and avoidance of the negative preferred normal for every
nonzero curve direction, transferred from the five leading profiles. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem compact_actual_profile_curves (sLo K d : ℝ)
    (hsLo : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      -K ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ b c : ℝ, (b ≠ 0 ∨ c ≠ 0) →
        realSecondForm F (b,c) (b,c) p ≠ 0 ∧
        normalize (realSecondForm F (b,c) (b,c) p) ≠
          -profilePreferred (realBoundaryProfile F z p) := by
  obtain ⟨H,hH,hcurve⟩ := compact_curve_avoidance (X := X)
    (sLo/2) K (d+1) (half_pos hsLo) hK (by linarith)
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hlo hD hturn
  have hc : Continuous (fun x => profileCoefficients (J x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_profileCoefficients (hreg x)).continuousAt.comp hJ.continuousAt
  let A : X → ℝ := fun x => profileCoefficients (J x) 3
  let N₀ : X → ℝ := fun x => profileCoefficients (J x) 2
  have hA : Continuous A := (continuous_apply 3).comp hc
  have hN₀ : Continuous N₀ := (continuous_apply 2).comp hc
  obtain ⟨η₀,hη₀,hpreserve⟩ := hcurve univ isCompact_univ A N₀ hA hN₀
    (fun x _ hx => hturn x hx)
  let ε := min 1 (min (sLo/2) η₀)
  have hε : 0 < ε := lt_min zero_lt_one (lt_min (half_pos hsLo) hη₀)
  obtain ⟨δ,hδ,hprofile⟩ := compact_boundary_profile_stability
    (isCompact_univ.image hJ) (by rintro _ ⟨x,_,rfl⟩; exact hreg x) ε hε
  refine ⟨min δ η₀,lt_min hδ hη₀,?_⟩
  intro z hz hzη x F hF p herror hcurv b c hbc
  obtain ⟨hactual,hnear⟩ := hprofile (J x) (mem_image_of_mem J (mem_univ x))
    (realBoundaryProfile F z p) (herror.trans_le (min_le_left _ _))
  obtain ⟨f,hn,hm,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hdiff (j : Fin 4) :
      |(![f.S,f.D,f.N,z*f.L] j)-profileCoefficients (J x) j| < ε := by
    rw [← hcoef]
    exact (profileCoefficient_sub_le _ _ j).trans_lt hnear
  have hS : |f.S-profileCoefficients (J x) 0| < ε := by simpa using hdiff 0
  have hD' : |f.D-profileCoefficients (J x) 1| < ε := by simpa using hdiff 1
  have hN : |f.N-N₀ x| < η₀ := by
    exact (show |f.N-N₀ x| < ε by simpa [N₀] using hdiff 2).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hL : |z*f.L-A x| < η₀ := by
    exact (show |z*f.L-A x| < ε by simpa [A] using hdiff 3).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεS : ε ≤ sLo/2 := (min_le_right 1 _).trans (min_le_left _ _)
  have hsmin : sLo/2 ≤ f.S := by
    have hh := (abs_lt.mp hS).1
    linarith [hlo x]
  have hdbound : |f.D| ≤ d+1 := by
    have hh := abs_sub_le f.D (profileCoefficients (J x) 1) 0
    simp only [sub_zero] at hh
    linarith [hD x]
  have hh := hpreserve z hz (hzη.trans_le (min_le_right _ _)) x (mem_univ x)
    f.S f.D f.N f.L _ b c hsmin hcurv hdbound hbc hN hL
  simpa only [hn] using f.actual_curve_avoidance hF b c hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ActualProfileCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive boundary invariant on the zero-amplitude collar survives
small errors in the five profiles. No large angular derivative is needed there. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

private lemma continuousAt_collarInvariant {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) (v : ℝ × ℝ × ℝ) :
    ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => collarInvariant w.1 w.2) (J,v) := by
  have hc : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) =>
      profileCoefficients w.1) (J,v) :=
    ContinuousAt.comp (f := fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.1)
      (x := (J,v)) (contDiffAt_profileCoefficients hJ).continuousAt continuous_fst.continuousAt
  have hS := (continuous_apply 0).continuousAt.comp hc
  have hD := (continuous_apply 1).continuousAt.comp hc
  have hb : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.1) (J,v) :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hcc : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.2.1) (J,v) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hk : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.2.2) (J,v) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
  exact (((hD.mul hb).add (hS.mul hcc)).pow 2).add (hk.mul (hb.pow 2))

theorem compact_profile_collar {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} (hJ : Continuous J)
    (hreg : ∀ x, J x ∈ regularBoundaryProfiles)
    {b c k : X → ℝ} (hb : Continuous b) (hc : Continuous c) (hk : Continuous k)
    (hpos : ∀ x, 0 < (profileCoefficients (J x) 1 * b x +
      profileCoefficients (J x) 0 * c x)^2 + k x * b x^2) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∀ H : BoundaryProfile, ‖H-J x‖ < η →
      H ∈ regularBoundaryProfiles ∧
      0 < (profileCoefficients H 1 * b x + profileCoefficients H 0 * c x)^2 + k x * b x^2 := by
  let V : Set (BoundaryProfile × (ℝ × ℝ × ℝ)) := regularBoundaryProfiles ×ˢ univ
  let O : Set (BoundaryProfile × (ℝ × ℝ × ℝ)) :=
    V ∩ (fun w => collarInvariant w.1 w.2) ⁻¹' Ioi 0
  have hcont : ContinuousOn (fun w => collarInvariant w.1 w.2) V := by
    intro w hw
    exact (continuousAt_collarInvariant hw.1 w.2).continuousWithinAt
  have hO : IsOpen O := hcont.isOpen_inter_preimage
    (isOpen_regularBoundaryProfiles.prod isOpen_univ) isOpen_Ioi
  let f : X → BoundaryProfile × (ℝ × ℝ × ℝ) := fun x => (J x,b x,c x,k x)
  have hf : Continuous f := hJ.prodMk (hb.prodMk (hc.prodMk hk))
  have hfO : range f ⊆ O := by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨hreg x,mem_univ _⟩,hpos x⟩
  obtain ⟨η,hη,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open hO hfO
  refine ⟨η,hη,?_⟩
  intro x H hclose
  have hH : (H,b x,c x,k x) ∈ Metric.cthickening η (range f) := by
    apply Metric.thickening_subset_cthickening
    apply Metric.mem_thickening_iff.mpr
    refine ⟨f x,mem_range_self x,?_⟩
    change dist (H,(b x,c x,k x)) (J x,(b x,c x,k x)) < η
    rw [dist_prod_same_right,dist_eq_norm]
    exact hclose
  exact ⟨(hsub hH).1.1,(hsub hH).2⟩

/-- Transfer collar positivity to nonvanishing and antipode avoidance for the
actual second form, using the intrinsic curvature lower bound. -/
theorem compact_actual_profile_collar {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} (hJ : Continuous J)
    (hreg : ∀ x, J x ∈ regularBoundaryProfiles)
    {b c k : X → ℝ} (hb : Continuous b) (hc : Continuous c) (hk : Continuous k)
    (hpos : ∀ x, 0 < (profileCoefficients (J x) 1 * b x +
      profileCoefficients (J x) 0 * c x)^2 + k x * b x^2) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∀ F : RField 4, ContDiff ℝ ∞ F →
      ∀ z : ℝ, ∀ p : Base, ‖realBoundaryProfile F z p-J x‖ < η →
      k x ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      realSecondForm F (b x,c x) (b x,c x) p ≠ 0 ∧
      normalize (realSecondForm F (b x,c x) (b x,c x) p) ≠
        -profilePreferred (realBoundaryProfile F z p) := by
  obtain ⟨η,hη,hclose⟩ := compact_profile_collar hJ hreg hb hc hk hpos
  refine ⟨η,hη,?_⟩
  intro x F hF z p herr hcurv
  obtain ⟨hactual,hpositive⟩ := hclose x (realBoundaryProfile F z p) herr
  obtain ⟨f,hn,_,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hpositive' : 0 < (f.D*b x+f.S*c x)^2+k x*b x^2 := by
    simpa only [hcoef,Matrix.cons_val_zero,Matrix.cons_val_one] using hpositive
  have hactualpos : 0 < (f.D*b x+f.S*c x)^2+
      coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p*b x^2 :=
    hpositive'.trans_le (add_le_add_right (mul_le_mul_of_nonneg_right hcurv (sq_nonneg _)) _)
  have hcomp := pure_first_positive_of_collar (N := f.N) (L := f.L) f.size_pos hactualpos
  simpa only [hn] using f.actual_curve_avoidance hF (b x) (c x) (Or.inl hcomp)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualProfileCurveCover
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine the zero-amplitude collar with the interior turn estimate on a
compact curve. The turn threshold is fixed before the loop is selected. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem compact_actual_profile_curve_cover {C D : Set X}
    (hC : IsClosed C) (hD : IsClosed D) (hcover : ∀ x, x ∈ C ∨ x ∈ D)
    (sLo K d : ℝ) (hsLo : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x ∈ D, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∀ b c k : X → ℝ, Continuous b → Continuous c → Continuous k →
      (∀ x, b x ≠ 0 ∨ c x ≠ 0) → (∀ x, -K ≤ k x) →
      (∀ x ∈ C, 0 < (profileCoefficients (J x) 1 * b x +
        profileCoefficients (J x) 0 * c x)^2 + k x*b x^2) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      k x ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      realSecondForm F (b x,c x) (b x,c x) p ≠ 0 ∧
      normalize (realSecondForm F (b x,c x) (b x,c x) p) ≠
        -profilePreferred (realBoundaryProfile F z p) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  obtain ⟨H,hH,hcurve⟩ := compact_actual_profile_curves (X := D) sLo K d hsLo hK hd
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hS hDb hturn b c k hb hc hk hbc hkb hcollar
  obtain ⟨ηd,hηd,hinterior⟩ := hcurve (fun x => J x.val) (hJ.comp continuous_subtype_val)
    (fun x => hreg x.val) (fun x => hS x.val) (fun x => hDb x.val)
    (fun x => hturn x.val x.property)
  obtain ⟨ηc,hηc,hcollar'⟩ := compact_actual_profile_collar (X := C)
    (hJ.comp continuous_subtype_val) (fun x => hreg x.val)
    (hb.comp continuous_subtype_val) (hc.comp continuous_subtype_val) (hk.comp continuous_subtype_val)
    (fun x => hcollar x.val x.property)
  refine ⟨min ηc ηd,lt_min hηc hηd,?_⟩
  intro z hz hzη x F hF p herr hcurv
  rcases hcover x with hx | hx
  · exact hcollar' ⟨x,hx⟩ F hF z p (herr.trans_le (min_le_left _ _)) hcurv
  · exact hinterior z hz (hzη.trans_le (min_le_right _ _)) ⟨x,hx⟩ F hF p
      (herr.trans_le (min_le_right _ _)) ((hkb x).trans hcurv) (b x) (c x) (hbc x)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CompactCrossingChoice
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform choice of an admissible preferred-normal path at a crossing.
The transverse threshold is fixed before the angular loop. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem compact_crossing_normal_choice (sLo sHi K d T : ℝ)
    (hsLo : 0 < sLo) (hsHi : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ C : Set X, IsCompact C →
      ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
      (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
      ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
      ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → |N-N₀ x| < η → |z*L-A x| < η →
      let P := frameVector n m (slopePure S D N L k t)
      let Q := frameVector n m (slopePure S D N L k u)
      (0 < inner ℝ P n ∧ 0 < inner ℝ Q n) ∨
        (0 < inner ℝ P Q ∧ ∃ w : E,
          inner ℝ n w = 0 ∧ 0 < inner ℝ P w ∧ 0 < inner ℝ Q w) := by
  obtain ⟨H,hH,htransverse⟩ := uniform_crossing_threshold (E := E)
    sLo sHi K d T 0 hsLo hsHi hK hd hT le_rfl
  refine ⟨H,hH,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B+1
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀] <;> positivity
  have hbound : ∀ x ∈ C, |N₀ x| ≤ max 0 B := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  obtain ⟨J,hJ,hlong⟩ := longitudinal_normal_choice (E := E)
    sHi d B₀ T hsHi.le hd hB₀ hT
  obtain ⟨η₀,hη₀,halt⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min zero_lt_one hη₀,?_⟩
  intro z hz hzη x hx n m hn hm hmn S D N L k t u hS hShi hk hD ht hu hN hL
  dsimp only
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀ := by
    have hh := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at hh
    dsimp [B₀]
    linarith [hbound x hx]
  rcases halt z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
      (hL.trans_le (min_le_right _ _)) with hlargeN | hlargeL
  · left
    rw [frameVector_inner_first hn hmn,frameVector_inner_first hn hmn]
    exact ⟨(htransverse n m hn hm hmn S D N L k t u hS hShi hk hD ht hu hlargeN).1,
      (htransverse n m hn hm hmn S D N L k u t hS hShi hk hD hu ht hlargeN).1⟩
  · right
    exact hlong n m hn hm hmn S D N L k t u (hsLo.trans_le hS) hShi hD hNbound ht hu hlargeL

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ProfileCrossingChoice
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the compact turn/nonturn alternative to a unit normal path in
the actual normal plane, with both required endpoint inequalities. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The turn threshold is chosen from the fixed metric and slope bounds,
before the loop and its mixed/longitudinal derivatives are supplied. -/
theorem compact_actual_profile_crossing_choice (sLo sHi K d T : ℝ)
    (hsLo : 0 < sLo) (hsHi : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, profileCoefficients (J x) 0 ≤ sHi) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      -K ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ t u : ℝ, |t| ≤ T → |u| ≤ T →
        (0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ profilePreferred (realBoundaryProfile F z p) ∧
         0 < realSecondForm F (1,u) (1,u) p ⬝ᵥ profilePreferred (realBoundaryProfile F z p)) ∨
        (0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ realSecondForm F (1,u) (1,u) p ∧
          ∃ w : Vec, profilePreferred (realBoundaryProfile F z p) ⬝ᵥ w = 0 ∧
            0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ w ∧
            0 < realSecondForm F (1,u) (1,u) p ⬝ᵥ w) := by
  obtain ⟨H,hH,hcross⟩ := compact_crossing_normal_choice (E := Space) (X := X)
    (sLo/2) (sHi+1) K (d+1) T (half_pos hsLo) (by linarith) hK (by linarith) hT
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hlo hhi hD hturn
  have hc : Continuous (fun x => profileCoefficients (J x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_profileCoefficients (hreg x)).continuousAt.comp hJ.continuousAt
  let A : X → ℝ := fun x => profileCoefficients (J x) 3
  let N₀ : X → ℝ := fun x => profileCoefficients (J x) 2
  have hA : Continuous A := (continuous_apply 3).comp hc
  have hN₀ : Continuous N₀ := (continuous_apply 2).comp hc
  obtain ⟨η₀,hη₀,hpreserve⟩ := hcross univ isCompact_univ A N₀ hA hN₀
    (fun x _ hx => hturn x hx)
  let ε := min 1 (min (sLo/2) η₀)
  have hε : 0 < ε := lt_min zero_lt_one (lt_min (half_pos hsLo) hη₀)
  obtain ⟨δ,hδ,hprofile⟩ := compact_boundary_profile_stability
    (isCompact_univ.image hJ) (by rintro _ ⟨x,_,rfl⟩; exact hreg x) ε hε
  refine ⟨min δ η₀,lt_min hδ hη₀,?_⟩
  intro z hz hzη x F hF p herror hcurv t u ht hu
  obtain ⟨hactual,hnear⟩ := hprofile (J x) (mem_image_of_mem J (mem_univ x))
    (realBoundaryProfile F z p) (herror.trans_le (min_le_left _ _))
  obtain ⟨f,hn,hm,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hdiff (j : Fin 4) :
      |(![f.S,f.D,f.N,z*f.L] j)-profileCoefficients (J x) j| < ε := by
    rw [← hcoef]
    exact (profileCoefficient_sub_le _ _ j).trans_lt hnear
  have hS : |f.S-profileCoefficients (J x) 0| < ε := by simpa using hdiff 0
  have hD' : |f.D-profileCoefficients (J x) 1| < ε := by simpa using hdiff 1
  have hN : |f.N-N₀ x| < η₀ := by
    exact (show |f.N-N₀ x| < ε by simpa [N₀] using hdiff 2).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hL : |z*f.L-A x| < η₀ := by
    exact (show |z*f.L-A x| < ε by simpa [A] using hdiff 3).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεS : ε ≤ sLo/2 := (min_le_right 1 _).trans (min_le_left _ _)
  have hsmin : sLo/2 ≤ f.S := by
    have hh := (abs_lt.mp hS).1
    linarith [hlo x]
  have hsmax : f.S ≤ sHi+1 := by
    have hh := (abs_lt.mp hS).2
    linarith [hhi x]
  have hdbound : |f.D| ≤ d+1 := by
    have hh := abs_sub_le f.D (profileCoefficients (J x) 1) 0
    simp only [sub_zero] at hh
    linarith [hD x]
  have hmn : inner ℝ (spaceCoordinates.symm f.m) (spaceCoordinates.symm f.n) = 0 := by
    rw [spaceCoordinates_symm_inner,dotProduct_comm]
    exact f.orthogonal
  have hh := hpreserve z hz (hzη.trans_le (min_le_right _ _)) x (mem_univ x)
    (spaceCoordinates.symm f.n) (spaceCoordinates.symm f.m)
    (spaceCoordinates_norm_unit f.unit_n) (spaceCoordinates_norm_unit f.unit_m) hmn
    f.S f.D f.N f.L _ t u hsmin hsmax hcurv hdbound ht hu hN hL
  rw [← f.slope_space_components hF t,← f.slope_space_components hF u] at hh
  rcases hh with hpos | ⟨hpq,w,hnw,hpw,hqw⟩
  · left
    simpa only [spaceCoordinates_symm_inner,hn] using hpos
  · right
    refine ⟨by simpa only [spaceCoordinates_symm_inner] using hpq,spaceCoordinates w,?_,?_,?_⟩
    · rw [← hn]
      simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hnw
    · simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hpw
    · simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hqw

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceCurveCrossingLoop
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One supported loop preserves a finite family of later curves. The
boundary collars are fixed before selecting the compact interior and the
large transverse derivative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity PhaseGeometry SurfaceJetCoordinates

variable {ι : Type*} [Finite ι]

theorem actual_supported_curve_crossing_loop_oai {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    {K : ι → Set Base} (hK : ∀ i, IsCompact (K i)) (hKT : ∀ i, K i ⊆ T)
    {P : Set Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ i, K i) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ i, K i) ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0)
    {E : Set Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c k : ι → Base → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hk : ∀ i, ContDiff ℝ ∞ (k i))
    (hbc : ∀ i, ∀ x ∈ K i, b i x ≠ 0 ∨ c i x ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ i, ∀ x ∈ K i, -B ≤ k i x)
    (hold : ∀ i, ∀ x ∈ K i, a x = 0 →
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x))*b i x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x)*c i x)^2 + k i x*(b i x)^2) :
    ∃ Z : TopologicalSpace.Opens GeometricJet,
      jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
    ∃ l : Loop (jetDomain Z),
      (∀ J, l.amplitude J = a (decode J).1) ∧
      (∃ W : Set GeometricJet, IsOpen W ∧ jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
        ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
    ∃ e₁ e₂ : GeometricJet → Vec, ∃ α : GeometricJet × ℝ → ℝ,
      ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧ ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
      (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
      (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
    (∀ x ∈ T, ∀ t : ℝ, surfaceCircularProfile F a e₁ e₂ α (x,t) ∈ regularBoundaryProfiles) ∧
    ∃ η : ℝ, 0 < η ∧
      (∀ z : ℝ, 0 < z → z < η →
      ∀ i, ∀ x ∈ K i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      k i x ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i x,c i x) (b i x,c i x) p ≠ 0 ∧
      normalize (realSecondForm G (b i x,c i x) (b i x,c i x) p) ≠
        -profilePreferred (realBoundaryProfile G z p)) ∧
      ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p =
        κ*gramDet (coordDeriv dx G p) (coordDeriv dy G p) →
      -B ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧
        0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ realSecondForm G (1,s) (1,s) p ∧
           ∃ w : Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
             0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
             0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ w)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hadapt,sLo,sHi,D,hsLo,hsHi,hD,hfamily⟩ :=
    actual_surface_collar_profile_family hF ha hT hU hTU hn hI hN hHess haT hboundary
  obtain ⟨A,hA,hCA,hAe⟩ := hadapt
  let C₀ : Set Base := {p ∈ T | a p = 0}
  have hC : IsCompact C₀ := hT.inter_right (isClosed_eq ha.continuous continuous_const)
  have hcol (i : ι) := surface_zero_amplitude_collar hF ha hΩ (hK i)
    (fun _ hx => hTΩ (image_mono (hKT i) hx)) hC.isClosed (fun x hx => hx.2) h₁ h₂ hframe hA hCA
    (fun j hj => (hAe j hj).2) (hb i).contDiffOn (hc i).contDiffOn (hk i).contDiffOn
    (fun x hx => hold i x hx.1 hx.2.2)
  choose W hW hCW ε hε hcollar using hcol
  obtain ⟨δ,hδ,hδε⟩ := finite_positive_lower hε
  obtain ⟨V,hV,hCV,hconstruct⟩ := hfamily δ hδ
  let W₀ : Set Base := V ∩ ⋂ i, W i
  have hW₀ : IsOpen W₀ := hV.inter (isOpen_iInter_of_finite hW)
  have hCW₀ : C₀ ⊆ W₀ := fun x hx => ⟨hCV hx,mem_iInter.mpr (fun i => hCW i hx)⟩
  obtain ⟨V₀,hV₀,hCV₀,_,hV₀W⟩ := compact_open_thickening hC hW₀ hCW₀
  let L : Set Base := ⋃ i, K i
  have hL : IsCompact L := isCompact_iUnion hK
  have hLT : L ⊆ T := iUnion_subset hKT
  let I : Set Base := (L \ V₀) ∪ E
  have hIc : IsCompact I := (hL.diff hV₀).union hE.isCompact
  have hIT : I ⊆ T := union_subset (fun _ hx => hLT hx.1) hET
  have haI : ∀ x ∈ I, 0 < a x := by
    intro x hx
    rcases hx with hx | hx
    · apply lt_of_le_of_ne (haT x (hLT hx.1))
      intro hz
      exact hx.2 (hCV₀ ⟨hLT hx.1,hz.symm⟩)
    · exact haE x hx
  let P₀ := (P ∩ I) ∪ E
  have hP₀ : P₀.Finite := (hP.inter_of_left I).union hE
  have hP₀I : P₀ ⊆ I := union_subset inter_subset_right subset_union_right
  have hlocalI : ∀ p ∈ I \ P₀, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ I ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0 := by
    intro p hp
    have hpE : p ∉ E := fun h => hp.2 (Or.inr h)
    have hpL : p ∈ L := (hp.1.resolve_right hpE).1
    obtain ⟨N,hN,hpN,f,hf,hzero,hderiv⟩ := hlocal p ⟨hpL,fun h => hp.2 (Or.inl ⟨h,hp.1⟩)⟩
    refine ⟨N ∩ Eᶜ,hN.inter hE.isClosed.isOpen_compl,⟨hpN,hpE⟩,f,hf.mono inter_subset_left,?_,hderiv⟩
    intro x hx
    have hxL := hx.1.resolve_right hx.2.2
    exact hzero x ⟨hxL.1,hx.2.1⟩
  let X (i : ι) := ↥(K i ×ˢ Icc (0 : ℝ) 1)
  let (i : ι) : CompactSpace (X i) := isCompact_iff_compactSpace.mp ((hK i).prod isCompact_Icc)
  let C (i : ι) : Set (X i) := {w | w.val.1 ∈ closure V₀}
  let Q (i : ι) : Set (X i) := {w | w.val.1 ∉ V₀}
  have hC' (i : ι) : IsClosed (C i) := isClosed_closure.preimage (continuous_fst.comp continuous_subtype_val)
  have hQ' (i : ι) : IsClosed (Q i) := hV₀.isClosed_compl.preimage (continuous_fst.comp continuous_subtype_val)
  have hcover (i : ι) : ∀ w : X i, w ∈ C i ∨ w ∈ Q i := by
    intro w
    by_cases h : w.val.1 ∈ V₀
    · exact Or.inl (subset_closure h)
    · exact Or.inr h
  have hthreshold (i : ι) := compact_actual_profile_curve_cover (hC' i) (hQ' i) (hcover i)
    sLo B D hsLo hB hD
  choose H hH htransfer using hthreshold
  obtain ⟨Hbase,hHbase,hHHbase⟩ := finite_positive_upper H
  let Y := ↥(E ×ˢ Icc (0 : ℝ) 1)
  let : CompactSpace Y := isCompact_iff_compactSpace.mp (hE.isCompact.prod isCompact_Icc)
  obtain ⟨Hcross,hHcross,hcross⟩ := compact_actual_profile_crossings (X := Y)
    sLo sHi B D slopeBound hsLo hsHi hB hD hSlope
  obtain ⟨Hnormal,hHnormal,hnormal⟩ := compact_actual_profile_crossing_choice (X := Y)
    sLo sHi B D slopeBound hsLo hsHi hB hD hSlope
  let H₀ := max Hbase (max Hcross Hnormal)
  have hH₀ : 0 < H₀ := hHbase.trans_le (le_max_left _ _)
  have hHH₀ (i : ι) : H i ≤ H₀ := (hHHbase i).trans (le_max_left _ _)
  have hCrossH : Hcross ≤ H₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hNormalH : Hnormal ≤ H₀ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,hprofile,hturn⟩ :=
    hconstruct I P₀ hIc hIT haI hP₀ hP₀I hlocalI H₀ hH₀.le
  have hgood (i : ι) : ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ w : X i, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α w.val‖ < η →
      k i w.val.1 ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i w.val.1,c i w.val.1) (b i w.val.1,c i w.val.1) p ≠ 0 ∧
      normalize (realSecondForm G (b i w.val.1,c i w.val.1) (b i w.val.1,c i w.val.1) p) ≠
        -profilePreferred (realBoundaryProfile G z p) := by
    let J : X i → BoundaryProfile := fun w => surfaceCircularProfile F a e₁ e₂ α w.val
    have hJ : Continuous J := by
      exact ((surfaceCircularProfile_smoothOn hF ha hΩ hZΩ h₁ h₂ hα).continuousOn.mono
        (fun w hw => ⟨hTZ (mem_image_of_mem _ (hKT i hw.1)),mem_univ _⟩)).domRestrict
    have hd (w : X i) := hprofile w.val.1 (hKT i w.property.1) w.val.2
    have hturn' : ∀ w ∈ Q i, profileCoefficients (J w) 3 = 0 →
        H i+2 < |profileCoefficients (J w) 2| := by
      intro w hw hz
      have hh := hturn w.val.1 (Or.inl ⟨mem_iUnion.mpr ⟨i,w.property.1⟩,hw⟩) w.val.2 w.property.2 hz
      linarith [hHH₀ i]
    apply htransfer i J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
      (fun w => (hd w).2.2.2) hturn'
      (fun w => b i w.val.1) (fun w => c i w.val.1) (fun w => k i w.val.1)
      ((hb i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      ((hc i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      ((hk i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      (fun w => hbc i w.val.1 w.property.1) (fun w => hkb i w.val.1 w.property.1)
    intro w hw
    have hWmem : w.val.1 ∈ W i := mem_iInter.mp (hV₀W hw).2 i
    have hVmem : w.val.1 ∈ V := (hV₀W hw).1
    have hθ := (hsmall w.val.1 hVmem w.val.2).trans_le (hδε i)
    obtain ⟨hS,hD'⟩ := surfaceCircularProfile_frozen_coefficients hF ha hΩ hZΩ h₁ h₂ hframe hα
      (hTZ (mem_image_of_mem _ (hKT i w.property.1))) w.val.2
    change 0 < (profileCoefficients _ 1 * _ + profileCoefficients _ 0 * _)^2 + _
    rw [hS,hD']
    exact hcollar i w.val.1 ⟨w.property.1,hWmem⟩ _ hθ
  choose η hη hgood' using hgood
  obtain ⟨η₀,hη₀,hη₀η⟩ := finite_positive_lower hη
  let J : Y → BoundaryProfile := fun w => surfaceCircularProfile F a e₁ e₂ α w.val
  have hJ : Continuous J :=
    ((surfaceCircularProfile_smoothOn hF ha hΩ hZΩ h₁ h₂ hα).continuousOn.mono
      (fun w hw => ⟨hTZ (mem_image_of_mem _ (hET hw.1)),mem_univ _⟩)).domRestrict
  have hd (w : Y) := hprofile w.val.1 (hET w.property.1) w.val.2
  have ht (w : Y) (hz : profileCoefficients (J w) 3 = 0) :=
    hturn w.val.1 (Or.inr w.property.1) w.val.2 w.property.2 hz
  obtain ⟨ηc,hηc,hcross'⟩ := hcross J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
    (fun w => (hd w).2.2.1) (fun w => (hd w).2.2.2)
    (fun w hz => lt_of_le_of_lt (add_le_add hCrossH le_rfl) (ht w hz))
  obtain ⟨ηn,hηn,hnormal'⟩ := hnormal J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
    (fun w => (hd w).2.2.1) (fun w => (hd w).2.2.2)
    (fun w hz => lt_of_le_of_lt (add_le_add hNormalH le_rfl) (ht w hz))
  let ηall := min η₀ (min ηc ηn)
  have hηall : 0 < ηall := lt_min hη₀ (lt_min hηc hηn)
  have hηcurve : ηall ≤ η₀ := min_le_left _ _
  have hηcross : ηall ≤ ηc := (min_le_right _ _).trans (min_le_left _ _)
  have hηnormal : ηall ≤ ηn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Z,hTZ,fun j hj => hΩ (hZΩ hj),l,hamp,hzero,e₁,e₂,α,h₁.mono hZΩ,h₂.mono hZΩ,
    hα,hper,hvel,(fun x hx t => (hprofile x hx t).1),ηall,hηall,?_,?_⟩
  · intro z hz hzη i x hx t ht G hG p herr hcurv
    exact hgood' i z hz (hzη.trans_le (hηcurve.trans (hη₀η i))) ⟨(x,t),hx,ht⟩ G hG p
      (herr.trans_le (hηcurve.trans (hη₀η i))) hcurv
  · intro z hz hzη x hx t ht G hG p herr κ hκ hcurv r s hr hs
    obtain ⟨hleft,hright⟩ := hcross' z hz (hzη.trans_le hηcross) ⟨(x,t),hx,ht⟩
      G hG p (herr.trans_le hηcross) κ hκ hcurv r s hr hs
    exact ⟨hleft,hright,hnormal' z hz (hzη.trans_le hηnormal) ⟨(x,t),hx,ht⟩
      G hG p (herr.trans_le hηnormal) hcurv r s hr hs⟩

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop_oai.{u_1} := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop_oai.{u_1}
