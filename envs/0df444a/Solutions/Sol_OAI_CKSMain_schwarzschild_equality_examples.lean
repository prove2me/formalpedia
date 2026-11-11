-- Prove2me | solution 1 for OAI.CKSMain.schwarzschild_equality_examples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:50:31.764824+00:00
-- url     : https://prove2.me/submissions/f1593f91-5c84-4aad-a2aa-3ef788623b0b

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSBondiPenrose_002
import Definitions.Def_Q227CKS002
import Theorems.Thm_OAI_CKSSchwarzschild_numerical_equality
import Theorems.Thm_OAI_CKSSchwarzschild_physical_DEC
import Theorems.Thm_OAI_CKSSchwarzschild_source_minimum_area

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereCalculus
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_HeatBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

open scoped Pointwise

lemma volume_preimage_isometry (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Ambient) :
    (volume : Measure Ambient) (u ⁻¹' s) = volume s := by
  have hm := u.toHomeomorph.toMeasurableEquiv.map_apply (μ := volume) s
  change (Measure.map u volume) s = volume (u ⁻¹' s) at hm
  rw [u.measurePreserving.map_eq] at hm
  exact hm.symm

lemma sphereCone_preimage (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHome u ⁻¹' s)) =
      u ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨r, hr, u v.1, ⟨sphereHome u v, hv, rfl⟩, (u.map_smul r v.1).symm⟩
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨r, hr, u.symm v.1, ⟨sphereHome u.symm v, ?_, rfl⟩, ?_⟩
    · change sphereHome u (sphereHome u.symm v) ∈ s
      have h : sphereHome u (sphereHome u.symm v) = v := by
        apply Subtype.ext
        exact u.apply_symm_apply v.1
      simpa [h] using hv
    · apply u.injective
      simpa using hx

theorem sphereHome_measurePreserving (u : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereHome u) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereHome u).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereHome u).continuous.measurable hs,
    Measure.toSphere_apply' _ (hs.preimage (sphereHome u).continuous.measurable),
    Measure.toSphere_apply' _ hs, sphereCone_preimage, volume_preimage_isometry]

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

open scoped Manifold ContDiff Topology
open Set

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FullSphereHeat
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MeasureTheory Set

theorem sphereArea_eq_four_pi : sphereArea = 4 * Real.pi := by
  rw [sphereArea, sphereIntegral_apply]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.toSphere_real_apply_univ]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ADMAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSInducedSphere
open scoped Topology ContDiff

lemma surfaceMeasure_real : surfaceMeasure.real univ = 4*Real.pi := by
  rw [← sphereArea_eq_four_pi,sphereArea,sphereIntegral_apply]
  simp

end
end CKSADM

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiCharge
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact _root_.OAI.CKSSpatialManifold.spatialBilinearTriv_atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure)

lemma nullDirection_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞ nullDirection :=
by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : Sphere => (1:ℝ)) := contMDiff_const
  exact hc.prodMk_space (contMDiff_coe_sphere (E := E) (n := 2))

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiBalance
attribute [-instance] _root_.OAI.CKSSpatialManifold.spatialBilinearTriv_atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure sphereIntegral sphereArea)

lemma charge_energy {M : Sphere → ℝ} (hM : SmoothSphere M) :
    (bondiCharge M).1 = (16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure := by
  have h := rawCharge_test hM (ContinuousLinearMap.fst ℝ ℝ E)
  change (rawCharge M).1 = ∫ n, M n * 1 ∂surfaceMeasure at h
  simp only [mul_one] at h
  change (16*Real.pi)⁻¹ * (rawCharge M).1 = _
  rw [h]

lemma charge_momentum {M : Sphere → ℝ} (hM : SmoothSphere M) (i : Fin 3) :
    (bondiCharge M).2 i = (16*Real.pi)⁻¹ * ∫ n, M n * (n:E) i ∂surfaceMeasure := by
  have h := rawCharge_test hM
    ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))
  change (rawCharge M).2 i = ∫ n, M n * (n:E) i ∂surfaceMeasure at h
  change (16*Real.pi)⁻¹ * (rawCharge M).2 i = _
  rw [h]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_TailEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
lemma metricEDist_eq (g : Metric I (M := M)) (x y : M) :
    metricEDist I g x y =
      ⨅ γ : Path x y, ⨅ (_ : ContMDiff (modelWithCornersEuclideanHalfSpace 1) I 1 γ),
        ∫⁻ t : unitInterval, ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  unfold metricEDist
  rw [Manifold.riemannianEDist_def]
  congr 1
  funext γ
  congr 1
  funext hγ
  apply lintegral_congr
  intro t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

end
end CKSReplacementCompleteness

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundarySmooth
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSBoundarySurface
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

lemma inclusion_mfderiv_injective (x : Boundary M) :
    Injective (mfderiv I2 I3 (Subtype.val : Boundary M → M) x) := by
  rw [(inclusion_hasMFDeriv x).mfderiv]
  intro a b h
  change liftPlane a = liftPlane b at h
  have hh : dropPlane (liftPlane a) = dropPlane (liftPlane b) := congrArg dropPlane h
  change (a : E2) = (b : E2)
  exact (drop_lift a).symm.trans (hh.trans (drop_lift b))

end CKSBoundarySurface

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma lapse_smoothAt {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : ContDiffAt ℝ ∞ (lapse m) r := by
  exact (lapseSquared_smoothAt (lt_of_lt_of_le (mul_pos (by norm_num) hm) hr)).sqrt
    (ne_of_gt (lapseSquared_pos hm hr))
lemma lapse_dominates_velocity {m r : ℝ} (hm : 0 < m) (hr : 2*m < r) :
    |velocity m r| < lapse m r := by
  have hrp : 0 < r := lt_trans (mul_pos (by norm_num) hm) hr
  have hh : 2*m/r < 1 := (div_lt_one hrp).mpr hr
  have hs := lapse_sq hm hr.le
  have hp := lapse_pos hm hr.le
  have hvs : (|velocity m r|)^2 = (velocity m r)^2 := sq_abs _
  unfold lapseSquared at hs
  nlinarith [abs_nonneg (velocity m r)]

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildMetric
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] CKSSpatialManifold.real_id_isometric
attribute [local instance] OAI.CKSSchwarzschild.instIsBoundedSMulRealSpatialBilinear
attribute [local instance] OAI.CKSSchwarzschild.instTopologicalSpaceTotalSpaceExteriorContinuousLinearMapRealIdE3TangentSpaceEuclideanSpaceFinOfNatNatEuclideanHalfSpaceI3
lemma tensorInner_smooth {m : ℝ} (hm : 0 < m) :
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 (tensorInner m)) := by
  intro p
  apply endInner_smoothAt (position_smooth m p)
  apply cartTensor_smoothAt hm
  rw [norm_position hm]
  exact radius_ge m p
lemma tensorInner_symm (m : ℝ) (p : Exterior) (v w : TangentSpace I3 p) :
    tensorInner m p v w = tensorInner m p w v := by
  exact cartTensor_symm m _ _ _

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCartesianDerivatives
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma norm_derivative {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ (fun y : E3 => ‖y‖) x a = ⟪radialUnit x,a⟫_ℝ := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have he := congrArg (fun L : E3 →L[ℝ] ℝ => L a) (hn.hasFDerivAt.pow 2).fderiv
  rw [fderiv_norm_sq_apply] at he
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply,
    show (2:ℕ)-1=1 by norm_num,pow_one,nsmul_eq_mul,Nat.cast_ofNat] at he
  change 2 * ⟪x,a⟫_ℝ = 2 * ‖x‖ * (fderiv ℝ (fun y : E3 => ‖y‖) x) a at he
  simp only [radialUnit,real_inner_smul_left]
  have hp := norm_pos_iff.mpr hx
  field_simp
  nlinarith

lemma radialUnit_derivative {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ radialUnit x a = ‖x‖⁻¹ • (a-⟪radialUnit x,a⟫_ℝ • radialUnit x) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x hn.hasFDerivAt).smul (hasFDerivAt_id x)
  rw [show fderiv ℝ radialUnit x = _ from h.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit]
  simp only [Function.comp_def,id_eq]
  module

lemma radial_inner_derivative {x : E3} (hx : x ≠ 0) (a b : E3) :
    fderiv ℝ (fun y => ⟪radialUnit y,b⟫_ℝ) x a =
      (⟪a,b⟫_ℝ - ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)/‖x‖ := by
  rw [fderiv_inner_apply ℝ ((radialUnit_smoothAt hx).differentiableAt (by simp)) (differentiableAt_const b)]
  simp only [fderiv_const_apply,zero_apply,inner_zero_right,zero_add]
  rw [radialUnit_derivative hx,real_inner_smul_left,inner_sub_left,real_inner_smul_left]
  simp only [div_eq_mul_inv]
  ring

lemma radial_metric_derivative {x : E3} (hx : x ≠ 0) (c : E3 → ℝ)
    (hc : DifferentiableAt ℝ c x) (a b d : E3) :
    fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x d =
      fderiv ℝ c x d * (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) +
      c x / ‖x‖ * ((⟪d,a⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,a⟫_ℝ)*⟪radialUnit x,b⟫_ℝ +
        ⟪radialUnit x,a⟫_ℝ * (⟪d,b⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)) := by
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const (c := a))
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const (c := b))
  have h := (hasFDerivAt_const (⟪a,b⟫_ℝ) x).add (hc.hasFDerivAt.mul (ha.hasFDerivAt.mul hb.hasFDerivAt))
  rw [show fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x = _ from h.fderiv]
  simp only [add_apply,smul_apply,zero_add,smul_eq_mul]
  rw [radial_inner_derivative hx,radial_inner_derivative hx]
  simp only [Pi.mul_apply]
  ring

lemma radialNormal_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    fderiv ℝ (radialNormal m) x a =
      (deriv (lapse m) ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (lapse m ‖x‖ / ‖x‖) • tangentProjection x a := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have hu := (lapse_smoothAt hm hr).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h := (hu.hasDerivAt.hasFDerivAt.comp x hn.hasFDerivAt).smul
    ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  rw [show fderiv ℝ (radialNormal m) x = _ from h.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit_derivative hx]
  simp only [tangentProjection,smul_smul,div_eq_mul_inv]
  simp only [Function.comp_def]
  module
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildAdvancedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma lapseSquared_pos_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    0 < lapseSquared m r := by
  by_cases h : 2*m ≤ r
  · exact lapseSquared_pos hm h
  · rw [lapseSquared,velocity_near m r (by linarith)]
    have hp : 0 < r := lt_trans hm hr
    have he : 2*m/r < 2 := (div_lt_iff₀ hp).mpr (by linarith)
    norm_num
    linarith
lemma lapse_smooth_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    ContDiffAt ℝ ∞ (lapse m) r :=
  (lapseSquared_smoothAt (lt_trans hm hr)).sqrt (ne_of_gt (lapseSquared_pos_extended hm hr))
lemma lapse_pos_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) : 0 < lapse m r :=
  Real.sqrt_pos.mpr (lapseSquared_pos_extended hm hr)
lemma lapse_sub_velocity_pos {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    0 < lapse m r - velocity m r := by
  by_cases h : 2*m < r
  · linarith [lapse_dominates_velocity hm h,le_abs_self (velocity m r)]
  · rw [velocity_near m r (by linarith)]
    linarith [lapse_pos_extended hm hr]
lemma advancedSlope_smooth {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    ContDiffAt ℝ ∞ (advancedSlope m) r := by
  apply ((lapse_smooth_extended hm hr).mul
    ((lapse_smooth_extended hm hr).sub (velocity_smooth m).contDiffAt)).inv
  exact ne_of_gt (mul_pos (lapse_pos_extended hm hr) (lapse_sub_velocity_pos hm hr))
lemma advancedTime_hasDerivAt {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    HasDerivAt (advancedTime m) (advancedSlope m r) r := by
  have hs : ContinuousOn (advancedSlope m) (Ioi m) := fun s hs =>
    (advancedSlope_smooth hm hs).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (advancedSlope m) volume (2*m) r := by
    apply (hs.mono ?_).intervalIntegrable
    intro s h
    have hh : min (2*m) r ≤ s := h.1
    have hmin : m < min (2*m) r := lt_min (by linarith) hr
    exact lt_of_lt_of_le hmin hh
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hs.stronglyMeasurableAtFilter isOpen_Ioi r hr) (advancedSlope_smooth hm hr).continuousAt
lemma advancedTime_smooth {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (advancedTime m) (Ioi m) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  refine ⟨fun r hr => (advancedTime_hasDerivAt hm hr).differentiableAt.differentiableWithinAt,?_⟩
  apply ContDiffOn.congr (f := advancedSlope m)
    (fun r hr => (advancedSlope_smooth hm hr).contDiffWithinAt)
  intro r hr
  exact (advancedTime_hasDerivAt hm hr).deriv
lemma advancedGraph_smooth {m : ℝ} (hm : 0 < m) {x : E3} (hr : m < ‖x‖) :
    ContDiffAt ℝ ∞ (advancedGraph m) x := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  exact (((advancedTime_smooth hm).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x
    (contDiffAt_norm ℝ hx)).prodMk contDiffAt_id
lemma advancedGraph_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : m < ‖x‖) (a : E3) :
    fderiv ℝ (advancedGraph m) x a = graphTangent m x a := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := ((advancedTime_hasDerivAt hm hr).hasFDerivAt.comp x hn.hasFDerivAt).prodMk (hasFDerivAt_id x)
  rw [show fderiv ℝ (advancedGraph m) x = _ from h.fderiv]
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    norm_derivative hx,graphTangent]
  congr 1
  ring
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildNormalDerivative
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma radial_field_derivative {f : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f ‖x‖) (a : E3) :
    fderiv ℝ (fun y : E3 => f ‖y‖ • radialUnit y) x a =
      (deriv f ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (f ‖x‖ / ‖x‖) • tangentProjection x a := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := (hf.hasDerivAt.hasFDerivAt.comp x hn.hasFDerivAt).smul
    ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  rw [show fderiv ℝ (fun y : E3 => f ‖y‖ • radialUnit y) x = _ from h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit_derivative hx]
  simp only [tangentProjection,smul_smul,div_eq_mul_inv,Function.comp_def]
  module
lemma futureNormal_derivative {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : m < ‖z.2‖) (a : Spacetime) :
    fderiv ℝ (futureNormal m) z a =
    (((deriv (velocity m) ‖z.2‖-deriv (lapse m) ‖z.2‖)/(lapse m ‖z.2‖-velocity m ‖z.2‖)^2) * ⟪radialUnit z.2,a.2⟫_ℝ,
      (deriv (velocity m) ‖z.2‖ * ⟪radialUnit z.2,a.2⟫_ℝ) • radialUnit z.2 +
        (velocity m ‖z.2‖ / ‖z.2‖) • tangentProjection z.2 a.2) := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) z.2).differentiableAt one_ne_zero
  have hu := (lapse_smooth_extended hm hr).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hv := (velocity_smooth m).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ‖z.2‖
  have hq := (hu.hasDerivAt.sub hv.hasDerivAt).inv (ne_of_gt (lapse_sub_velocity_pos hm hr))
  have hF := (hq.hasFDerivAt.comp z.2 hn.hasFDerivAt).comp z spacePart.hasFDerivAt
  have hS := ((hv.comp z.2 hn).smul
    ((radialUnit_smoothAt hx).differentiableAt (by simp))).hasFDerivAt.comp z spacePart.hasFDerivAt
  have h := hF.prodMk hS
  rw [show fderiv ℝ (futureNormal m) z = _ from h.fderiv]
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  change ((spacePart a |> fderiv ℝ (fun y : E3 => ‖y‖) z.2) *
      (-(deriv (lapse m) ‖z.2‖-deriv (velocity m) ‖z.2‖)/(lapse m ‖z.2‖-velocity m ‖z.2‖)^2),
    fderiv ℝ (fun y : E3 => velocity m ‖y‖ • radialUnit y) z.2 a.2) = _
  rw [radial_field_derivative hx hv,norm_derivative hx]
  apply Prod.ext
  · change ⟪radialUnit z.2,a.2⟫_ℝ * _ = _
    ring
  · rfl
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildConnection
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma tangentProjection_orthogonal {x : E3} (hx : x ≠ 0) (a : E3) :
    ⟪radialUnit x,tangentProjection x a⟫_ℝ = 0 := by
  simp [tangentProjection,inner_sub_right,inner_smul_right,norm_radialUnit hx]
lemma cartMetric_tangent (m : ℝ) (x a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartMetric m x a b = ⟪a,b⟫_ℝ := by simp [cartMetric_apply,ha]
lemma cartTensor_tangent (m : ℝ) (x a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartTensor m x a b = velocity m ‖x‖ / ‖x‖ * ⟪a,b⟫_ℝ := by
  simp [cartTensor,euclideanForm_apply,radialForm_apply,ha]

lemma radial_connection_tangent {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖)
    (a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) (hb : ⟪radialUnit x,b⟫_ℝ = 0) :
    covariantPair (cartMetric m) (radialNormal m) x a b = lapse m ‖x‖/‖x‖ * ⟪a,b⟫_ℝ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  let c := fun y : E3 => (lapseSquared m ‖y‖)⁻¹-1
  have hc : DifferentiableAt ℝ c x := by
    exact ((((lapseSquared_smoothAt (lt_of_lt_of_le (by positivity) hr)).comp x
      (contDiffAt_norm ℝ hx)).inv (ne_of_gt (lapseSquared_pos hm hr))).sub contDiffAt_const).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hn : fderiv ℝ (radialNormal m) x a = (lapse m ‖x‖/‖x‖) • a := by
    rw [radialNormal_derivative hm hr,ha]
    simp [tangentProjection,ha]
  unfold covariantPair
  rw [hn]
  change cartMetric m x ((lapse m ‖x‖/‖x‖) • a) b + 1/2 *
    (fderiv ℝ (fun y => ⟪radialNormal m x,b⟫_ℝ + c y * (⟪radialUnit y,radialNormal m x⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x a +
     fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y * (⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x (radialNormal m x) -
     fderiv ℝ (fun y => ⟪a,radialNormal m x⟫_ℝ + c y * (⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x b) = _
  rw [radial_metric_derivative hx c hc,radial_metric_derivative hx c hc,radial_metric_derivative hx c hc]
  simp only [ha,hb,zero_mul,mul_zero,sub_zero,zero_add,add_zero]
  rw [cartMetric_apply]
  simp only [inner_smul_right,real_inner_smul_left,ha,hb,mul_zero,add_zero,
    radialNormal,radialUnit_inner_self hx,mul_one]
  rw [real_inner_comm b a]
  ring

lemma tangentProjection_normSq {x : E3} (hx : x ≠ 0) (a : E3) :
    ⟪tangentProjection x a,tangentProjection x a⟫_ℝ = ⟪a,a⟫_ℝ - ⟪radialUnit x,a⟫_ℝ^2 := by
  simp only [tangentProjection,inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right,
    radialUnit_inner_self hx,real_inner_comm a (radialUnit x)]
  ring

lemma sphereMeanCurvature_eq {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    sphereMeanCurvature m x = 2*lapse m ‖x‖/‖x‖ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  unfold sphereMeanCurvature
  simp_rw [radial_connection_tangent hm hr _ _ (tangentProjection_orthogonal hx _) (tangentProjection_orthogonal hx _)]
  rw [← Finset.mul_sum]
  have hs : (∑ i : Fin 3, ⟪tangentProjection x (EuclideanSpace.single i 1),tangentProjection x (EuclideanSpace.single i 1)⟫_ℝ) = 2 := by
    simp_rw [tangentProjection_normSq hx]
    rw [Finset.sum_sub_distrib]
    simp only [EuclideanSpace.inner_single_right,one_mul,PiLp.single_apply,ite_true, if_true]
    have h := real_inner_self_eq_norm_sq (radialUnit x)
    change (∑ i : Fin 3, (radialUnit x) i * (radialUnit x) i) = ‖radialUnit x‖^2 at h
    rw [norm_radialUnit hx] at h
    simp only [one_pow] at h
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    simp only [starRingEnd_apply,star_trivial,← sq] at h ⊢
    linarith
  rw [hs]
  ring

lemma sphereTensorTrace_eq {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    sphereTensorTrace m x = 2*velocity m ‖x‖/‖x‖ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  unfold sphereTensorTrace
  simp_rw [cartTensor_tangent m x _ _ (tangentProjection_orthogonal hx _)]
  have he := sphereMeanCurvature_eq hm hr
  unfold sphereMeanCurvature at he
  simp_rw [radial_connection_tangent hm hr _ _ (tangentProjection_orthogonal hx _) (tangentProjection_orthogonal hx _)] at he
  rw [← Finset.mul_sum] at he ⊢
  have hp := lapse_pos hm hr
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hr
  have hs : (∑ i : Fin 3, ⟪tangentProjection x (EuclideanSpace.single i 1),tangentProjection x (EuclideanSpace.single i 1)⟫_ℝ) = 2 := by
    apply (mul_left_cancel₀ (ne_of_gt (div_pos hp hn)))
    rw [he]
    ring
  rw [hs]
  ring

theorem horizon_expansion {m : ℝ} (hm : 0 < m) {x : E3} (hx : ‖x‖ = 2*m) :
    sphereThetaPlus m x = 0 := by
  unfold sphereThetaPlus
  rw [sphereMeanCurvature_eq hm (by linarith),sphereTensorTrace_eq hm (by linarith),hx,
    lapse_horizon hm,velocity_near m (2*m) (by linarith)]
  ring
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildSpacetimeAlgebra
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma advancedMetric_apply (m : ℝ) (z a b : Spacetime) :
    advancedMetric m z a b = -schwarzschildH m ‖z.2‖ * a.1*b.1 +
      a.1 * ⟪radialUnit z.2,b.2⟫_ℝ + b.1 * ⟪radialUnit z.2,a.2⟫_ℝ +
      ⟪a.2,b.2⟫_ℝ - ⟪radialUnit z.2,a.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ := by
  change -schwarzschildH m ‖z.2‖ * (a.1*b.1) + a.1 * ⟪radialUnit z.2,b.2⟫_ℝ +
    ⟪radialUnit z.2,a.2⟫_ℝ * b.1 + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit z.2,a.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ = _
  ring
lemma H_lapse {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    schwarzschildH m r = (lapse m r)^2-(velocity m r)^2 := by
  rw [lapse_sq hm hr]
  simp only [schwarzschildH,lapseSquared]
  ring
lemma H_factor {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    schwarzschildH m r = (lapse m r-velocity m r)*(lapse m r+velocity m r) := by
  rw [H_lapse hm hr]
  ring
lemma advancedSlope_identity {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    -schwarzschildH m r*(advancedSlope m r)^2+2*advancedSlope m r = (lapseSquared m r)⁻¹ := by
  have hh : m < r := lt_of_lt_of_le (by linarith) hr
  have hu := ne_of_gt (lapse_pos hm hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm hh)
  rw [H_factor hm hr,advancedSlope,← lapse_sq hm hr]
  field_simp
  ring
lemma graph_induced_metric {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    advancedMetric m (advancedGraph m x) (graphTangent m x a) (graphTangent m x b) = cartMetric m x a b := by
  rw [advancedMetric_apply,cartMetric_apply]
  change -schwarzschildH m ‖x‖*(advancedSlope m ‖x‖ * ⟪radialUnit x,a⟫_ℝ)*(advancedSlope m ‖x‖ * ⟪radialUnit x,b⟫_ℝ) +
    advancedSlope m ‖x‖ * ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ +
    advancedSlope m ‖x‖ * ⟪radialUnit x,b⟫_ℝ * ⟪radialUnit x,a⟫_ℝ + ⟪a,b⟫_ℝ -
    ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ = _
  linear_combination (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) * advancedSlope_identity hm hr
lemma futureNormal_unit {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : 2*m ≤ ‖z.2‖) :
    advancedMetric m z (futureNormal m z) (futureNormal m z) = -1 := by
  have hx : z.2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
  rw [advancedMetric_apply]
  simp only [futureNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  rw [H_factor hm hr]
  field_simp
  ring
lemma futureNormal_orthogonal {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    advancedMetric m (advancedGraph m x) (futureNormal m (advancedGraph m x)) (graphTangent m x a) = 0 := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
  have hu := ne_of_gt (lapse_pos hm hr)
  rw [advancedMetric_apply]
  simp only [futureNormal,advancedGraph,graphTangent,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  rw [H_factor hm hr,advancedSlope]
  field_simp
  ring
lemma futureNormal_future {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : 2*m ≤ ‖z.2‖) :
    0 < (futureNormal m z).1 := by
  exact inv_pos.mpr (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildSpacetimeDerivatives
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma H_hasDerivAt {m r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwarzschildH m) (2*m/r^2) r := by
  have h : HasDerivAt (fun s : ℝ => 1-2*m/s) (0-(0*r-2*m*1)/r^2) r :=
    (hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_const r (2*m)).div (hasDerivAt_id r) hr)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring
lemma H_radial_derivative {m : ℝ} {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ (fun y : E3 => schwarzschildH m ‖y‖) x a =
      (2*m/‖x‖^2) * ⟪radialUnit x,a⟫_ℝ := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x hn.hasFDerivAt
  rw [show fderiv ℝ (fun y : E3 => schwarzschildH m ‖y‖) x = _ from h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,norm_derivative hx]
  ring
lemma lapse_deriv_identity {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    lapse m r * deriv (lapse m) r = m/r^2 + velocity m r*deriv (velocity m) r := by
  have hu := (lapse_smooth_extended hm hr).differentiableAt (by simp)
  have hv := (velocity_smooth m).differentiable (by simp) r
  have h1 := hu.hasDerivAt.pow 2
  have h2 := (H_hasDerivAt (m := m) (ne_of_gt (lt_trans hm hr))).add (hv.hasDerivAt.pow 2)
  have he : (fun s => (lapse m s)^2) =ᶠ[𝓝 r] (fun s => schwarzschildH m s+(velocity m s)^2) := by
    filter_upwards [lt_mem_nhds hr] with s hs
    exact Real.sq_sqrt (lapseSquared_pos_extended hm hs).le
  have hh := (h1.congr_of_eventuallyEq he.symm).unique h2
  norm_num at hh
  linear_combination hh/2
lemma advancedMetric_spatial_derivative {m : ℝ} {x : E3} (hx : x ≠ 0) (a b : Spacetime) (d : E3) :
    fderiv ℝ (fun y : E3 => advancedMetric m (0,y) a b) x d =
      -(2*m/‖x‖^2) * ⟪radialUnit x,d⟫_ℝ * a.1*b.1 +
      (a.1- ⟪radialUnit x,a.2⟫_ℝ)/‖x‖ * (⟪d,b.2⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,b.2⟫_ℝ) +
      (b.1- ⟪radialUnit x,b.2⟫_ℝ)/‖x‖ * (⟪d,a.2⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,a.2⟫_ℝ) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have hh := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).differentiableAt.comp x hn
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).inner ℝ (differentiableAt_const a.2)
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).inner ℝ (differentiableAt_const b.2)
  have h := (((hh.hasFDerivAt.neg.mul_const a.1).mul_const b.1).add
    (hb.hasFDerivAt.const_mul a.1) |>.add (ha.hasFDerivAt.const_mul b.1) |>.add
    (hasFDerivAt_const (⟪a.2,b.2⟫_ℝ) x)).sub (ha.hasFDerivAt.mul hb.hasFDerivAt)
  have he : (fun y : E3 => advancedMetric m (0,y) a b) =
    (fun y => -schwarzschildH m ‖y‖ * a.1*b.1 + a.1 * ⟪radialUnit y,b.2⟫_ℝ +
      b.1 * ⟪radialUnit y,a.2⟫_ℝ + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit y,a.2⟫_ℝ * ⟪radialUnit y,b.2⟫_ℝ) := by
    funext y
    exact advancedMetric_apply m _ _ _
  change HasFDerivAt (fun y : E3 => -schwarzschildH m ‖y‖ * a.1*b.1 + a.1 * ⟪radialUnit y,b.2⟫_ℝ +
      b.1 * ⟪radialUnit y,a.2⟫_ℝ + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit y,a.2⟫_ℝ * ⟪radialUnit y,b.2⟫_ℝ) _ x at h
  rw [he, h.fderiv]
  simp only [sub_apply,add_apply,neg_apply,smul_apply,add_zero,smul_eq_mul,Function.comp_def]
  rw [H_radial_derivative hx,radial_inner_derivative hx,radial_inner_derivative hx]
  ring
lemma advancedMetric_derivative {m : ℝ} {z : Spacetime} (hx : z.2 ≠ 0) (a b d : Spacetime) :
    fderiv ℝ (fun y => advancedMetric m y a b) z d =
      -(2*m/‖z.2‖^2) * ⟪radialUnit z.2,d.2⟫_ℝ * a.1*b.1 +
      (a.1- ⟪radialUnit z.2,a.2⟫_ℝ)/‖z.2‖ * (⟪d.2,b.2⟫_ℝ - ⟪radialUnit z.2,d.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ) +
      (b.1- ⟪radialUnit z.2,b.2⟫_ℝ)/‖z.2‖ * (⟪d.2,a.2⟫_ℝ - ⟪radialUnit z.2,d.2⟫_ℝ * ⟪radialUnit z.2,a.2⟫_ℝ) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) z.2).differentiableAt one_ne_zero
  have hh := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).differentiableAt.comp z.2 hn
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).inner ℝ (differentiableAt_const a.2)
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).inner ℝ (differentiableAt_const b.2)
  have hs : DifferentiableAt ℝ (fun y : E3 => advancedMetric m (0,y) a b) z.2 := by
    simp_rw [advancedMetric_apply]
    exact ((((hh.neg.mul_const a.1).mul_const b.1).add (hb.const_mul a.1)).add (ha.const_mul b.1) |>.add (differentiableAt_const (⟪a.2,b.2⟫_ℝ))).sub (ha.mul hb)
  have h := hs.hasFDerivAt.comp z (spacePart.hasFDerivAt)
  rw [show fderiv ℝ (fun y => advancedMetric m y a b) z = _ from h.fderiv]
  change fderiv ℝ (fun y : E3 => advancedMetric m (0,y) a b) z.2 d.2 = _
  exact advancedMetric_spatial_derivative hx a b d.2
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildGraphSecondForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma second_coefficient {u v du dv c : ℝ} (hu : u ≠ 0) (hq : u-v ≠ 0)
    (hid : u*du = c+v*dv) :
    -((u-v)*(u+v))*((dv-du)/(u-v)^2)*(u*(u-v))⁻¹ +
      (dv-du)/(u-v)^2 + (u*(u-v))⁻¹*dv-c*v*((u*(u-v))⁻¹)^2 = dv/u^2 := by
  field_simp
  linear_combination v * hid

lemma graph_metric_cross_derivatives {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    fderiv ℝ (fun y => advancedMetric m y (futureNormal m (advancedGraph m x)) (graphTangent m x b))
      (advancedGraph m x) (graphTangent m x a) =
    fderiv ℝ (fun y => advancedMetric m y (graphTangent m x a) (futureNormal m (advancedGraph m x)))
      (advancedGraph m x) (graphTangent m x b) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [advancedMetric_derivative hx,advancedMetric_derivative hx]
  simp only [advancedGraph,graphTangent,futureNormal,inner_smul_right,
    radialUnit_inner_self hx,mul_one,real_inner_comm a (radialUnit x),real_inner_comm b (radialUnit x),real_inner_comm b a]
  ring

lemma graph_metric_normal_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    fderiv ℝ (fun y => advancedMetric m y (graphTangent m x a) (graphTangent m x b))
      (advancedGraph m x) (futureNormal m (advancedGraph m x)) =
      -(2*m/‖x‖^2)*velocity m ‖x‖*(advancedSlope m ‖x‖)^2 *
        (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [advancedMetric_derivative hx]
  simp only [advancedGraph,graphTangent,futureNormal,inner_smul_right,real_inner_smul_left,
    radialUnit_inner_self hx,mul_one]
  ring

lemma advancedMetric_radial_pair {m : ℝ} {z : Spacetime} (hx : z.2 ≠ 0)
    (a b : E3) (A B C s : ℝ) :
    advancedMetric m z (A * ⟪radialUnit z.2,a⟫_ℝ,
        (B * ⟪radialUnit z.2,a⟫_ℝ) • radialUnit z.2 + C • tangentProjection z.2 a)
      (s * ⟪radialUnit z.2,b⟫_ℝ,b) =
      (-schwarzschildH m ‖z.2‖*A*s+A+s*B) * (⟪radialUnit z.2,a⟫_ℝ * ⟪radialUnit z.2,b⟫_ℝ) +
        C * (⟪a,b⟫_ℝ - ⟪radialUnit z.2,a⟫_ℝ * ⟪radialUnit z.2,b⟫_ℝ) := by
  rw [advancedMetric_apply]
  simp only [tangentProjection,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  ring

lemma futureNormal_graph_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    fderiv ℝ (futureNormal m) (advancedGraph m x) (graphTangent m x a) =
    (((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2) * ⟪radialUnit x,a⟫_ℝ,
      (deriv (velocity m) ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (velocity m ‖x‖ / ‖x‖) • tangentProjection x a) := by
  have hmx : m < ‖x‖ := lt_of_lt_of_le (by linarith) hr
  simpa only [advancedGraph, graphTangent] using
    (futureNormal_derivative hm (z := advancedGraph m x) hmx (graphTangent m x a))

lemma graph_normal_derivative_pair {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    advancedMetric m (advancedGraph m x)
      (fderiv ℝ (futureNormal m) (advancedGraph m x) (graphTangent m x a)) (graphTangent m x b) =
      (-schwarzschildH m ‖x‖*((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2)*advancedSlope m ‖x‖ +
        (deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2 +
        advancedSlope m ‖x‖*deriv (velocity m) ‖x‖) * (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) +
      (velocity m ‖x‖ / ‖x‖) * (⟪a,b⟫_ℝ - ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [futureNormal_graph_derivative hm hr]
  simpa only [advancedGraph, graphTangent] using
    (advancedMetric_radial_pair (m := m) (z := advancedGraph m x) hx a b
      ((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2)
      (deriv (velocity m) ‖x‖) (velocity m ‖x‖ / ‖x‖) (advancedSlope m ‖x‖))

lemma graph_induced_second_form {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    covariantPair (advancedMetric m) (futureNormal m) (advancedGraph m x)
      (graphTangent m x a) (graphTangent m x b) = cartTensor m x a b := by
  rw [covariantPair,graph_metric_cross_derivatives hm hr,graph_metric_normal_derivative hm hr,
    graph_normal_derivative_pair hm hr]
  have hc := second_coefficient (ne_of_gt (lapse_pos hm hr))
    (ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr)))
    (lapse_deriv_identity hm (lt_of_lt_of_le (by linarith) hr))
  rw [← H_factor hm hr] at hc
  change -schwarzschildH m ‖x‖ * _ * advancedSlope m ‖x‖ + _ + advancedSlope m ‖x‖ * deriv (velocity m) ‖x‖ -
    m/‖x‖^2 * velocity m ‖x‖ * (advancedSlope m ‖x‖)^2 = deriv (velocity m) ‖x‖/(lapse m ‖x‖)^2 at hc
  change _ = velocity m ‖x‖ / ‖x‖ * ⟪a,b⟫_ℝ +
      (deriv (velocity m) ‖x‖ / lapseSquared m ‖x‖ - velocity m ‖x‖ / ‖x‖) *
      (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)
  rw [← lapse_sq hm hr]
  linear_combination (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) * hc
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma radialNormal_points_out {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    0 < fderiv ℝ (fun y : E3 => ‖y‖) x (radialNormal m x) := by
  have hn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  rw [norm_derivative hn]
  simp only [radialNormal,inner_smul_right,radialUnit_inner_self hn,mul_one]
  exact lapse_pos hm hx
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildRoundMetric
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] OAI.CKSSchwarzschild.schwarzschildRoundMetricFinrank
lemma metricInner_quad {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    metricInner m p v v = (v 0)^2 / lapseSquared m (radius m p) +
      (radius m p)^2 * ‖ambientDerivative directionAmbient p v‖^2 := by
  change cartMetric m (position m p) (ambientDerivative (position m) p v)
    (ambientDerivative (position m) p v) = _
  rw [cartMetric_apply,position_radial_inner hm,norm_position hm]
  have ho : ⟪ambientDerivative directionAmbient p v,directionAmbient p⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact directionAmbient_orthogonal p v
  rw [mfderiv_position,inner_add_left,inner_add_right,inner_add_right]
  have ho' : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 :=
    directionAmbient_orthogonal p v
  simp only [inner_smul_left,inner_smul_right,ho,ho',starRingEnd_apply,star_trivial,
    real_inner_self_eq_norm_sq,norm_direction]
  ring

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_LocalMaximumHessian
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply _root_.OAI.CKSSchwarzschild.drop_join _root_.OAI.CKSSchwarzschild.halfProduct_symm_fst _root_.OAI.CKSSchwarzschild.halfProduct_symm_snd _root_.OAI.CKSSchwarzschild.halfProduct_val _root_.OAI.CKSSchwarzschild.join_drop _root_.OAI.CKSSchwarzschild.join_succ _root_.OAI.CKSSchwarzschild.join_zero _root_.OAI.CKSSchwarzschild.productChart_apply _root_.OAI.CKSSchwarzschild.productChart_source _root_.OAI.CKSSchwarzschild.productChart_symm _root_.OAI.CKSSchwarzschild.productChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma localMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [h,hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by simpa using he.deriv
  have hz : deriv (deriv f) x = 0 := by simpa using hd.deriv_eq
  linarith

lemma affineLine_hasDerivAt (y a : E2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => y+s•a) a t := by
  simpa using ((hasDerivAt_id t).smul_const a).const_add y

lemma line_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E2 → V} {y : E2} (hf : DifferentiableAt ℝ f y) (a : E2) :
    deriv (fun t : ℝ => f (y+t•a)) 0 = fderiv ℝ f y a := by
  have hh : HasFDerivAt f (fderiv ℝ f y) (y+(0:ℝ)•a) := by simpa using hf.hasFDerivAt
  exact (hh.comp_hasDerivAt 0 (affineLine_hasDerivAt y a 0)).deriv

lemma line_second_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E2 → V} {y : E2} (hf : ContDiffAt ℝ ∞ f y) (a : E2) :
    deriv (deriv (fun t : ℝ => f (y+t•a))) 0 =
      fderiv ℝ (fun z => fderiv ℝ f z a) y a := by
  have he : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
    ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono
      (fun _ h => h.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hline : Tendsto (fun t : ℝ => y+t•a) (𝓝 0) (𝓝 y) := by
    have hh := (affineLine_hasDerivAt y a 0).continuousAt
    change Tendsto _ _ (𝓝 (y+(0:ℝ)•a)) at hh
    simpa using hh
  have hh : deriv (fun t : ℝ => f (y+t•a)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (y+t•a) a) := by
    filter_upwards [hline he] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (affineLine_hasDerivAt y a t)).deriv
  rw [hh.deriv_eq]
  exact line_deriv (((hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : ∞+1 ≤ ∞)).clm_apply contDiffAt_const).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) a

lemma curve_normSq_second {c : ℝ → E3} {t : ℝ} (hc : ContDiffAt ℝ ∞ c t) :
    deriv (deriv (fun s => ‖c s‖^2)) t =
      2 * (⟪deriv c t,deriv c t⟫_ℝ + ⟪c t,deriv (deriv c) t⟫_ℝ) := by
  have he : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ c s :=
    ((hc.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono
      (fun _ h => h.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hder : deriv (fun s => ‖c s‖^2) =ᶠ[𝓝 t]
      (fun s => 2*⟪c s,deriv c s⟫_ℝ) := by
    filter_upwards [he] with s hs
    have hd := hs.hasDerivAt.inner ℝ hs.hasDerivAt
    simpa [real_inner_self_eq_norm_sq,real_inner_comm (deriv c s) (c s),two_mul] using hd.deriv
  rw [hder.deriv_eq]
  have hd := (hc.differentiableAt (by simp)).hasDerivAt.inner ℝ
    (((hc.derivWithin (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : ∞+1 ≤ ∞)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt)
  convert (hd.const_mul 2).deriv using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma maximum_radius_hessian {f : E2 → E3} {y : E2}
    (hf : ContDiffAt ℝ ∞ f y) (hm : IsLocalMax (fun z => ‖f z‖^2) y) (a : E2) :
    ⟪f y, fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ ≤
      -⟪fderiv ℝ f y a, fderiv ℝ f y a⟫_ℝ := by
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => f (y+t•a)) 0 := by
    have hh : ContDiffAt ℝ ∞ f (y+(0:ℝ)•a) := by simpa using hf
    exact hh.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hmax : IsLocalMax (fun t : ℝ => ‖f (y+t•a)‖^2) 0 := by
    have hh : IsLocalMax (fun z => ‖f z‖^2) (y+(0:ℝ)•a) := by simpa using hm
    exact hh.comp_continuous (g := fun t : ℝ => y+t•a) (b := 0) (affineLine_hasDerivAt y a 0).continuousAt
  have hh := localMax_second_deriv_nonpos hmax (hc.continuousAt.norm.pow 2)
  rw [curve_normSq_second hc, line_second_deriv hf a,
    line_deriv (hf.differentiableAt (by simp)) a] at hh
  simpa using (show ⟪f (y+(0:ℝ)•a), fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ ≤
    -⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ from by linarith)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceChristoffel
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma metric_normal_pair {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) (z : E3) :
    cartMetric m x (radialNormal m x) z = ⟪radialUnit x,z⟫_ℝ / lapse m ‖x‖ := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  have hu := lapse_pos hm hx
  rw [cartMetric_apply]
  simp only [radialNormal,real_inner_smul_left,inner_smul_right,radialUnit_inner_self hxn,mul_one]
  rw [← lapse_sq hm hx]
  field_simp
  ring

lemma christoffel_tangent_radial {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖)
    (a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) (hb : ⟪radialUnit x,b⟫_ℝ = 0) :
    christoffelPair (cartMetric m) x a b (radialNormal m x) =
      (1/lapse m ‖x‖ - lapse m ‖x‖) / ‖x‖ * ⟪a,b⟫_ℝ := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  have hxn : x ≠ 0 := norm_pos_iff.mp hn
  let c := fun y : E3 => (lapseSquared m ‖y‖)⁻¹-1
  have hc : DifferentiableAt ℝ c x :=
    ((((lapseSquared_smoothAt hn).comp x (contDiffAt_norm ℝ hxn)).inv
      (ne_of_gt (lapseSquared_pos hm hx))).sub contDiffAt_const).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold christoffelPair
  change 1/2 *
    (fderiv ℝ (fun y => ⟪b,radialNormal m x⟫_ℝ+c y*(⟪radialUnit y,b⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x a +
     fderiv ℝ (fun y => ⟪a,radialNormal m x⟫_ℝ+c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x b -
     fderiv ℝ (fun y => ⟪a,b⟫_ℝ+c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x (radialNormal m x)) = _
  rw [radial_metric_derivative hxn c hc,radial_metric_derivative hxn c hc,
    radial_metric_derivative hxn c hc]
  simp only [ha,hb,zero_mul,mul_zero,zero_add,add_zero,sub_zero,
    radialNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hxn,mul_one]
  rw [real_inner_comm b a]
  dsimp [c]
  rw [← lapse_sq hm hx]
  have hu := lapse_pos hm hx
  field_simp
  ring

lemma christoffel_neg_normal (g : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ) (x a b N : E3) :
    christoffelPair g x a b (-N) = -christoffelPair g x a b N := by
  simp only [christoffelPair,map_neg,fderiv_fun_neg,neg_apply]
  ring
lemma parameterSecondForm_neg (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) (a b : E2) :
    parameterSecondForm m f y (-N) a b = -parameterSecondForm m f y N a b := by
  simp only [parameterSecondForm,map_neg,neg_apply,christoffel_neg_normal]
  ring
lemma parameterMeanCurvature_neg (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) :
    parameterMeanCurvature m f y (-N) = -parameterMeanCurvature m f y N := by
  simp only [parameterMeanCurvature,parameterSecondForm_neg]
  ring

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceFrames
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma first_basis_ne_zero : (EuclideanSpace.single 0 1 : E2) ≠ 0 := by
  intro hh
  have := congrArg (fun x : E2 => x 0) hh
  simp at this
lemma secondResidual_ne_zero (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3) :
    secondResidual g T ≠ 0 := by
  intro hh
  have := congrArg (fun x : E2 => x 1) hh
  simp [secondResidual] at this

lemma normalized_metric_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (v : E3)
    (hv : 0 < g v v) :
    g ((Real.sqrt (g v v))⁻¹ • v) ((Real.sqrt (g v v))⁻¹ • v) = 1 := by
  have hp := Real.sqrt_pos.mpr hv
  have hs := Real.sq_sqrt hv.le
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp
  nlinarith

lemma firstFrame_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (hT : Function.Injective T) :
    g (T (firstFrame g T)) (T (firstFrame g T)) = 1 := by
  have hne : T (EuclideanSpace.single 0 1) ≠ 0 := by
    simpa only [map_zero] using hT.ne first_basis_ne_zero
  simpa only [firstFrame,map_smul] using normalized_metric_unit g _ (hg _ hne)

lemma secondFrame_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (hT : Function.Injective T) :
    g (T (secondFrame g T)) (T (secondFrame g T)) = 1 := by
  have hne : T (secondResidual g T) ≠ 0 := by
    simpa only [map_zero] using hT.ne (secondResidual_ne_zero g T)
  simpa only [secondFrame,map_smul] using normalized_metric_unit g _ (hg _ hne)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceNormal
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma maximum_radius_tangent {f : E2 → E3} {y : E2}
    (hf : DifferentiableAt ℝ f y) (hm : IsLocalMax (fun z => ‖f z‖^2) y) (a : E2) :
    ⟪radialUnit (f y),fderiv ℝ f y a⟫_ℝ = 0 := by
  have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L a) (hm.hasFDerivAt_eq_zero hf.hasFDerivAt.norm_sq)
  have hzero : ⟪f y,fderiv ℝ f y a⟫_ℝ = 0 := by
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      zero_apply] at hh
    change (2:ℕ) • ⟪f y,fderiv ℝ f y a⟫_ℝ = 0 at hh
    simpa only [two_nsmul,add_self_eq_zero] using hh
  simp only [radialUnit,real_inner_smul_left,hzero,mul_zero]

lemma tangent_range (x : E3) (hx : x ≠ 0) (T : E2 →L[ℝ] E3)
    (hT : Function.Injective T) (ht : ∀ a, ⟪radialUnit x,T a⟫_ℝ = 0) :
    LinearMap.range T.toLinearMap = (ℝ ∙ radialUnit x)ᗮ := by
  have hn : radialUnit x ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_radialUnit hx]; norm_num)
  let : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp [E3]⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨a,rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (ht a)
  · rw [LinearMap.finrank_range_of_inj hT,Submodule.finrank_orthogonal_span_singleton (n := 2) hn]
    simp [E2]

lemma normal_radial_at_tangent {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖)
    (T : E2 →L[ℝ] E3) (hT : Function.Injective T)
    (ht : ∀ a, ⟪radialUnit x,T a⟫_ℝ = 0) (N : E3)
    (hunit : cartMetric m x N N = 1) (horth : ∀ a, cartMetric m x N (T a) = 0) :
    N = radialNormal m x ∨ N = -radialNormal m x := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  let q := ⟪radialUnit x,N⟫_ℝ
  let d := N-q•radialUnit x
  have hd : ⟪radialUnit x,d⟫_ℝ = 0 := by
    simp only [d,inner_sub_right,inner_smul_right,radialUnit_inner_self hxn,mul_one]
    exact sub_self _
  have hdr : d ∈ LinearMap.range T.toLinearMap := by
    rw [tangent_range x hxn T hT ht]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hd
  obtain ⟨a,ha⟩ := hdr
  change T a = d at ha
  have ho : ⟪N,d⟫_ℝ = 0 := by
    have hh := horth a
    change cartMetric m x N (T a) = 0 at hh
    rw [ha,cartMetric_apply,hd] at hh
    simpa using hh
  have hdd : ⟪d,d⟫_ℝ = 0 := by
    change ⟪N-q•radialUnit x,d⟫_ℝ = 0
    rw [inner_sub_left,real_inner_smul_left,ho,hd]
    ring
  have he : N = q•radialUnit x := sub_eq_zero.mp (inner_self_eq_zero.mp hdd)
  have hu := lapse_pos hm hx
  have hu2 := lapseSquared_pos hm hx
  have hq : q^2 = (lapse m ‖x‖)^2 := by
    rw [he,cartMetric_apply] at hunit
    simp only [real_inner_smul_left,inner_smul_right,radialUnit_inner_self hxn,mul_one] at hunit
    rw [← lapse_sq hm hx] at hunit
    field_simp at hunit
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hq) with hh | hh
  · left
    rw [he,hh]
    rfl
  · right
    rw [he,hh]
    simp [radialNormal,neg_smul]

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceBarrier
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma scalar_second_form_bound {r u h : ℝ} (hr : 0 < r) (hu : 0 < u) (hh : h ≤ -1) :
    u/r ≤ -(h/r/u + (1/u-u)/r) := by
  have he : -(h/r/u + (1/u-u)/r) - u/r = (-h-1)/(r*u) := by
    field_simp
    ring
  have := div_nonneg (by linarith : 0 ≤ -h-1) (mul_pos hr hu).le
  rw [← he] at this
  linarith

lemma outward_surface_second_form_bound {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (a : E2) (ha : cartMetric m (f y) (fderiv ℝ f y a) (fderiv ℝ f y a) = 1) :
    lapse m ‖f y‖ / ‖f y‖ ≤ parameterSecondForm m f y (radialNormal m (f y)) a a := by
  have ht := maximum_radius_tangent (hf.differentiableAt (by simp)) hmax a
  have hau : ⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ = 1 := by
    rwa [cartMetric_tangent m _ _ _ ht] at ha
  have hh := maximum_radius_hessian hf hmax a
  rw [hau] at hh
  have hs : ⟪radialUnit (f y),fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ =
      ⟪f y,fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ / ‖f y‖ := by
    simp only [radialUnit,real_inner_smul_left,div_eq_mul_inv]
    ring
  rw [parameterSecondForm,metric_normal_pair hm hr,christoffel_tangent_radial hm hr _ _ ht ht,hau,mul_one,hs]
  exact scalar_second_form_bound (lt_of_lt_of_le (by positivity) hr) (lapse_pos hm hr) hh

lemma outward_surface_mean_bound {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) :
    2*lapse m ‖f y‖/‖f y‖ ≤ parameterMeanCurvature m f y (radialNormal m (f y)) := by
  have hpos := cartMetric_pos hm hr
  have ha := outward_surface_second_form_bound hm hf hmax hr _ (firstFrame_unit _ _ hpos hinj)
  have hb := outward_surface_second_form_bound hm hf hmax hr _ (secondFrame_unit _ _ hpos hinj)
  dsimp [parameterMeanCurvature]
  calc
    2*lapse m ‖f y‖/‖f y‖ = lapse m ‖f y‖/‖f y‖ + lapse m ‖f y‖/‖f y‖ := by ring
    _ ≤ _ := add_le_add ha hb

lemma tangent_surface_tensor_trace {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : DifferentiableAt ℝ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) :
    parameterTensorTrace m f y = 2*velocity m ‖f y‖/‖f y‖ := by
  have hpos := cartMetric_pos hm hr
  have ha := firstFrame_unit _ _ hpos hinj
  have hb := secondFrame_unit _ _ hpos hinj
  have hta := maximum_radius_tangent hf hmax (firstFrame (cartMetric m (f y)) (fderiv ℝ f y))
  have htb := maximum_radius_tangent hf hmax (secondFrame (cartMetric m (f y)) (fderiv ℝ f y))
  rw [cartMetric_tangent m _ _ _ hta] at ha
  rw [cartMetric_tangent m _ _ _ htb] at hb
  dsimp [parameterTensorTrace]
  rw [cartTensor_tangent m _ _ _ hta,cartTensor_tangent m _ _ _ htb,ha,hb]
  ring

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceParameter
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_center [IsManifold I2 ∞ T] (F : T → E3) (p : T) :
    surfaceParameter F p ((extChartAt I2 p) p) = F p := by
  simp [surfaceParameter]
omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_smooth [IsManifold I2 ∞ T]
    {F : T → E3} (hF : ContMDiff I2 𝓘(ℝ,E3) ∞ F) (p : T) :
    ContDiffAt ℝ ∞ (surfaceParameter F p) ((extChartAt I2 p) p) := by
  have hh := (contMDiffAt_iff.mp (hF p)).2
  simpa only [surfaceParameter,I2,mfld_simps,chartAt_self_eq,Function.id_comp,contDiffWithinAt_univ] using hh

omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_derivative [IsManifold I2 ∞ T]
    {F : T → E3} (hF : ContMDiff I2 𝓘(ℝ,E3) ∞ F) (p : T) :
    fderiv ℝ (surfaceParameter F p) ((extChartAt I2 p) p) = mfderiv I2 𝓘(ℝ,E3) F p := by
  have hh : (mfderiv I2 𝓘(ℝ,E3) F p : E2 →L[ℝ] E3) =
      fderivWithin ℝ (writtenInExtChartAt I2 𝓘(ℝ,E3) p F) (range I2) ((extChartAt I2 p) p) :=
    ((hF p).mdifferentiableAt (by simp)).mfderiv
  simp only [surfaceParameter,I2,writtenInExtChartAt,mfld_simps,chartAt_self_eq,
    Function.id_comp,fderivWithin_univ] at hh ⊢
  exact hh.symm

lemma surfaceParameter_maximum {F : T → E3} {p : T}
    (hp : ∀ q : T, ‖F q‖^2 ≤ ‖F p‖^2) :
    IsLocalMax (fun z => ‖surfaceParameter F p z‖^2) ((extChartAt I2 p) p) := by
  apply Filter.Eventually.of_forall
  intro z
  change ‖surfaceParameter F p z‖^2 ≤ ‖surfaceParameter F p ((extChartAt I2 p) p)‖^2
  rw [surfaceParameter_center]
  exact hp ((extChartAt I2 p).symm z)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryBridge
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSMain
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric
  CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass

lemma constant_radius_hessian {f : E2 → E3} {y : E2}
    (hf : ContDiffAt ℝ ∞ f y) (hn : ∀ z, ‖f z‖ = ‖f y‖) (a : E2) :
    ⟪f y, fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ =
      -⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ := by
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => f (y+t•a)) 0 := by
    have hh : ContDiffAt ℝ ∞ f (y+(0:ℝ)•a) := by simpa using hf
    exact hh.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have he : (fun t : ℝ => ‖f (y+t•a)‖^2) = (fun _ : ℝ => ‖f y‖^2) :=
    funext (fun t => congrArg (fun r : ℝ => r^2) (hn (y+t•a)))
  have h := curve_normSq_second hc
  rw [he,line_second_deriv hf a,line_deriv (hf.differentiableAt (by simp)) a] at h
  simp only [deriv_const',deriv_const,zero_smul,add_zero] at h
  linarith

lemma constant_radius_second_form {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hn : ∀ z, ‖f z‖ = ‖f y‖) (hr : 2*m ≤ ‖f y‖)
    (a : E2) (ha : cartMetric m (f y) (fderiv ℝ f y a) (fderiv ℝ f y a) = 1) :
    parameterSecondForm m f y (radialNormal m (f y)) a a = lapse m ‖f y‖/‖f y‖ := by
  have hmax : IsLocalMax (fun z => ‖f z‖^2) y :=
    Filter.Eventually.of_forall (fun z => by dsimp; rw [hn z])
  have ht := maximum_radius_tangent (hf.differentiableAt (by simp)) hmax a
  have hau : ⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ = 1 := by
    rwa [cartMetric_tangent m _ _ _ ht] at ha
  have hh := constant_radius_hessian hf hn a
  rw [hau] at hh
  have hs : ⟪radialUnit (f y),fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ = -1/‖f y‖ := by
    simp only [radialUnit,real_inner_smul_left,hh,div_eq_mul_inv]
    ring
  rw [parameterSecondForm,metric_normal_pair hm hr,christoffel_tangent_radial hm hr _ _ ht ht,
    hau,mul_one,hs]
  have hu := lapse_pos hm hr
  have hp : 0 < ‖f y‖ := lt_of_lt_of_le (by positivity) hr
  field_simp
  ring

lemma constant_radius_mean {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hn : ∀ z, ‖f z‖ = ‖f y‖) (hr : 2*m ≤ ‖f y‖)
    (hi : Function.Injective (fderiv ℝ f y)) :
    parameterMeanCurvature m f y (radialNormal m (f y)) = 2*lapse m ‖f y‖/‖f y‖ := by
  have ha := constant_radius_second_form hm hf hn hr _ (firstFrame_unit _ _ (cartMetric_pos hm hr) hi)
  have hb := constant_radius_second_form hm hf hn hr _ (secondFrame_unit _ _ (cartMetric_pos hm hr) hi)
  dsimp only [parameterMeanCurvature]
  rw [ha,hb]
  ring

lemma schwarzschildMarginal {m : ℝ} (hm : 0 < m) :
    MarginalBoundary (smoothMetric hm) (tensorInner m) := by
  refine ⟨schwarzschildBoundary hm,?_⟩
  intro p
  let F : Boundary Exterior → E3 := position m ∘ Subtype.val
  let f := surfaceParameter F p
  let y := (extChartAt I2 p) p
  have hf := surfaceParameter_smooth ((position_smooth m).comp CKSBoundarySurface.inclusion_smooth) p
  change ContDiffAt ℝ ∞ f y at hf
  have hy : f y = position m p.val := surfaceParameter_center F p
  have hn (z : E2) : ‖f z‖ = 2*m := horizon_radius hm ((extChartAt I2 p).symm z)
  have hc : ∀ z, ‖f z‖ = ‖f y‖ := fun z => (hn z).trans (hn y).symm
  have hi : Function.Injective (fderiv ℝ f y) := by
    rw [surfaceParameter_derivative ((position_smooth m).comp CKSBoundarySurface.inclusion_smooth)]
    rw [mfderiv_comp p ((position_smooth m).mdifferentiable (by simp) _)
      (CKSBoundarySurface.inclusion_smooth.mdifferentiable (by simp) _)]
    exact (position_derivative_injective hm _).comp (CKSBoundarySurface.inclusion_mfderiv_injective p)
  have hr : 2*m ≤ ‖f y‖ := (hn y).ge
  have hH := constant_radius_mean hm hf hc hr hi
  have hmax : IsLocalMax (fun z => ‖f z‖^2) y :=
    Filter.Eventually.of_forall (fun z => by dsimp; rw [hc z])
  have hK := tangent_surface_tensor_trace hm (hf.differentiableAt (by simp)) hmax hr hi
  change parameterMeanCurvature m f y
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p)) + parameterTensorTrace m f y = 0
  rw [horizonNormal_coordinate hm p,← hy,hH,hK,hn y,lapse_horizon hm,velocity_near m _ (by linarith)]
  ring

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_MainDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

namespace InteriorSurface
variable {q : SmoothMetric I3 (M := N)} {k : InnerField I3 (M := N)}
  {A : CoefficientAtlas q k} {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T]
  [IsManifold I2 ∞ T] (D : InteriorSurface q k A T)

lemma ComponentwiseApparent.pointwise (h : D.ComponentwiseApparent) (p : T) :
    D.thetaPlus p = 0 ∨ D.thetaMinus p = 0 := by
  rcases h p with h | h
  · exact Or.inl (h p mem_connectedComponent)
  · exact Or.inr (h p mem_connectedComponent)

end InteriorSurface

attribute [local instance] sixteen_atLeastTwo

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma sphere_coordinate_integral (i : Fin 3) :
    (∫ n : Sphere, (n : E3) i ∂surfaceMeasure) = 0 := by
  let u : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.neg ℝ
  have h := (sphereHome_measurePreserving u).integral_comp
    (sphereHome u).measurableEmbedding (fun n : Sphere => (n : E3) i)
  change (∫ n : Sphere, -(n : E3) i ∂surfaceMeasure) = _ at h
  rw [integral_neg] at h
  linarith

lemma constant_bondi_charge (m : ℝ) : bondiCharge (fun _ => 4*m) = (m,0) := by
  apply Prod.ext
  · rw [charge_energy contMDiff_const,integral_const,CKSADM.surfaceMeasure_real]
    change (16*Real.pi)⁻¹ * ((4*Real.pi) * (4*m)) = m
    field_simp
    ring
  · apply PiLp.ext
    intro i
    rw [charge_momentum contMDiff_const,integral_const_mul,sphere_coordinate_integral]
    simp
lemma bondi_charge {m : ℝ} (hm : 0 < m) : bondiCharge (cksData hm).massAspect = (m,0) :=
  constant_bondi_charge m

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_RiemannianContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory CKSReplacementCompleteness
open scoped ContDiff Topology ENNReal
namespace CKSReplacementCompleteness
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
lemma scalar_edist_le_metricEDist (g : Metric I (M := M)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ,ℝ) 1 f)
    (hdf : ∀ x v, ‖mfderiv I 𝓘(ℝ,ℝ) f x v‖ ≤ tangentNorm I g x v) (x y : M) :
    edist (f x) (f y) ≤ metricEDist I g x y := by
  rw [metricEDist_eq]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ,ℝ)),riemannianEDist_def]
  let η : Path (f x) (f y) := γ.map hf.continuous
  have hη : ContMDiff (modelWithCornersEuclideanHalfSpace 1) 𝓘(ℝ,ℝ) 1 η := hf.comp hγ
  apply (iInf_le_of_le η (iInf_le _ hη)).trans
  apply lintegral_mono
  intro t
  change ‖mfderiv (modelWithCornersEuclideanHalfSpace 1) 𝓘(ℝ,ℝ) (f ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp t (hf.mdifferentiable (by simp) _) (hγ.mdifferentiable (by simp) _)]
  rw [ContinuousLinearMap.comp_apply,← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hdf _ _)

lemma complete_of_proper_scalar {X : Type*} [EMetricSpace X] {f : X → ℝ}
    (hcompact : ∀ c, IsCompact {x | f x ≤ c})
    (hf : ∀ x y, edist (f x) (f y) ≤ edist x y) : CompleteSpace X := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro s hs
  obtain ⟨N,hN⟩ := EMetric.cauchySeq_iff.mp hs 1 (by norm_num)
  have hbound : ∀ᶠ n in atTop, s n ∈ {x | f x ≤ f (s N)+1} := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd : edist (f (s n)) (f (s N)) < 1 := (hf _ _).trans_lt (hN n hn N le_rfl)
    have hreal : |f (s n)-f (s N)| < 1 := by
      simpa only [edist_dist,Real.dist_eq,ENNReal.ofReal_lt_one] using hd
    change f (s n) ≤ f (s N)+1
    linarith [(abs_lt.mp hreal).2]
  obtain ⟨x,hx,hlim⟩ := (hcompact (f (s N)+1)).isSeqCompact.exists_tendsto_of_frequently_mem
    hbound.frequently hs
  exact ⟨x,hlim⟩
end CKSReplacementCompleteness

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCompleteness
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSReplacementCompleteness
open scoped ContDiff Topology ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma velocity_abs_bound {m r : ℝ} (hr : 0 ≤ r) : |velocity m r| ≤ r+1 := by
  have h0 := Real.smoothTransition.nonneg (r-2*m-1)
  have h1 := Real.smoothTransition.le_one (r-2*m-1)
  have hl : -1 ≤ velocity m r := by
    unfold velocity
    nlinarith
  have hu : velocity m r ≤ r := by
    unfold velocity
    nlinarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma lapseSquared_bound {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    lapseSquared m r ≤ (r+2)^2 := by
  have hp : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hv := (sq_le_sq₀ (abs_nonneg (velocity m r)) (by linarith : 0 ≤ r+1)).mpr
    (velocity_abs_bound hp.le)
  rw [sq_abs] at hv
  have h := div_nonneg (by positivity : 0 ≤ 2*m) hp.le
  unfold lapseSquared
  nlinarith

lemma logRadius_smooth {m : ℝ} (hm : 0 < m) : ContMDiff I3 𝓘(ℝ,ℝ) ∞ (logRadius m) := by
  intro p
  show ContMDiffAt I3 𝓘(ℝ,ℝ) ∞ (Real.log ∘ fun q : Exterior => radius m q+2) p
  exact (Real.contDiffAt_log.mpr (ne_of_gt (by linarith [radius_pos hm p] : 0 < radius m p+2))).comp_contMDiffAt (f := fun q : Exterior => radius m q+2)
    ((radius_smooth m p).add contMDiffAt_const)
lemma mfderiv_logRadius {m : ℝ} (hm : 0 < m) (p : Exterior) :
    mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p = (radius m p+2)⁻¹ • firstCoordinate := by
  have hh := (((radius_smooth m p).mdifferentiableAt (by simp)).hasMFDerivAt).add
    (hasMFDerivAt_const (I := I3) (I' := 𝓘(ℝ,ℝ)) (2:ℝ) p)
  rw [mfderiv_radius] at hh
  have hl := (Real.hasDerivAt_log (ne_of_gt (by linarith [radius_pos hm p] : 0 < radius m p+2))).hasFDerivAt
  have he := (hl.hasMFDerivAt.comp p hh).mfderiv
  change mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p = _ at he
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  change (firstCoordinate v + 0) * ((radius m p+2)⁻¹) = (radius m p+2)⁻¹ * firstCoordinate v
  ring
lemma logRadius_derivative_bound {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    ‖mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p v‖ ≤
      tangentNorm I3 (smoothMetric hm).toContinuousRiemannianMetric p v := by
  rw [mfderiv_logRadius hm]
  rw [norm_tangentSpace_vectorSpace]
  change |(radius m p+2)⁻¹ * v 0| ≤ Real.sqrt (metricInner m p v v)
  have hr : 0 < radius m p+2 := by linarith [radius_pos hm p]
  have he : (radius m p+2)⁻¹ * v 0 = v 0/(radius m p+2) := by ring
  rw [he,← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [div_pow,metricInner_quad hm]
  have h := div_le_div_of_nonneg_left (sq_nonneg (v 0))
    (lapseSquared_pos hm (radius_ge m p)) (lapseSquared_bound hm (radius_ge m p))
  have hnn : 0 ≤ (radius m p)^2 * ‖ambientDerivative directionAmbient p v‖^2 := by positivity
  linarith
lemma logRadius_sublevel_compact {m : ℝ} (hm : 0 < m) (c : ℝ) :
    IsCompact {p : Exterior | logRadius m p ≤ c} := by
  have he : {p : Exterior | logRadius m p ≤ c} = {p | radius m p ≤ Real.exp c-2} := by
    ext p
    simp only [mem_ofPred_eq,logRadius]
    rw [Real.log_le_iff_le_exp (by linarith [radius_pos hm p])]
    constructor <;> intro h <;> linarith
  rw [he]
  exact radius_sublevel_compact m _

theorem source_complete {m : ℝ} (hm : 0 < m) :
    IsComplete I3 (smoothMetric hm).toContinuousRiemannianMetric := by
  let g := (smoothMetric hm).toContinuousRiemannianMetric
  let : EMetricSpace Exterior := metricSpace I3 g
  apply complete_of_proper_scalar (f := logRadius m)
  · exact logRadius_sublevel_compact hm
  · intro p q
    exact scalar_edist_le_metricEDist g ((logRadius_smooth hm).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (logRadius_derivative_bound hm) p q
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildOrientability
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma orientation_map_trans {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (f : V ≃ₗ[ℝ] W) (g : W ≃ₗ[ℝ] Z) (o : Orientation ℝ V (Fin 3)) :
    Orientation.map (Fin 3) g (Orientation.map (Fin 3) f o) =
      Orientation.map (Fin 3) (f.trans g) o := by
  induction o using Module.Ray.ind with | h a ha =>
  rfl

lemma orientation_map_inverse_eq (f g : E3 ≃L[ℝ] E3)
    (h : 0 < f.toContinuousLinearMap.det * g.toContinuousLinearMap.det)
    (o : Orientation ℝ E3 (Fin 3)) :
    Orientation.map (Fin 3) f.symm.toLinearEquiv o =
      Orientation.map (Fin 3) g.symm.toLinearEquiv o := by
  apply (Orientation.map (Fin 3) g.toLinearEquiv).injective
  rw [orientation_map_trans,orientation_map_trans]
  have he : g.symm.toLinearEquiv.trans g.toLinearEquiv = LinearEquiv.refl ℝ E3 := by ext; simp
  rw [he,Orientation.map_refl,Equiv.refl_apply]
  apply (Orientation.map_eq_iff_det_pos o _ (by simp [E3])).mpr
  change 0 < LinearMap.det (g.toLinearEquiv.toLinearMap.comp f.symm.toLinearEquiv.toLinearMap)
  rw [LinearMap.det_comp]
  have hf : f.toContinuousLinearMap.det ≠ 0 := f.toLinearEquiv.isUnit_det'.ne_zero
  have hi : LinearMap.det f.symm.toLinearEquiv.toLinearMap = (f.toContinuousLinearMap.det)⁻¹ := by
    exact (LinearEquiv.coe_inv_det f.toLinearEquiv).symm.trans (by simp only [Units.val_inv_eq_inv_val,LinearEquiv.coe_det]; rfl)
  rw [hi]
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_ne_zero hf)).mp
  have hc : (g.toContinuousLinearMap.det * (f.toContinuousLinearMap.det)⁻¹) *
      (f.toContinuousLinearMap.det)^2 = f.toContinuousLinearMap.det * g.toContinuousLinearMap.det := by
    field_simp
  change 0 * _ < (g.toContinuousLinearMap.det * (f.toContinuousLinearMap.det)⁻¹) * (f.toContinuousLinearMap.det)^2
  rwa [zero_mul,hc]

theorem source_orientable : CKSSourceExterior.Orientable (N := Exterior) := by
  let O : Orientation ℝ E3 (Fin 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation
  let o := fun p : Exterior => Orientation.map (Fin 3) (positionTangentEquiv p).symm.toLinearEquiv O
  refine ⟨o,?_⟩
  intro x
  let e := trivializationAt E3 (TangentSpace I3) x
  let A : Exterior → E3 →L[ℝ] E3 := fun y =>
    (positionTangentEquiv y).toContinuousLinearMap.comp (e.symmL ℝ y)
  have hs : ContinuousAt A x := by
    convert (CKSSpatialManifold.mfderiv_gauge_smooth (I := I3) (position_smooth 1 x)).continuousAt using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    ext v
    rfl
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E3 (TangentSpace I3) x
  let B := fun y (hy : y ∈ e.baseSet) => (e.continuousLinearEquivAt ℝ y hy).symm.trans (positionTangentEquiv y)
  have hB : ∀ y hy, (B y hy).toContinuousLinearMap = A y := by
    intro y hy
    ext v
    simp only [B,A,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.trans_apply,ContinuousLinearMap.comp_apply]
    rw [Trivialization.symmL_apply e hy]
    rfl
  have hd : (A x).det ≠ 0 := by
    rw [← hB x hx]
    exact (B x hx).toLinearEquiv.isUnit_det'.ne_zero
  have hc := (ContinuousLinearMap.continuous_det.continuousAt.comp hs).mul_const (A x).det
  have hev : ∀ᶠ y in 𝓝 x, 0 < (A y).det * (A x).det :=
    hc.eventually (lt_mem_nhds (mul_self_pos.mpr hd))
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (hev.and (e.open_baseSet.mem_nhds hx))
  refine ⟨V,hVo,hxV,fun y hy => (hV hy).2,?_⟩
  intro y hy
  change Orientation.map (Fin 3) (e.continuousLinearEquivAt ℝ y (hV hy).2).toLinearEquiv
      (Orientation.map (Fin 3) (positionTangentEquiv y).symm.toLinearEquiv O) =
    Orientation.map (Fin 3) (e.continuousLinearEquivAt ℝ x (hV hxV).2).toLinearEquiv
      (Orientation.map (Fin 3) (positionTangentEquiv x).symm.toLinearEquiv O)
  rw [orientation_map_trans,orientation_map_trans]
  exact orientation_map_inverse_eq (B y (hV hy).2) (B x (hV hxV).2)
    (by rw [hB,hB]; exact (hV hy).1) O
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildSpacetimeRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance instIsBoundedSMulRealSpacetimeBilinear : IsBoundedSMul ℝ SpacetimeBilinear :=
  @NormedSpace.toIsBoundedSMul ℝ SpacetimeBilinear _ _ _

lemma advancedMetric_smoothAt (m : ℝ) {z : Spacetime} (hx : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ (advancedMetric m) z := by
  have hsp : ContDiffAt ℝ ∞ (fun y : Spacetime => y.2) z := contDiffAt_snd
  have hn := (contDiffAt_norm ℝ hx).comp z hsp (n := ∞)
  have hH : ContDiffAt ℝ ∞ (fun y : Spacetime => schwarzschildH m ‖y.2‖) z :=
    contDiffAt_const.sub (contDiffAt_const.div hn (norm_ne_zero_iff.mpr hx))
  have hR : ContDiffAt ℝ ∞ (fun y : Spacetime => radiusForm y.2) z := by
    exact (((innerSL ℝ).contDiff.contDiffAt.comp z ((radialUnit_smoothAt hx).comp z hsp)).clm_comp contDiffAt_const)
  exact ((((hH.neg.smul contDiffAt_const).add (contDiffAt_const.smulRight hR)).add
    (hR.smulRight contDiffAt_const)).add contDiffAt_const).sub (hR.smulRight hR)

lemma advancedMetric_symm (m : ℝ) (z a b : Spacetime) :
    advancedMetric m z a b = advancedMetric m z b a := by
  rw [advancedMetric_apply,advancedMetric_apply,real_inner_comm a.2 b.2]
  ring

lemma advancedMetric_nondegenerate (m : ℝ) {z : Spacetime} (hx : z.2 ≠ 0)
    (a : Spacetime) (ha : ∀ b : Spacetime, advancedMetric m z a b = 0) : a = 0 := by
  have hr := ha (0,radialUnit z.2)
  rw [advancedMetric_apply] at hr
  simp only [mul_zero,zero_mul,zero_add,add_zero,radialUnit_inner_self hx,mul_one,
    real_inner_comm a.2 (radialUnit z.2)] at hr
  have ht : a.1 = 0 := by linarith
  have ht' := ha (1,0)
  rw [advancedMetric_apply] at ht'
  simp only [ht,zero_mul,inner_zero_right,mul_zero,zero_add,add_zero,one_mul,sub_zero] at ht'
  have hb := ha (0,a.2)
  rw [advancedMetric_apply] at hb
  simp only [ht,ht',zero_add,mul_zero,sub_zero] at hb
  have ha2 : a.2 = 0 := (inner_self_eq_zero).mp hb
  exact Prod.ext ht ha2

lemma advancedGraph_injective (m : ℝ) : Function.Injective (advancedGraph m) := by
  intro x y h
  exact congrArg Prod.snd h

lemma advancedTime_horizon (m : ℝ) : advancedTime m (2*m) = 0 := by
  simp [advancedTime]
lemma advancedSlope_horizon {m : ℝ} (hm : 0 < m) : advancedSlope m (2*m) = 1/2 := by
  rw [advancedSlope,lapse_horizon hm,velocity_near m (2*m) (by linarith)]
  norm_num
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSSpatialManifold CKSMetricGluing CKSLorentz
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma horizon_regular_graph {m : ℝ} (hm : 0 < m) : HorizonRegularGraph m where
  ambient_smooth := fun _ hx => advancedMetric_smoothAt m hx
  ambient_symmetric := advancedMetric_symm m
  ambient_nondegenerate := fun _ hx => advancedMetric_nondegenerate m hx
  graph_smooth_across := fun _ hx => advancedGraph_smooth hm hx
  graph_injective := advancedGraph_injective m
  graph_derivative := fun _ hx => advancedGraph_derivative hm hx
  horizon_time := advancedTime_horizon m
  horizon_slope := advancedSlope_horizon hm
  induced_metric := fun _ hx => graph_induced_metric hm hx
  normal_unit := fun _ hx => futureNormal_unit hm hx
  normal_orthogonal := fun _ hx => futureNormal_orthogonal hm hx
  future_facing := fun _ hx => futureNormal_future hm hx
  induced_second_form := fun _ hx => graph_induced_second_form hm hx

lemma source_boundary_nonempty : (I3.boundary Exterior).Nonempty := by
  let n : Sphere := ⟨EuclideanSpace.single 0 1,by simp⟩
  exact ⟨(boundarySphere.symm n).val,(boundarySphere.symm n).property⟩
lemma source_boundary_connected : ConnectedSpace (Boundary Exterior) := by
  let : ConnectedSpace Sphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ E3) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  exact boundarySphere.symm.connectedSpace_iff.mp inferInstance
lemma source_boundary_theta {m : ℝ} (hm : 0 < m) (p : Exterior) (hp : p ∈ I3.boundary Exterior) :
    sphereThetaPlus m (position m p) = 0 := by
  apply horizon_expansion hm
  rw [norm_position hm]
  have hh := (boundary_iff p).mp hp
  change 2*m+p.1.val = 2*m
  rw [hh,add_zero]

theorem schwarzschild_equality_example {m : ℝ} (hm : 0 < m) :
    SchwarzschildEqualityExample m hm where
  connected := inferInstance
  orientable := source_orientable
  boundary_nonempty := source_boundary_nonempty
  boundary_compact := boundary_compact
  boundary_connected := source_boundary_connected
  smooth_tensor := tensorInner_smooth hm
  symmetric_tensor := tensorInner_symm m
  complete := source_complete hm
  dec := physical_DEC hm
  exterior_CKS := ⟨cksData hm⟩
  bondi := bondi_charge hm
  timelike := by rw [bondi_charge hm]; simpa using hm
  horizon_regular := horizon_regular_graph hm
  boundary_normal_unit := fun _ hx => radialNormal_unit hm hx
  boundary_normal_orthogonal := fun _ _ hx => radialNormal_orthogonal m hx
  boundary_normal_points_into_end := fun _ hx => radialNormal_points_out hm hx
  boundary_theta_plus := source_boundary_theta hm
  full_cut_area := source_minimum_area hm
  positive_area := by rw [source_minimum_area hm]; positivity
  equality := numerical_equality hm
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildHorizonExclusion
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma local_surface_barrier {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m < ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) (N : E3)
    (hunit : cartMetric m (f y) N N = 1)
    (horth : ∀ a, cartMetric m (f y) N (fderiv ℝ f y a) = 0) :
    |parameterTensorTrace m f y| < |parameterMeanCurvature m f y N| := by
  have hd := hf.differentiableAt (by simp)
  have hh := outward_surface_mean_bound hm hf hmax hr.le hinj
  have ht := tangent_surface_tensor_trace hm hd hmax hr.le hinj
  have hp : 0 < ‖f y‖ := lt_trans (by positivity) hr
  have hu := lapse_dominates_velocity hm hr
  have hs : |parameterTensorTrace m f y| < parameterMeanCurvature m f y (radialNormal m (f y)) := by
    apply lt_of_lt_of_le _ hh
    rw [ht,abs_div,abs_mul,abs_of_pos hp]
    norm_num
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hu (by norm_num)) hp
  rcases normal_radial_at_tangent hm hr.le _ hinj (maximum_radius_tangent hd hmax) N hunit horth with hN | hN
  · rw [hN]
    exact lt_of_lt_of_le hs (le_abs_self _)
  · rw [hN,parameterMeanCurvature_neg,abs_neg]
    exact lt_of_lt_of_le hs (le_abs_self _)

universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

theorem closed_surface_barrier {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : InteriorImmersion m T) :
    ∃ p, |surfaceTensorTrace m D.map p| < |surfaceMeanCurvature m D.map D.normal p| := by
  have hc : Continuous (fun p => ‖D.map p‖^2) := D.smooth.continuous.norm.pow 2
  obtain ⟨p,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  refine ⟨p,?_⟩
  unfold surfaceTensorTrace surfaceMeanCurvature
  apply local_surface_barrier hm (surfaceParameter_smooth D.smooth p)
    (surfaceParameter_maximum (fun q => hmax (Set.mem_univ q)))
  · simpa only [surfaceParameter_center] using D.interior p
  · rw [surfaceParameter_derivative D.smooth p]
    exact D.immersion p
  · simpa only [surfaceParameter_center] using D.normal_unit p
  · intro a
    rw [surfaceParameter_center,surfaceParameter_derivative D.smooth p]
    exact D.normal_orthogonal p a

theorem no_closed_apparent_horizon {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : InteriorImmersion m T) :
    ¬ (∀ p, surfaceMeanCurvature m D.map D.normal p + surfaceTensorTrace m D.map p = 0 ∨
      surfaceMeanCurvature m D.map D.normal p - surfaceTensorTrace m D.map p = 0) := by
  obtain ⟨p,hp⟩ := closed_surface_barrier hm D
  intro hh
  rcases hh p with hp' | hp'
  · have he : surfaceMeanCurvature m D.map D.normal p = -surfaceTensorTrace m D.map p := by linarith
    rw [he,abs_neg] at hp
    exact (lt_irrefl _ hp)
  · have he : surfaceMeanCurvature m D.map D.normal p = surfaceTensorTrace m D.map p := by linarith
    rw [he] at hp
    exact (lt_irrefl _ hp)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildIntrinsicEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

theorem no_intrinsic_closed_apparent_horizon {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : IntrinsicInteriorImmersion m T) :
    ¬ (∀ p, intrinsicSurfaceMeanCurvature D p + intrinsicSurfaceTensorTrace D p = 0 ∨
      intrinsicSurfaceMeanCurvature D p - intrinsicSurfaceTensorTrace D p = 0) := by
  exact no_closed_apparent_horizon hm (D.coordinateImmersion hm)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_MainProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
open CKSSchwarzschild

lemma schwarzschild_no_additional_horizons {m : ℝ} (hm : 0 < m) :
    NoAdditionalHorizons.{0,v} (smoothMetric hm) (tensorInner m)
      (cksData hm).chart (schwarzschildAtlas hm) := by
  intro T _ _ _ _ _ _ _ D _ h
  apply no_intrinsic_closed_apparent_horizon hm (D.schwarzschildImmersion hm)
  intro p
  exact InteriorSurface.ComponentwiseApparent.pointwise D h p

lemma schwarzschild_attainment {m : ℝ} (hm : 0 < m) :
    SchwarzschildAttainment.{v} m hm := by
  have h := schwarzschild_equality_example hm
  refine ⟨{
    smooth_tensor := h.smooth_tensor
    symmetric_tensor := h.symmetric_tensor
    orientable := h.orientable
    boundary_compact := h.boundary_compact
    boundary_nonempty := h.boundary_nonempty
    complete := h.complete
    dec := h.dec
    timelike := h.timelike
    boundary_connected := h.boundary_connected
    boundary_marginal := schwarzschildMarginal hm
    positive_area := h.positive_area
    no_horizons := schwarzschild_no_additional_horizons hm },
    h.horizon_regular,?_,h.full_cut_area,h.equality⟩
  rw [bondiMass,h.bondi]
  simpa using Real.sqrt_sq hm.le

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ComparatorMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
universe u v
attribute [local instance] manifold_regular sixteen_atLeastTwo

theorem schwarzschild_equality_examples_oai (m : ℝ) (hm : 0 < m) :
    SchwarzschildExample.{v} m hm := by
  exact ⟨CKSSchwarzschild.smoothMetric hm, CKSSchwarzschild.cksData hm,
    schwarzschildAtlas hm, fun _ => rfl, schwarzschild_attainment hm⟩


end CKSMain
end
end OAI
end

theorem solution.{v} : type_of% @OAI.CKSMain.schwarzschild_equality_examples_oai.{v} := @OAI.CKSMain.schwarzschild_equality_examples_oai.{v}
