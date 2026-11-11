-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_defect_combination
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:35:16.087685+00:00
-- url     : https://prove2.me/submissions/d7546c09-3082-477c-b0dc-cae489f6c8d3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_nonharmonic_logSource_compact
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_nonharmonic_sqrtSource_compact

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma invariantPart_add_antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) :
    invariantPart J α + antiInvariantPart J α = α := by
  unfold invariantPart antiInvariantPart
  module

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGeometricCenter
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma hermitianCenterExtension_eq {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {b : Space} (hφb : φ b = 1) :
    hermitianCenterExtension J p D hφ hc hφD b = coordinateJ J p b := by
  simp only [hermitianCenterExtension,SchwartzCutoff.schwartz_apply,hφb,one_smul]

lemma hermitianCenterExtension_square {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {b : Space} (hφb : φ b = 1) (v : Space) :
    hermitianCenterExtension J p D hφ hc hφD b
      (hermitianCenterExtension J p D hφ hc hφD b v) = -v := by
  have hb : b ∈ D.domain := hφD (subset_tsupport φ (by simp [Function.mem_support,hφb]))
  rw [hermitianCenterExtension_eq J p D hφ hc hφD hφb]
  exact coordinateJ_square J p (D.domain_subset hb) v

end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstOrderAntiDdc
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extDeriv_dc_apply {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) (hJ : DifferentiableAt ℝ J x) (u v : E) :
    extDeriv (dc J f) x ![u,v] =
      -(fderiv ℝ (fderiv ℝ f) x u (J x v)) + fderiv ℝ (fderiv ℝ f) x v (J x u) +
      fderiv ℝ f x ((fderiv ℝ J x v) u - (fderiv ℝ J x u) v) := by
  let L := (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp x ((hdf.hasFDerivAt.clm_comp hJ.hasFDerivAt).neg)
  have hd : fderiv ℝ (dc J f) x =
      L.comp (-((ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp (fderiv ℝ J x) +
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J x)).comp (fderiv ℝ (fderiv ℝ f) x))) :=
    h.fderiv
  rw [extDeriv_one,hd]
  simp [L,ofSubsingletonLIE,map_sub]
  ring

end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldComplexDifferential
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_ddc (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    pullback (exteriorDerivative (complexDifferential J f)) (extChartAt Model p).symm z =
      extDeriv (ExteriorForms.dc (coordinateJ J p) (f ∘ (extChartAt Model p).symm)) z := by
  rw [pullback_exteriorDerivative _ (complexDifferential_smooth J hf) (isOpen_extChartAt_target p)
    (contMDiffOn_extChartAt_symm p) hz,extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
  exact pullback_complexDifferential J hf p hy

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiDdcBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma logPotential_hessian {s : ℝ} (hs : 0 < s) (z u v : E) :
    fderiv ℝ (fderiv ℝ (logPotential s)) z u v =
      ⟪u,v⟫/(s^2+‖z‖^2) - 2*⟪z,u⟫*⟪z,v⟫/(s^2+‖z‖^2)^2 := by
  have he : fderiv ℝ (logPotential s) = fun z : E => (s^2+‖z‖^2)⁻¹ • innerSL ℝ z :=
    funext (logPotential_fderiv hs)
  rw [he]
  have hi := (hasDerivAt_inv (ne_of_gt (radial_sq_pos hs z))).comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2))
  have h := hi.smul ((innerSL ℝ (E := E)).hasFDerivAt (x := z))
  change HasFDerivAt (fun z : E => (s^2+‖z‖^2)⁻¹ • innerSL ℝ z) _ z at h
  rw [h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,Function.comp_apply,Nat.cast_ofNat]
  change (s^2+‖z‖^2)⁻¹ * ⟪u,v⟫ + (-((s^2+‖z‖^2)^2)⁻¹ * (2*⟪z,u⟫))*⟪z,v⟫ = _
  ring

lemma sqrtPotential_hessian {s : ℝ} (hs : 0 < s) (z u v : E) :
    fderiv ℝ (fderiv ℝ (sqrtPotential s)) z u v =
      ⟪u,v⟫/Real.sqrt (s^2+‖z‖^2) -
        ⟪z,u⟫*⟪z,v⟫/(Real.sqrt (s^2+‖z‖^2))^3 := by
  have he : fderiv ℝ (sqrtPotential s) =
      fun z : E => (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z :=
    funext (sqrtPotential_fderiv hs)
  rw [he]
  have hi := (hasDerivAt_inv (ne_of_gt (Real.sqrt_pos.2 (radial_sq_pos hs z)))).comp_hasFDerivAt z
    (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).sqrt
    (ne_of_gt (radial_sq_pos hs z)))
  have h := hi.smul ((innerSL ℝ (E := E)).hasFDerivAt (x := z))
  change HasFDerivAt (fun z : E => (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z) _ z at h
  rw [h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,Function.comp_apply,Nat.cast_ofNat]
  change (Real.sqrt (s^2+‖z‖^2))⁻¹ * ⟪u,v⟫ +
    (-((Real.sqrt (s^2+‖z‖^2))^2)⁻¹ * ((1/(2*Real.sqrt (s^2+‖z‖^2)))*(2*⟪z,u⟫)))*⟪z,v⟫ = _
  ring
end TamingCompatibility.RadialPotential

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TwoDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma two_direction_inner_sq_le (z u v : E) (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ⟪z,u⟫^2 + ⟪z,v⟫^2 ≤ ‖z‖^2*‖u‖^2 := by
  by_cases hu : u = 0
  · have hv0 : v = 0 := norm_eq_zero.mp (by simpa [hu] using hv)
    simp [hu,hv0]
  have hu2 : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hvu : ⟪v,u⟫ = 0 := by rw [real_inner_comm,huv]
  have hzu : ⟪u,z⟫ = ⟪z,u⟫ := real_inner_comm _ _
  have hzv : ⟪v,z⟫ = ⟪z,v⟫ := real_inner_comm _ _
  have h : 0 ≤ ⟪‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v,
    ‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v⟫ := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    huv,hvu,hzu,hzv] at h
  simp only [real_inner_self_eq_norm_sq,hv] at h
  nlinarith
end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sqrtPotential_trace_lower {s : ℝ} (hs : 0 < s) (z u v : E)
    (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ‖u‖^2/Real.sqrt (s^2+‖z‖^2) ≤
      fderiv ℝ (fderiv ℝ (sqrtPotential s)) z u u +
      fderiv ℝ (fderiv ℝ (sqrtPotential s)) z v v := by
  have hA := radial_sq_pos hs z
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have hS := two_direction_inner_sq_le z u v huv hv
  rw [sqrtPotential_hessian hs,sqrtPotential_hessian hs,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv]
  calc
    _ = ((Real.sqrt (s^2+‖z‖^2))^2 * ‖u‖^2)/(Real.sqrt (s^2+‖z‖^2))^3 := by
      field_simp
    _ ≤ (2*(Real.sqrt (s^2+‖z‖^2))^2*‖u‖^2 -
      (⟪z,u⟫^2+⟪z,v⟫^2))/(Real.sqrt (s^2+‖z‖^2))^3 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hq 3)).mpr
      rw [hq2]
      nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg ‖u‖)]
    _ = _ := by field_simp <;> ring
end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma constant_ddc_trace (J : E →L[ℝ] E) (hJJ : ∀ v, J (J v) = -v)
    {f : E → ℝ} {z : E} (hdf : DifferentiableAt ℝ (fderiv ℝ f) z) (v : E) :
    extDeriv (ExteriorForms.dc (fun _ => J) f) z ![v,J v] =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (J v) (J v) := by
  rw [ExteriorForms.extDeriv_dc_apply hdf (differentiableAt_const J)]
  have hzero : fderiv ℝ (fun _ : E => J) z = 0 := (hasFDerivAt_const J z).fderiv
  simp [hJJ, hzero]

end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma bilinear_diagonal_difference (H : E →L[ℝ] E →L[ℝ] ℝ)
    (J K : E →L[ℝ] E) (v : E) :
    ‖H (J v) (J v) - H (K v) (K v)‖ ≤
      ‖H‖ * ‖J-K‖ * (‖J‖+‖K‖) * ‖v‖^2 := by
  have heq : H (J v) (J v) - H (K v) (K v) =
      H ((J-K) v) (J v) + H (K v) ((J-K) v) := by
    simp only [_root_.sub_apply,map_sub]
    ring
  rw [heq]
  calc
    _ ≤ ‖H ((J-K) v) (J v)‖ + ‖H (K v) ((J-K) v)‖ := norm_add_le _ _
    _ ≤ ‖H‖*‖(J-K) v‖*‖J v‖ + ‖H‖*‖K v‖*‖(J-K) v‖ :=
      add_le_add (H.le_opNorm₂ _ _) (H.le_opNorm₂ _ _)
    _ ≤ ‖H‖*(‖J-K‖*‖v‖)*(‖J‖*‖v‖) + ‖H‖*(‖K‖*‖v‖)*(‖J-K‖*‖v‖) := by
      gcongr
      · exact (J-K).le_opNorm v
      · exact J.le_opNorm v
      · exact K.le_opNorm v
      · exact (J-K).le_opNorm v
    _ = _ := by ring

lemma ddc_gradient_bound (p : E →L[ℝ] ℝ) (D : E →L[ℝ] E →L[ℝ] E)
    (J : E →L[ℝ] E) (v : E) :
    ‖p (D (J v) v - D v (J v))‖ ≤ 2*‖p‖*‖D‖*‖J‖*‖v‖^2 := by
  calc
    _ ≤ ‖p‖ * ‖D (J v) v - D v (J v)‖ := p.le_opNorm _
    _ ≤ ‖p‖ * (‖D (J v) v‖ + ‖D v (J v)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖p‖ * (‖D‖*‖J v‖*‖v‖ + ‖D‖*‖v‖*‖J v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (D.le_opNorm₂ _ _) (D.le_opNorm₂ _ _)) (norm_nonneg _)
    _ ≤ ‖p‖ * (‖D‖*(‖J‖*‖v‖)*‖v‖ + ‖D‖*‖v‖*(‖J‖*‖v‖)) := by
      gcongr <;> exact J.le_opNorm v
    _ = _ := by ring

lemma ddc_perturbation_bound {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {f : E → ℝ} {z : E} (hdf : DifferentiableAt ℝ (fderiv ℝ f) z)
    (hJ : DifferentiableAt ℝ J z) (hJJ : ∀ v, J z (J z v) = -v)
    (hKK : ∀ v, K (K v) = -v) (v : E) :
    ‖extDeriv (ExteriorForms.dc J f) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) f) z ![v,K v]‖ ≤
      (‖fderiv ℝ (fderiv ℝ f) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ f z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 := by
  rw [ExteriorForms.extDeriv_dc_apply hdf hJ,constant_ddc_trace K hKK hdf,hJJ]
  simp only [map_neg,neg_neg]
  have heq :
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (J z v) (J z v) +
        fderiv ℝ f z ((fderiv ℝ J z (J z v)) v - (fderiv ℝ J z v) (J z v)) -
        (fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (K v) (K v)) =
      (fderiv ℝ (fderiv ℝ f) z (J z v) (J z v) - fderiv ℝ (fderiv ℝ f) z (K v) (K v)) +
        fderiv ℝ f z ((fderiv ℝ J z (J z v)) v - (fderiv ℝ J z v) (J z v)) := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖*‖J z-K‖*(‖J z‖+‖K‖)*‖v‖^2 +
      2*‖fderiv ℝ f z‖*‖fderiv ℝ J z‖*‖J z‖*‖v‖^2 :=
        add_le_add (bilinear_diagonal_difference _ _ _ _) (ddc_gradient_bound _ _ _ _)
    _ = _ := by ring
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_logPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (logPotential s) z‖ ≤ 2/(s+‖z‖) := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [logPotential_fderiv hs]
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,norm_mul,
    norm_inv,Real.norm_of_nonneg (le_of_lt hA)]
  calc
    _ ≤ (s^2+‖z‖^2)⁻¹ * (‖z‖*‖v‖) := by
      gcongr; exact norm_inner_le_norm _ _
    _ = (‖z‖/(s^2+‖z‖^2))*‖v‖ := by ring
    _ ≤ (2/(s+‖z‖))*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply (div_le_div_iff₀ hA ha).mpr
      nlinarith [sq_nonneg (s-‖z‖)]

lemma norm_sqrtPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (sqrtPotential s) z‖ ≤ 1 := by
  have hA := radial_sq_pos hs z
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have ht : ‖z‖ ≤ Real.sqrt (s^2+‖z‖^2) := by nlinarith [sq_nonneg s,norm_nonneg z]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [sqrtPotential_fderiv hs]
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,norm_mul,
    norm_inv,Real.norm_of_nonneg (le_of_lt hq),one_mul]
  calc
    _ ≤ (Real.sqrt (s^2+‖z‖^2))⁻¹ * (‖z‖*‖v‖) := by
      gcongr; exact norm_inner_le_norm _ _
    _ ≤ (Real.sqrt (s^2+‖z‖^2))⁻¹ * (Real.sqrt (s^2+‖z‖^2)*‖v‖) := by gcongr
    _ = _ := by field_simp

lemma norm_logPotential_hessian {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (logPotential s)) z‖ ≤ 6/(s+‖z‖)^2 := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [logPotential_hessian hs]
  calc
    _ ≤ ‖⟪u,v⟫/(s^2+‖z‖^2)‖ + ‖2*⟪z,u⟫*⟪z,v⟫/(s^2+‖z‖^2)^2‖ := norm_sub_le _ _
    _ = ‖⟪u,v⟫‖/(s^2+‖z‖^2) + 2*‖⟪z,u⟫‖*‖⟪z,v⟫‖/(s^2+‖z‖^2)^2 := by
      simp only [norm_div,norm_mul,norm_pow,Real.norm_of_nonneg (le_of_lt hA)]
      norm_num
    _ ≤ (‖u‖*‖v‖)/(s^2+‖z‖^2) + 2*(‖z‖*‖u‖)*(‖z‖*‖v‖)/(s^2+‖z‖^2)^2 := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ = (1/(s^2+‖z‖^2)+2*‖z‖^2/(s^2+‖z‖^2)^2)*‖u‖*‖v‖ := by ring
    _ ≤ (3/(s^2+‖z‖^2))*‖u‖*‖v‖ := by
      gcongr
      apply (le_div_iff₀ hA).mpr
      field_simp
      nlinarith [sq_nonneg s]
    _ ≤ (6/(s+‖z‖)^2)*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
      apply (div_le_div_iff₀ hA (pow_pos ha 2)).mpr
      nlinarith [sq_nonneg (s-‖z‖)]

lemma norm_sqrtPotential_hessian {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (sqrtPotential s)) z‖ ≤ 4/(s+‖z‖) := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have hqa : s+‖z‖ ≤ 2*Real.sqrt (s^2+‖z‖^2) := by
    nlinarith [sq_nonneg (s-‖z‖)]
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [sqrtPotential_hessian hs]
  calc
    _ ≤ ‖⟪u,v⟫/Real.sqrt (s^2+‖z‖^2)‖ +
      ‖⟪z,u⟫*⟪z,v⟫/(Real.sqrt (s^2+‖z‖^2))^3‖ := norm_sub_le _ _
    _ = ‖⟪u,v⟫‖/Real.sqrt (s^2+‖z‖^2) +
      ‖⟪z,u⟫‖*‖⟪z,v⟫‖/(Real.sqrt (s^2+‖z‖^2))^3 := by
        simp only [norm_div,norm_mul,norm_pow,Real.norm_of_nonneg (le_of_lt hq)]
    _ ≤ (‖u‖*‖v‖)/Real.sqrt (s^2+‖z‖^2) +
      (‖z‖*‖u‖)*(‖z‖*‖v‖)/(Real.sqrt (s^2+‖z‖^2))^3 := by
        gcongr <;> exact norm_inner_le_norm _ _
    _ = (1/Real.sqrt (s^2+‖z‖^2)+‖z‖^2/(Real.sqrt (s^2+‖z‖^2))^3)*‖u‖*‖v‖ := by ring
    _ ≤ (2/Real.sqrt (s^2+‖z‖^2))*‖u‖*‖v‖ := by
      gcongr
      apply (le_div_iff₀ hq).mpr
      field_simp
      nlinarith [sq_nonneg s]
    _ ≤ (4/(s+‖z‖))*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
      apply (div_le_div_iff₀ hq ha).mpr
      linarith
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma log_error_coefficient {a t L M : ℝ} (ha : 0 < a) (ht : t ≤ a)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    6/a^2*(L*t)*(M+M)+2*(2/a)*L*M ≤ 16*L*M/a := by
  apply (le_div_iff₀ ha).mpr
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hL hM) (sub_nonneg.mpr ht)]

lemma sqrt_error_coefficient {a t L M : ℝ} (ha : 0 < a) (ht : t ≤ a)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    4/a*(L*t)*(M+M)+2*1*L*M ≤ 10*L*M := by
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hL hM) (sub_nonneg.mpr ht)]

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel 

lemma eval_antiInvariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = 0 := by
  have h := congrArg (fun β => eval β x v (J.endomorphism x v))
    (invariantPart_add_antiInvariantPart J α)
  change eval (invariantPart J α) x v (J.endomorphism x v) +
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = _ at h
  rw [eval_invariantPart_complexLine] at h
  linarith

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_apply
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) :
    (closedLiftOfInverse A J α hs ht H Gs f).val =
      (fun a b : TwoForm X => a+b) (exteriorDerivative (codifferential J α ht (Gs f).val.val)) (H f).val.val := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLiftOfInverse_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (x : X) (v : TangentSpace Model x) :
    eval (closedLiftOfInverse A J α hs ht H Gs f).val x v (J.endomorphism x v) =
      eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) := by
  rw [closedLiftOfInverse_apply]
  change eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) +
    eval (H f).val.val x v (J.endomorphism x v) = _
  rw [← (H f).property,eval_antiInvariantPart_complexLine,add_zero]

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ScalarChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarChartLift_apply_inverse (p : X) (f : Space → ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    scalarChartLift p f ((extChartAt Model p).symm z) = f z := by
  classical
  simp only [scalarChartLift,ite_eq_left ((extChartAt Model p).map_target hz),
    (extChartAt Model p).right_inv hz]

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianRadialProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hermitianGraph_complex_pair (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v) (v : E) :
    ⟪hermitianGraph K v, hermitianGraph K (K v)⟫ = 0 ∧
      ‖hermitianGraph K (K v)‖ = ‖hermitianGraph K v‖ := by
  constructor
  · rw [hermitianGraph_inner,hK,inner_neg_right,real_inner_comm]
    ring
  · have he : ‖hermitianGraph K (K v)‖^2 = ‖hermitianGraph K v‖^2 := by
      rw [hermitianGraph_norm_sq,hermitianGraph_norm_sq,hK,norm_neg]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma linear_pullback_hessian (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => f (L x))) z u v =
      fderiv ℝ (fderiv ℝ f) (L z) (L u) (L v) := by
  have he : fderiv ℝ (fun x => f (L x)) = fun x => (fderiv ℝ f (L x)).comp L := by
    funext x
    simpa only [L.fderiv] using fderiv_fun_comp x (hf.differentiable (by simp) _) L.differentiableAt
  have hf' := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd := ((hf' (L z)).hasFDerivAt.comp z L.hasFDerivAt).clm_comp (hasFDerivAt_const L z)
  dsimp only [Function.comp_def] at hd
  rw [he,hd.fderiv]
  simp

lemma hermitianSqrt_ddc_lower (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v)
    {s : ℝ} (hs : 0 < s) (z v : E) :
    (‖v‖^2+‖K v‖^2)/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianSqrtPotential K s)) z ![v,K v] := by
  have hc := hermitianSqrtPotential_smooth K hs
  have hd : DifferentiableAt ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  rw [constant_ddc_trace K hK hd]
  change _ ≤ fderiv ℝ (fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x))) z v v +
    fderiv ℝ (fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x))) z (K v) (K v)
  rw [linear_pullback_hessian _ (sqrtPotential_smooth hs),
    linear_pullback_hessian _ (sqrtPotential_smooth hs)]
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := sqrtPotential_trace_lower hs (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  simpa only [hermitianGraph_norm_sq,add_assoc] using h

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma schwartz_fderiv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (W : 𝓢(E,F)) (z : E) :
    ‖fderiv ℝ W z‖ ≤ SchwartzMap.seminorm ℝ 0 1 W := by
  simpa only [norm_iteratedFDeriv_one] using W.norm_iteratedFDeriv_le_seminorm ℝ 1 z

lemma schwartz_difference_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (W : 𝓢(E,F)) (z b : E) :
    ‖W z-W b‖ ≤ SchwartzMap.seminorm ℝ 0 1 W * ‖z-b‖ := by
  have h := lipschitzWith_of_nnnorm_fderiv_le (W.smooth ⊤ |>.differentiable (by simp))
    (C := ⟨SchwartzMap.seminorm ℝ 0 1 W, apply_nonneg _ _⟩)
    (fun z => schwartz_fderiv_bound W z)
  exact h.norm_sub_le z b

lemma hermitianCenterExtension_eventually_eq {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {z : Space} (hz : φ =ᶠ[𝓝 z] fun _ => 1) :
    (hermitianCenterExtension J p D hφ hc hφD : Space → Space →L[ℝ] Space) =ᶠ[𝓝 z]
      coordinateJ J p :=
  hz.mono fun _ hx => hermitianCenterExtension_eq J p D hφ hc hφD hx

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ContinuousAlternatingMap
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma closedLift_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (a : antiPre A J α hs ht) (p : X) {y : Space}
    (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs a).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      nonharmonicCorrectionLM A J α hs ht Gs p y a ![v,coordinateJ J p y v] := by
  change _ = ManifoldForms.pullback
    (exteriorDerivative (codifferential J α ht (Gs a).val.val)) (extChartAt Model p).symm y _
  rw [pullback_complexLine J _ p hy,pullback_complexLine J _ p hy]
  exact closedLiftOfInverse_complexLine A J α hs ht H Gs a _ _

lemma correctedDdc_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] -
      nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v] := by
  change ManifoldForms.pullback (_-_) _ _ _ = _
  change ManifoldForms.pullback (smoothDdc J hf).val _ _ _ -
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs
      (smoothAntiProjection A J α hs ht (smoothDdc J hf))).val _ _ _ = _
  rw [closedLift_pullback_complexLine A J α hs ht H Gs _ p hy]
  rfl

lemma form_complexLine_norm_le (β : MetricForms.Form Space 2) (K : Space →L[ℝ] Space)
    (v : Space) : ‖β ![v,K v]‖ ≤ ‖β‖*‖K‖*‖v‖^2 := by
  calc
    _ ≤ ‖β‖*(‖v‖*‖K v‖) := by simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using β.le_opNorm ![v,K v]
    _ ≤ ‖β‖*(‖v‖*(‖K‖*‖v‖)) := by gcongr; exact K.le_opNorm v
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_HermitianDerivativeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma linear_pullback_fderiv_norm (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : E) :
    ‖fderiv ℝ (fun x => f (L x)) z‖ ≤ ‖fderiv ℝ f (L z)‖ * ‖L‖ := by
  rw [fderiv_fun_comp z (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) L.differentiableAt,L.fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

lemma linear_pullback_hessian_norm (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => f (L x))) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * ‖L‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [linear_pullback_hessian L hf]
  have h := (fderiv ℝ (fderiv ℝ f) (L z)).le_opNorm₂ (L u) (L v)
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * ‖L u‖ * ‖L v‖ := h
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * (‖L‖ * ‖u‖) * (‖L‖ * ‖v‖) := by
      gcongr <;> exact L.le_opNorm _
    _ = _ := by ring

lemma hermitianGraph_norm_ge (K : E →L[ℝ] E) (z : E) : ‖z‖ ≤ ‖hermitianGraph K z‖ := by
  have h := hermitianGraph_norm_sq K z
  nlinarith [sq_nonneg ‖K z‖,norm_nonneg (hermitianGraph K z),norm_nonneg z]

lemma norm_hermitianGraph_le (K : E →L[ℝ] E) : ‖hermitianGraph K‖ ≤ 1+‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hn : ‖hermitianGraph K z‖ ≤ ‖z‖ + ‖K z‖ := by
    have h1 := hermitianGraph_norm_sq K z
    have hpos := mul_nonneg (norm_nonneg z) (norm_nonneg (K z))
    nlinarith only [h1,norm_nonneg (hermitianGraph K z),norm_nonneg z,
      norm_nonneg (K z),hpos]
  calc
    _ ≤ ‖z‖ + ‖K z‖ := hn
    _ ≤ ‖z‖ + ‖K‖ * ‖z‖ := add_le_add_right (K.le_opNorm z) _
    _ = _ := by ring

lemma norm_hermitianLog_gradient (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (hermitianLogPotential K s) z‖ ≤ 2*(1+‖K‖)/(s+‖z‖) := by
  calc
    _ ≤ ‖fderiv ℝ (logPotential s) (hermitianGraph K z)‖ * ‖hermitianGraph K‖ :=
      linear_pullback_fderiv_norm _ (logPotential_smooth hs) z
    _ ≤ (2/(s+‖hermitianGraph K z‖)) * (1+‖K‖) := by
      gcongr
      exact norm_logPotential_fderiv hs _
      exact norm_hermitianGraph_le K
    _ ≤ (2/(s+‖z‖)) * (1+‖K‖) := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring

lemma norm_hermitianLog_hessian (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (hermitianLogPotential K s)) z‖ ≤ 6*(1+‖K‖)^2/(s+‖z‖)^2 := by
  let : NormedAddCommGroup (WithLp 2 (E × E)) := inferInstance
  let : NormedSpace ℝ (WithLp 2 (E × E)) := inferInstance
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (logPotential s)) (hermitianGraph K z)‖ * ‖hermitianGraph K‖^2 :=
      linear_pullback_hessian_norm _ (logPotential_smooth hs) z
    _ ≤ (6/(s+‖hermitianGraph K z‖)^2) * (1+‖K‖)^2 := by
      gcongr
      exact norm_logPotential_hessian hs _
      exact norm_hermitianGraph_le K
    _ ≤ (6/(s+‖z‖)^2) * (1+‖K‖)^2 := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring

lemma norm_hermitianSqrt_gradient (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (hermitianSqrtPotential K s) z‖ ≤ 1+‖K‖ := by
  calc
    _ ≤ ‖fderiv ℝ (sqrtPotential s) (hermitianGraph K z)‖ * ‖hermitianGraph K‖ :=
      linear_pullback_fderiv_norm _ (sqrtPotential_smooth hs) z
    _ ≤ 1 * (1+‖K‖) := by
      gcongr
      exact norm_sqrtPotential_fderiv hs _
      exact norm_hermitianGraph_le K
    _ = _ := one_mul _

lemma norm_hermitianSqrt_hessian (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z‖ ≤ 4*(1+‖K‖)^2/(s+‖z‖) := by
  let : NormedAddCommGroup (WithLp 2 (E × E)) := inferInstance
  let : NormedSpace ℝ (WithLp 2 (E × E)) := inferInstance
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (sqrtPotential s)) (hermitianGraph K z)‖ * ‖hermitianGraph K‖^2 :=
      linear_pullback_hessian_norm _ (sqrtPotential_smooth hs) z
    _ ≤ (4/(s+‖hermitianGraph K z‖)) * (1+‖K‖)^2 := by
      gcongr
      exact norm_sqrtPotential_hessian hs _
      exact norm_hermitianGraph_le K
    _ ≤ (4/(s+‖z‖)) * (1+‖K‖)^2 := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianLog_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (hermitianLogPotential K s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianLogPotential K s)) z ![v,K v]‖ ≤
      ((1+M)^2*(16*L*M/(s+‖z‖)))*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (hermitianLogPotential K s) z :=
    contDiffAt_infty.mp (hermitianLogPotential_smooth K hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (hermitianLogPotential K s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hNs : 1+M ≤ (1+M)^2 := by nlinarith
  have hgN : 1+‖K‖ ≤ (1+M)^2 := (show 1+‖K‖ ≤ 1+M by linarith).trans hNs
  have hhN : (1+‖K‖)^2 ≤ (1+M)^2 := by gcongr
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (hermitianLogPotential K s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (hermitianLogPotential K s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ ((1+M)^2*(6/(s+‖z‖)^2*(L*‖z‖)*(M+M)+2*(2/(s+‖z‖))*L*M))*‖v‖^2 := by
      have hh := (norm_hermitianLog_hessian K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhN (by norm_num)) (sq_nonneg _))
      have hg := (norm_hermitianLog_gradient K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgN (by norm_num)) ha.le)
      calc
        _ ≤ ((6*(1+M)^2/(s+‖z‖)^2)*(L*‖z‖)*(M+M) +
            2*(2*(1+M)^2/(s+‖z‖))*L*M)*‖v‖^2 := by gcongr
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (log_error_coefficient ha (by linarith) hL hM) (sq_nonneg _)) (sq_nonneg ‖v‖)

lemma hermitianSqrt_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (hermitianSqrtPotential K s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianSqrtPotential K s)) z ![v,K v]‖ ≤
      ((1+M)^2*(10*L*M))*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (hermitianSqrtPotential K s) z :=
    contDiffAt_infty.mp (hermitianSqrtPotential_smooth K hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hNs : 1+M ≤ (1+M)^2 := by nlinarith
  have hgN : 1+‖K‖ ≤ (1+M)^2 := (show 1+‖K‖ ≤ 1+M by linarith).trans hNs
  have hhN : (1+‖K‖)^2 ≤ (1+M)^2 := by gcongr
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (hermitianSqrtPotential K s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ ((1+M)^2*(4/(s+‖z‖)*(L*‖z‖)*(M+M)+2*1*L*M))*‖v‖^2 := by
      have hh := (norm_hermitianSqrt_hessian K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhN (by norm_num)) ha.le)
      have hg := (norm_hermitianSqrt_gradient K hs z).trans hgN
      calc
        _ ≤ ((4*(1+M)^2/(s+‖z‖))*(L*‖z‖)*(M+M) +
            2*((1+M)^2)*L*M)*‖v‖^2 := by gcongr
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sqrt_error_coefficient ha (by linarith) hL hM) (sq_nonneg _)) (sq_nonneg ‖v‖)
end TamingCompatibility.RadialPotential

end
end

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitian_sqrt_radius_bound (K : E →L[ℝ] E) {s M : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hK : ‖K‖ ≤ M) (z : E) :
    Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤ (1+M)*(s+‖z‖) := by
  have hG : ‖hermitianGraph K z‖ ≤ (1+M)*‖z‖ :=
    ((hermitianGraph K).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right ((norm_hermitianGraph_le K).trans (by linarith)) (norm_nonneg _))
  have hp : 0 ≤ s^2+‖z‖^2+‖K z‖^2 := by positivity
  have hq := Real.sq_sqrt hp
  have he := hermitianGraph_norm_sq K z
  have hsum : Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤ s+‖hermitianGraph K z‖ := by
    nlinarith [Real.sqrt_nonneg (s^2+‖z‖^2+‖K z‖^2),
      norm_nonneg (hermitianGraph K z),mul_nonneg hs.le (norm_nonneg (hermitianGraph K z))]
  nlinarith [mul_nonneg hM hs.le]

lemma hermitianSqrt_variable_ddc_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖v‖^2/((1+M)*(s+‖z‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (hermitianSqrtPotential K s)) z ![v,J z v] := by
  have hp := hermitianSqrt_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  have hb := hermitianSqrt_ddc_lower K hKK hs z v
  have hq : 0 < Real.sqrt (s^2+‖z‖^2+‖K z‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hden : ‖v‖^2/((1+M)*(s+‖z‖)) ≤
      (‖v‖^2+‖K v‖^2)/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) := by
    calc
      _ ≤ ‖v‖^2/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hq (hermitian_sqrt_radius_bound K hs hM hKn z)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ‖K v‖]) hq.le
  rw [Real.norm_eq_abs,abs_le] at hp
  linarith [hp.1]

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianTraceTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extDeriv_dc_translate (J : E → E →L[ℝ] E) (f : E → ℝ) (b y : E) :
    extDeriv (dc J (fun x => f (x-b))) y =
      extDeriv (dc (fun z => J (b+z)) f) (y-b) := by
  have he : dc J (fun x => f (x-b)) = fun x => dc (fun z => J (b+z)) f (x-b) := by
    funext x
    simp only [dc,fderiv_comp_sub]
    congr 3
    abel_nf
  rw [he,extDeriv,fderiv_comp_sub]
  rfl

lemma extDeriv_dc_congr_germ {J K : E → E →L[ℝ] E} {f g : E → ℝ} {y : E}
    (hJ : J =ᶠ[𝓝 y] K) (hf : f =ᶠ[𝓝 y] g) :
    extDeriv (dc J f) y = extDeriv (dc K g) y := by
  have he : dc J f =ᶠ[𝓝 y] dc K g := by
    filter_upwards [hJ,hf.fderiv (𝕜 := ℝ)] with x hx hf
    simp only [dc,hx,hf]
  exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin he.fderiv_eq
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma schwartz_hermitianSqrt_lower (W : 𝓢(E,E →L[ℝ] E)) {s : ℝ} (hs : 0 < s)
    (b y v : E) (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (fun x => hermitianSqrtPotential (W b) s (x-b))) y ![v,W y v] := by
  dsimp only
  rw [ExteriorForms.extDeriv_dc_translate]
  have hJ : DifferentiableAt ℝ (fun z => W (b+z)) (y-b) :=
    ((W.smooth ⊤).comp (contDiff_const.add contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _
  have he : b+(y-b)=y := by abel
  have h := hermitianSqrt_variable_ddc_lower (W b) hs (y-b) v hJ
    (by simpa only [he] using hWy) hWb
    (apply_nonneg _ _) (apply_nonneg _ _)
    (by simpa only [he] using GeometricChart.schwartz_difference_bound W y b)
    (by simpa only [fderiv_comp_add_left,he] using GeometricChart.schwartz_fderiv_bound W y)
    (by simpa only [he] using W.norm_le_seminorm ℝ y) (W.norm_le_seminorm ℝ b)
  simpa only [he] using h
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]

lemma translatedCutoffLog_germ (W : E → E →L[ℝ] E) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (b : E) {y : E} (hy : ‖y-b‖ < R) :
    translatedCutoffLog W R s b =ᶠ[𝓝 y] fun x => hermitianLogPotential (W b) s (x-b) := by
  have he : ∀ᶠ x in 𝓝 y, ‖x-b‖ < R :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
  filter_upwards [he] with x hx
  exact show scaledCutoff R (x-b) * hermitianLogPotential (W b) s (x-b) = _ by
    rw [scaledCutoff_one hR hx.le,one_mul]

lemma translatedCutoffSqrt_germ (W : E → E →L[ℝ] E) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (b : E) {y : E} (hy : ‖y-b‖ < R) :
    translatedCutoffSqrt W R s b =ᶠ[𝓝 y] fun x => hermitianSqrtPotential (W b) s (x-b) := by
  have he : ∀ᶠ x in 𝓝 y, ‖x-b‖ < R :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
  filter_upwards [he] with x hx
  exact show scaledCutoff R (x-b) * hermitianSqrtPotential (W b) s (x-b) = _ by
    rw [scaledCutoff_one hR hx.le,one_mul]

lemma cutoffSqrt_trace_lower (W : 𝓢(E,E →L[ℝ] E)) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (b y v : E) (hy : ‖y-b‖ < R)
    (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (translatedCutoffSqrt W R s b)) y ![v,W y v] := by
  rw [ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
    (translatedCutoffSqrt_germ W hR s b hy)]
  exact schwartz_hermitianSqrt_lower W hs b y v hWy hWb
end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianManifoldTrace
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ContinuousAlternatingMap RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
 [T2Space X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma pullback_ddc_scalarChartLift {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hfD : tsupport f ⊆ (extChartAt Model p).target)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p f)))
      (extChartAt Model p).symm y = extDeriv (ExteriorForms.dc (coordinateJ J p) f) y := by
  rw [pullback_ddc J (scalarChartLift_smooth p hf hc hfD) p hy]
  apply ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact scalarChartLift_apply_inverse p f hz

lemma manifold_cutoffSqrt_trace_lower {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain)
    (hy : ‖y-b‖ < R) (hφb : φ b = 1) (hφy : φ =ᶠ[𝓝 y] fun _ => 1) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p
        (HermitianRadial.translatedCutoffSqrt W R s b)))) (extChartAt Model p).symm y
          ![v,coordinateJ J p y v] := by
  dsimp only
  let W := hermitianCenterExtension J p D hφ hc hφD
  have hyD : y ∈ D.domain := hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith)
  rw [pullback_ddc_scalarChartLift J p
    (HermitianRadial.translatedCutoffSqrt_smooth W R hs b)
    (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
    (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hball).trans D.domain_subset)
    (D.domain_subset hyD)]
  have hW := hermitianCenterExtension_eventually_eq J p D hφ hc hφD hφy
  rw [← ExteriorForms.extDeriv_dc_congr_germ hW Filter.EventuallyEq.rfl]
  rw [← hW.self_of_nhds]
  exact HermitianRadial.cutoffSqrt_trace_lower W hR hs b y v hy
    (hermitianCenterExtension_square J p D hφ hc hφD hφy.self_of_nhds)
    (hermitianCenterExtension_square J p D hφ hc hφD hφb)
end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCorrectedLower
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set Filter
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma cutoff_one_near {R : ℝ} (hR : 0 < R) {b y : Space} (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1) :
    φ b = 1 ∧ φ =ᶠ[𝓝 y] fun _ => 1 := by
  refine ⟨hφone b (Metric.mem_closedBall_self (by positivity)),?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds
    (show y ∈ Metric.ball b (2*R) by rw [Metric.mem_ball,dist_eq_norm]; linarith)] with z hz
  exact hφone z (Metric.ball_subset_closedBall hz)

lemma sqrtForm_trace_lower {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcor : ‖nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p
          (HermitianRadial.translatedCutoffSqrt_smooth
            (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
          (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
          (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset))))‖
        ≤ C*(1+|Real.log (s+‖y-b‖)|)) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) -
      (((1+M)^2*10*L*M)+C*M*(1+|Real.log (s+‖y-b‖)|))*‖v‖^2 ≤
      ManifoldForms.pullback (sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] := by
  dsimp only
  obtain ⟨hφb,hφy⟩ := cutoff_one_near hR hy hφone
  let W := hermitianCenterExtension J p D hφ hc hφD
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hyT : y ∈ (extChartAt Model p).target := D.domain_subset
    (hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith))
  have hJ : ‖coordinateJ J p y‖ ≤ M := by
    rw [← hermitianCenterExtension_eq J p D hφ hc hφD hφy.self_of_nhds]
    exact W.norm_le_seminorm ℝ y
  have hlow := manifold_cutoffSqrt_trace_lower J p D hφ hc hφD hR hsp b y v hball hy hφb hφy
  rw [sqrtForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p hyT]
  have hline := form_complexLine_norm_le
    (nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b)
          (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
          (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hball).trans D.domain_subset)))))
    (coordinateJ J p y) v
  have hbound : (C*(1+|Real.log (s+‖y-b‖)|))*‖coordinateJ J p y‖*‖v‖^2 ≤
      (C*(1+|Real.log (s+‖y-b‖)|))*M*‖v‖^2 := by gcongr
  have hh := hline.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcor (norm_nonneg _)) (sq_nonneg _)).trans hbound)
  rw [Real.norm_eq_abs] at hh
  have hu := (abs_le.mp hh).2
  dsimp only at hlow
  convert sub_le_sub hlow hu using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (dsimp only [M,W]; ring)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefect
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianDefect_nonneg (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) (z v : E) : 0 ≤ hermitianDefect K z v := by
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := two_direction_inner_sq_le (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  dsimp only [hermitianDefect]
  linarith

lemma logPotential_trace_eq {s : ℝ} (hs : 0 < s) (z u v : E)
    (hv : ‖v‖ = ‖u‖) :
    fderiv ℝ (fderiv ℝ (logPotential s)) z u u +
      fderiv ℝ (fderiv ℝ (logPotential s)) z v v =
      2*(s^2*‖u‖^2 + (‖z‖^2*‖u‖^2 - ⟪z,u⟫^2 - ⟪z,v⟫^2)) /
        (s^2+‖z‖^2)^2 := by
  rw [logPotential_hessian hs,logPotential_hessian hs,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv]
  have h := ne_of_gt (radial_sq_pos hs z)
  field_simp
  ring

lemma hermitianLog_ddc_eq_defect (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) {s : ℝ} (hs : 0 < s) (z v : E) :
    extDeriv (ExteriorForms.dc (fun _ => K) (hermitianLogPotential K s)) z ![v,K v] =
      2*(s^2*‖hermitianGraph K v‖^2 + hermitianDefect K z v) /
        (s^2+‖hermitianGraph K z‖^2)^2 := by
  have hc := hermitianLogPotential_smooth K hs
  have hd : DifferentiableAt ℝ (fderiv ℝ (hermitianLogPotential K s)) z :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  rw [constant_ddc_trace K hK hd]
  change fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z v v +
    fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z (K v) (K v) = _
  rw [linear_pullback_hessian _ (logPotential_smooth hs),
    linear_pullback_hessian _ (logPotential_smooth hs)]
  exact logPotential_trace_eq hs _ _ _ (hermitianGraph_complex_pair K hK v).2

lemma hermitianLog_variable_defect_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    2*hermitianDefect K z v/(s^2+‖hermitianGraph K z‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖z‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (hermitianLogPotential K s)) z ![v,J z v] := by
  have hp := hermitianLog_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  rw [hermitianLog_ddc_eq_defect K hKK hs,Real.norm_eq_abs,abs_le] at hp
  have hpos : 0 ≤ 2*(s^2*‖hermitianGraph K v‖^2)/(s^2+‖hermitianGraph K z‖^2)^2 := by positivity
  have he : 2*(s^2*‖hermitianGraph K v‖^2+hermitianDefect K z v) /
      (s^2+‖hermitianGraph K z‖^2)^2 =
      2*(s^2*‖hermitianGraph K v‖^2)/(s^2+‖hermitianGraph K z‖^2)^2 +
      2*hermitianDefect K z v/(s^2+‖hermitianGraph K z‖^2)^2 := by ring
  rw [he] at hp
  linarith [hp.1]

lemma schwartz_hermitianLog_defect_lower (W : 𝓢(E,E →L[ℝ] E)) {s : ℝ} (hs : 0 < s)
    (b y v : E) (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (fun x => hermitianLogPotential (W b) s (x-b))) y ![v,W y v] := by
  dsimp only
  rw [ExteriorForms.extDeriv_dc_translate]
  have hJ : DifferentiableAt ℝ (fun z => W (b+z)) (y-b) :=
    ((W.smooth ⊤).comp (contDiff_const.add contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _
  have he : b+(y-b)=y := by abel
  have h := hermitianLog_variable_defect_lower (W b) hs (y-b) v hJ
    (by simpa only [he] using hWy) hWb
    (apply_nonneg _ _) (apply_nonneg _ _)
    (by simpa only [he] using GeometricChart.schwartz_difference_bound W y b)
    (by simpa only [fderiv_comp_add_left,he] using GeometricChart.schwartz_fderiv_bound W y)
    (by simpa only [he] using W.norm_le_seminorm ℝ y) (W.norm_le_seminorm ℝ b)
  simpa only [he] using h
end TamingCompatibility.RadialPotential

namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
lemma cutoffLog_defect_lower (W : 𝓢(E,E →L[ℝ] E)) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (b y v : E) (hy : ‖y-b‖ < R)
    (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (translatedCutoffLog W R s b)) y ![v,W y v] := by
  rw [ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
    (translatedCutoffLog_germ W hR s b hy)]
  exact schwartz_hermitianLog_defect_lower W hs b y v hWy hWb
end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ContinuousAlternatingMap RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
 [T2Space X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma manifold_cutoffLog_defect_lower {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain)
    (hy : ‖y-b‖ < R) (hφb : φ b = 1) (hφy : φ =ᶠ[𝓝 y] fun _ => 1) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p
        (HermitianRadial.translatedCutoffLog W R s b)))) (extChartAt Model p).symm y
          ![v,coordinateJ J p y v] := by
  dsimp only
  let W := hermitianCenterExtension J p D hφ hc hφD
  have hyD : y ∈ D.domain := hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith)
  rw [pullback_ddc_scalarChartLift J p
    (HermitianRadial.translatedCutoffLog_smooth W R hs b)
    (HermitianRadial.translatedCutoffLog_compact W hR s b)
    (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans D.domain_subset)
    (D.domain_subset hyD)]
  have hW := hermitianCenterExtension_eventually_eq J p D hφ hc hφD hφy
  rw [← ExteriorForms.extDeriv_dc_congr_germ hW Filter.EventuallyEq.rfl]
  rw [← hW.self_of_nhds]
  exact HermitianRadial.cutoffLog_defect_lower W hR hs b y v hy
    (hermitianCenterExtension_square J p D hφ hc hφD hφy.self_of_nhds)
    (hermitianCenterExtension_square J p D hφ hc hφD hφb)

end TamingCompatibility.GeometricChart

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set Filter
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma logForm_defect_lower {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcor : ‖nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p
          (HermitianRadial.translatedCutoffLog_smooth
            (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
          (HermitianRadial.translatedCutoffLog_compact _ hR s b)
          (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset))))‖
        ≤ C/(s+‖y-b‖)) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*RadialPotential.hermitianDefect (W b) (y-b) v/(s^2+‖RadialPotential.hermitianGraph (W b) (y-b)‖^2)^2 -
      (((1+M)^2*16*L*M+C*M)/(s+‖y-b‖))*‖v‖^2 ≤
      ManifoldForms.pullback (logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] := by
  dsimp only
  obtain ⟨hφb,hφy⟩ := cutoff_one_near hR hy hφone
  let W := hermitianCenterExtension J p D hφ hc hφD
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hyT : y ∈ (extChartAt Model p).target := D.domain_subset
    (hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith))
  have hJ : ‖coordinateJ J p y‖ ≤ M := by
    rw [← hermitianCenterExtension_eq J p D hφ hc hφD hφy.self_of_nhds]
    exact W.norm_le_seminorm ℝ y
  have hlow := manifold_cutoffLog_defect_lower J p D hφ hc hφD hR hsp b y v hball hy hφb hφy
  rw [logForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p hyT]
  have hline := form_complexLine_norm_le
    (nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p (HermitianRadial.translatedCutoffLog_smooth W R hsp b)
          (HermitianRadial.translatedCutoffLog_compact W hR s b)
          (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans D.domain_subset)))))
    (coordinateJ J p y) v
  have hbound : (C/(s+‖y-b‖))*‖coordinateJ J p y‖*‖v‖^2 ≤
      (C/(s+‖y-b‖))*M*‖v‖^2 := by gcongr
  have hh := hline.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcor (norm_nonneg _)) (sq_nonneg _)).trans hbound)
  rw [Real.norm_eq_abs] at hh
  have hu := (abs_le.mp hh).2
  dsimp only at hlow
  convert sub_le_sub hlow hu using 1 <;> first | rfl | (dsimp only [M,W]; ring)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_LogErrorAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set Filter Topology

lemma exists_inverse_distance_dominates_log (c E F : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      c/(2*t) ≤ c/t - (E+F*(1+|Real.log t|)) := by
  let g : ℝ → ℝ := fun t => E*t+F*(t+|t*Real.log t|)
  have hg : Continuous g :=
    (continuous_const.mul continuous_id).add
      (continuous_const.mul (continuous_id.add Real.continuous_mul_log.abs))
  have hzero : g 0 = 0 := by simp [g]
  have he : ∀ᶠ t in 𝓝 (0:ℝ), g t < c/2 :=
    hg.continuousAt.eventually (Iio_mem_nhds (by rw [hzero]; positivity))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro t ht htd
  have hb := hball (show t ∈ Metric.ball (0:ℝ) δ by simpa [Real.dist_eq,abs_of_pos ht] using htd)
  change E*t+F*(t+|t*Real.log t|) < c/2 at hb
  rw [abs_mul,abs_of_pos ht] at hb
  apply (le_sub_iff_add_le).mpr
  apply (mul_le_mul_iff_left₀ ht).mp
  field_simp
  nlinarith

lemma absorb_inverse_distance_error {c E t U V L q : ℝ}
    (hc : 0 < c) (hE : 0 ≤ E) (ht : 0 < t)
    (hU : L-E/t*q ≤ U) (hV : c/t*q ≤ V) :
    L ≤ U+(E/c)*V := by
  have h := mul_le_mul_of_nonneg_left hV (div_nonneg hE hc.le)
  have he : E/c*(c/t*q) = E/t*q := by field_simp
  rw [he] at h
  linarith
end TamingCompatibility


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefectCombination
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem exists_defect_combination_oai (hR1 : 2*R ≤ 1) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ δ ≤ R ∧
      ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      let β := logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)) +
        a • sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
      let val := ManifoldForms.pullback β.val (extChartAt Model p.val).symm y
        ![v,coordinateJ J p.val y v]
      0 ≤ val ∧
        2*hermitianDefect (hermitianCenterExtension J p.val (D p) hφ hc hφD b) (y-b) v /
          (s^2+‖hermitianGraph (hermitianCenterExtension J p.val (D p) hφ hc hφD b) (y-b)‖^2)^2 ≤ val := by
  obtain ⟨C₀,hC₀,hlog⟩ := nonharmonic_logSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters K hK hKU
  obtain ⟨C₁,hC₁,hsqrt⟩ := nonharmonic_sqrtSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 K hK hKU
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  let L := SchwartzMap.seminorm ℝ 0 1 W
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hL : 0 ≤ L := apply_nonneg _ _
  have hM : 0 ≤ M := apply_nonneg _ _
  let E := (1+M)^2*16*L*M+C₀*M
  let ES := (1+M)^2*10*L*M
  let FS := C₁*M
  let cS := 1/(1+M)
  have hcS : 0 < cS := by dsimp [cS] <;> positivity
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  obtain ⟨δ,hδ,habs⟩ := exists_inverse_distance_dominates_log cS ES FS hcS
  let a := E/(cS/2)+1
  refine ⟨a,min δ R,by dsimp [a] <;> positivity,lt_min hδ hR,min_le_right _ _,?_⟩
  intro s hsr b hb y hy hnear v
  dsimp only
  have hsp : 0 < s := hsr.1
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hyR : ‖y-b‖ < R := by linarith [(lt_min_iff.mp hnear).2]
  have hone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1 :=
    fun z hz => hφone z (hcenters b hb hz)
  have hl := logForm_defect_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₀
    (by simpa only [logSource,dist_comm b y,dist_eq_norm] using hlog y hy s hsr b hb)
  have hh := sqrtForm_trace_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₁
    (by simpa only [sqrtSource,dist_comm b y,dist_eq_norm] using hsqrt y hy s hsr b hb)
  let t := s+‖y-b‖
  have htpos : 0 < t := by dsimp [t] <;> positivity
  have hsmall : t < δ := (lt_min_iff.mp hnear).1
  have hsa := mul_le_mul_of_nonneg_right (habs t htpos hsmall) (sq_nonneg ‖v‖)
  have hsl : (cS/2)/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    apply le_trans _ hh
    convert hsa using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [cS,ES,FS,t,M,L,W] <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring)
  let q := 2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2
  have hll : q-E/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := hl
  have hcomb := absorb_inverse_distance_error (by positivity : 0 < cS/2) hE htpos hll hsl
  have hsqnonneg := le_trans (by positivity : 0 ≤ (cS/2)/t*‖v‖^2) hsl
  have htotal : q ≤ ManifoldForms.pullback
      (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] +
      a * ManifoldForms.pullback
      (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    dsimp only [a]
    nlinarith
  have hWb : ∀ w, W b (W b w) = -w :=
    hermitianCenterExtension_square J p.val (D p) hφ hc hφD
      (hone b (Metric.mem_closedBall_self (by positivity)))
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg (by norm_num) (hermitianDefect_nonneg (W b) hWb (y-b) v)) (sq_nonneg _)
  change 0 ≤ _ + a*_ ∧ _
  exact ⟨hq.trans htotal,htotal⟩
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_defect_combination_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_defect_combination_oai.{u_1}
