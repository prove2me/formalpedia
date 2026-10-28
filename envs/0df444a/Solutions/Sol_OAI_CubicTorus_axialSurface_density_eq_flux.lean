-- Prove2me | solution 1 for OAI.CubicTorus.axialSurface_density_eq_flux
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:16:10.304448+00:00
-- url     : https://prove2.me/submissions/dd8c35b8-35dd-4632-b5e1-d5c558a49404

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace Periodic

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrableOn_fundamentalCube_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Cover → F} (hf : Continuous f) : IntegrableOn f fundamentalCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedFundamentalCube).mono_set
    (fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x; change (F (x + latticeVector m)) i = (F x) i; rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_variation_of_function i hc hpc
  simpa only [normalFirstVariation, hi, hf] using hH D

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_OctantVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_periodic_centered_primitive {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.Periodic ψ 1 ∧
      ∀ t,deriv ψ t=f t-∫ u in (0 : ℝ)..1,f u := by
  let c : ℝ := ∫ u in (0 : ℝ)..1,f u
  let g : ℝ → ℝ := fun t ↦ f t-c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hgp : Function.Periodic g 1 := fun t ↦ by simp [g,hp t]
  let ψ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t,g u
  have hd (t : ℝ) : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun t ↦ (hd t).differentiableAt,(funext fun t ↦ (hd t).deriv) ▸ hg⟩
  have hz : (∫ u in (0 : ℝ)..1,g u)=0 := by
    rw [show g=(fun t ↦ f t-c) from rfl,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
        intervalIntegrable_const,intervalIntegral.integral_const]
    simp [c]
  refine ⟨ψ,hψ,?_,fun t ↦ (hd t).deriv⟩
  intro t
  change (∫ u in (0 : ℝ)..t+1,g u)=∫ u in (0 : ℝ)..t,g u
  rw [hgp.intervalIntegral_add_eq_add 0 t (fun _ _ ↦ hg.continuous.intervalIntegrable _ _)]
  simp only [zero_add,hz,add_zero]

lemma axial_scalar_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (i : Fin 3) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa only [PiLp.add_apply,latticeVector,WithLp.ofLp_toLp,mul_one] using hp.int_mul (m i) (x i)

lemma axial_scalar_fderiv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i : Fin 3) (x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ f (y i)) x v=deriv f (x i)*v i := by
  have hh := (hf (x i)).hasDerivAt.comp_hasFDerivAt x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : Cover ↦ f (y i)) _ x at hh
  rw [hh.fderiv]
  rfl

lemma axial_field_tangentialDivergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x ν : Cover) :
    tangentialDivergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x ν=
      deriv f (x i)*(1-(ν i)^2) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [tangentialDivergence_smul_const hd,axial_scalar_fderiv hf]
  simp [tangentPart,EuclideanSpace.inner_single_right,pow_two]

lemma axial_field_divergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Cover) :
    divergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x=deriv f (x i) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [divergence_smul_const hd,axial_scalar_fderiv hf]
  simp

theorem sibling_axial_flux_derivative {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : Function.Periodic ψ 1) :
    (∫ z,deriv ψ ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))=
      H*∫ x in fundamentalCube∩quotientMap ⁻¹' E,deriv ψ (x i) := by
  have hfield : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Cover ↦ ψ (x i) • (EuclideanSpace.single i 1 : Cover)) :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hh := Periodic.tangent_firstVariation_of_coordinate hH hfield (fun m x ↦ by
    rw [axial_scalar_periodic hp i m x])
  simpa only [axial_field_tangentialDivergence (hψ.differentiable (by simp)),
    axial_field_divergence (hψ.differentiable (by simp))] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_flux_marginal {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  obtain ⟨ψ,hψ,hψp,hd⟩ := smooth_periodic_centered_primitive hf hp
  have hh := sibling_axial_flux_derivative hH i hψ hψp
  simp_rw [hd,sub_mul] at hh
  have hiV : IntegrableOn (fun x : Cover ↦ f (x i))
      (fundamentalCube∩quotientMap ⁻¹' E) :=
    (integrableOn_fundamentalCube_of_continuous
      (hf.continuous.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous)).mono_set inter_subset_left
  rw [integral_sub (normal_axial_integrable μ i hf.continuous)
      ((normal_transverse_integrable μ i).const_mul _),integral_const_mul,
    integral_sub hiV (integrable_const _),integral_const] at hh
  simp only [Measure.real_def,Measure.restrict_apply_univ,smul_eq_mul] at hh
  change _-_ = H*(_-volume.real (fundamentalCube∩quotientMap ⁻¹' E)*_) at hh
  unfold axialTransverseMass
  nlinarith [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalSphere_sum_sq (ν : NormalSphere) : (∑ i : Fin 3,((ν : Cover) i)^2)=1 := by
  have hh := real_inner_self_eq_norm_sq (ν : Cover)
  rw [ν.property,one_pow] at hh
  simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,←pow_two] using hh

lemma normalSphere_coordinate_sq_le (ν : NormalSphere) (i : Fin 3) : ((ν : Cover) i)^2≤1 := by
  exact (Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) ↦ sq_nonneg ((ν : Cover) j))
    (Finset.mem_univ i)).trans_eq (normalSphere_sum_sq ν)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma circleMollifier_tendsto : Tendsto (fun n ↦ (circleMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [circleMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma circleSmoothApprox_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed hf.locallyIntegrable

lemma circleSmoothApprox_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n ↦ circleSmoothApprox f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous circleMollifier_tendsto hf x

lemma circleSmoothApprox_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ x,‖f x‖≤C)
    (n : ℕ) (x : ℝ) : ‖circleSmoothApprox f n x‖≤C := by
  rw [circleSmoothApprox,convolution_def]
  calc
    _ ≤ ∫ y : ℝ,(circleMollifier n).normed volume y*C := by
      apply norm_integral_le_of_norm_le ((circleMollifier n).integrable_normed.mul_const C)
      filter_upwards [] with y
      rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg ((circleMollifier n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hb (x-y)) ((circleMollifier n).nonneg_normed y)
    _ = C := by rw [integral_mul_const,(circleMollifier n).integral_normed,one_mul]

lemma circleSmoothApprox_integral_tendsto {α : Type*} [MeasurableSpace α]
    {η : Measure α} {g w : α → ℝ} (hg : Measurable g) (hw : Integrable w η)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x)*w x ∂η) atTop
      (𝓝 (∫ x,f (g x)*w x ∂η)) := by
  obtain ⟨C,hC⟩ := (hp.isBounded_of_continuous (by norm_num) hf).exists_norm_le
  have hbound (t : ℝ) : ‖f t‖≤C := hC _ ⟨t,rfl⟩
  apply tendsto_integral_of_dominated_convergence (fun x ↦ C*‖w x‖)
  · intro n
    exact (((circleSmoothApprox_contDiff hf n).continuous.measurable.comp hg).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  · exact hw.norm.const_mul C
  · intro n
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (circleSmoothApprox_bound hbound n (g x)) (norm_nonneg _)
  · filter_upwards [] with x
    exact (circleSmoothApprox_tendsto hf (g x)).mul tendsto_const_nhds

lemma circleSmoothApprox_integral_tendsto_finite {α : Type*} [MeasurableSpace α]
    {η : Measure α} [IsFiniteMeasure η] {g : α → ℝ} (hg : Measurable g)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x) ∂η) atTop
      (𝓝 (∫ x,f (g x) ∂η)) := by
  simpa only [mul_one] using circleSmoothApprox_integral_tendsto hg
    (integrable_const (1 : ℝ) (μ := η)) hf hp

theorem axial_flux_marginal_continuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  let A := fundamentalCube∩quotientMap ⁻¹' E
  have hA : volume A≠⊤ := ne_top_of_le_ne_top (by rw [volume_fundamentalCube]; exact ENNReal.one_ne_top)
    (measure_mono inter_subset_left)
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hA.lt_top⟩
  have hs := circleSmoothApprox_integral_tendsto
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst).measurable)
    (normal_transverse_integrable μ i) hf hp
  have hv := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict A)
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).measurable hf hp
  have ht := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict (Ioc (0 : ℝ) 1))
    measurable_id hf hp
  have ht' : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1,circleSmoothApprox f n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1,f t)) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),id_eq] using ht
  have hleft := hs.sub (hv.const_mul H)
  have hright := ht'.const_mul (axialTransverseMass μ i-H*volume.real A)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [] with n
  exact (axial_flux_marginal hH i (circleSmoothApprox_contDiff hf n)
    (circleSmoothApprox_periodic hp n)).symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AxisCircleLebesgue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSurfaceMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)),smul_eq_mul,mul_comm]

lemma axialVolumeMarginal_integral (E : Set Torus) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun x : Cover ↦ (x i : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]

lemma axisCircleLebesgue_integral {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle))=
      ∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun t : ℝ ↦ (t : AxisCircle)) := AddCircle.continuous_mk' (1 : ℝ)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]

lemma axial_circle_flux_integral {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := by
  rw [axialSurfaceMarginal_integral μ i hf,axialVolumeMarginal_integral E i hf,
    axisCircleLebesgue_integral hf]
  have hc : Continuous (fun t : ℝ ↦ f (t : AxisCircle)) := hf.comp (AddCircle.continuous_mk' (1 : ℝ))
  exact axial_flux_marginal_continuous hH i hc
    (fun t ↦ by change f ((t+1 : ℝ) : AxisCircle)=f (t : AxisCircle); rw [AddCircle.coe_add_period])

theorem axial_circle_flux_measure {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    let c := axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E)
    (axialSurfaceMarginal μ i : Measure AxisCircle)+
      Real.toNNReal (-H) • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal (-c) • (axisCircleLebesgue : Measure AxisCircle)=
      Real.toNNReal H • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal c • (axisCircleLebesgue : Measure AxisCircle) := by
  intro c
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hi (η : Measure AxisCircle) [IsFiniteMeasure η] : Integrable f η := f.integrable
  rw [integral_add_measure (hi _) (hi _),integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal']
  have hh := axial_circle_flux_integral hH i f.continuous
  change _-H*_=c*_ at hh
  have split (a : ℝ) : max a 0-max (-a) 0=a := by
    rcases le_total 0 a with ha|ha
    · simp only [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha),sub_zero]
    · simp only [max_eq_right ha,max_eq_left (neg_nonneg.mpr ha),zero_sub,neg_neg]
  have hh' : (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      c*(∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := hh
  rw [←split H,←split c] at hh'
  linarith only [hh']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircleLebesgue_eq_volume : (axisCircleLebesgue : Measure AxisCircle)=volume := by
  change Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))=volume
  exact (show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle))
    (volume.restrict (Ioc 0 1)) volume from by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

lemma cube_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Cover ↦ (x i : AxisCircle))
      (volume.restrict fundamentalCube) volume :=
  (torus_axis_measurePreserving i).comp quotientMap_measurePreserving

lemma axialVolumeMarginal_le (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≤volume := by
  change Measure.map (fun x : Cover ↦ (x i : AxisCircle))
    (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))≤volume
  rw [←(cube_axis_measurePreserving i).map_eq]
  exact Measure.map_mono (Measure.restrict_mono inter_subset_left le_rfl)
    (cube_axis_measurePreserving i).measurable

lemma axialVolumeMarginal_absolutelyContinuous (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≪volume :=
  (axialVolumeMarginal_le E i).absolutelyContinuous

theorem axialSurfaceMarginal_absolutelyContinuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hv := axialVolumeMarginal_absolutelyContinuous E i hz
  have hh := congrArg (fun η : Measure AxisCircle ↦ η s) (axial_circle_flux_measure hH i)
  simp only [Measure.add_apply,Measure.smul_apply,axisCircleLebesgue_eq_volume,hz,hv,smul_zero,
    add_zero] at hh
  exact hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusAxialSplit_measurePreserving (i : Fin 3) :
    MeasurePreserving (torusAxialSplit i) torusVolume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i).comp
    torus_to_product_measurePreserving

lemma axialSliceVolume_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (axialSliceVolume E i) := by
  exact measurable_measure_prodMk_left (hE.preimage (torusAxialSplit i).symm.measurable)

lemma axialVolumeMarginal_apply {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {s : Set AxisCircle} (hs : MeasurableSet s) :
    (axialVolumeMarginal E i : Measure AxisCircle) s=torusVolume (E∩{z : Torus | z i∈s}) := by
  have hm : Measurable (fun x : Cover ↦ (x i : AxisCircle)) :=
    (cube_axis_measurePreserving i).measurable
  change Measure.map _ _ s=_
  rw [Measure.map_apply hm hs,Measure.restrict_apply (hs.preimage hm)]
  have he : (fun x : Cover ↦ (x i : AxisCircle)) ⁻¹' s∩(fundamentalCube∩quotientMap ⁻¹' E)=
      quotientMap ⁻¹' (E∩{z : Torus | z i∈s})∩fundamentalCube := by
    ext x; simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]; tauto
  rw [he]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  have hh := quotientMap_measurePreserving.measure_preimage hS.nullMeasurableSet
  rw [Measure.restrict_apply (hS.preimage continuous_quotientMap.measurable)] at hh
  exact hh

theorem axialVolumeMarginal_eq_withDensity {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)=volume.withDensity (axialSliceVolume E i) := by
  apply Measure.ext
  intro s hs
  rw [axialVolumeMarginal_apply hE i hs,withDensity_apply _ hs]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  rw [←(torusAxialSplit_measurePreserving i).symm.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=_
  rw [Measure.prod_apply (hS.preimage (torusAxialSplit i).symm.measurable),←lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t∈s
  · rw [indicator_of_mem ht]
    congr 1
    ext y
    simp [axialSlice,ht]
  · rw [indicator_of_notMem ht]
    have he : Prod.mk t ⁻¹' ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=∅ := by
      ext y; simp [ht]
    rw [he,measure_empty]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceVolume_real_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Integrable (fun t ↦ (axialSliceVolume E i t).toReal) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (axialSliceVolume_measurable hE i).ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using axialSliceVolume_le_one E i t)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_integrable_mul_continuous {h f : AxisCircle → ℝ} (hi : Integrable h)
    (hf : Continuous f) : Integrable (fun t ↦ h t*f t) := by
  let F : C(AxisCircle,ℝ) := ⟨f,hf⟩
  exact hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun t ↦ F.norm_coe_le_norm t)

lemma integrable_circle_eq_zero_of_continuous_pairing {h : AxisCircle → ℝ}
    (hm : Measurable h) (hi : Integrable h)
    (hz : ∀ f : AxisCircle → ℝ,Continuous f → (∫ t,h t*f t)=0) : h=ᵐ[volume]0 := by
  let η := volume.withDensity (fun t ↦ ENNReal.ofReal (h t))
  let θ := volume.withDensity (fun t ↦ ENNReal.ofReal (-h t))
  have : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have : IsFiniteMeasure θ := isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  have he : η=θ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    change (∫ t,f t ∂volume.withDensity _)=(∫ t,f t ∂volume.withDensity _)
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (show Measurable (fun t ↦ ENNReal.ofReal (-h t)) from hm.neg.ennreal_ofReal) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal',smul_eq_mul]
    have hip : Integrable (fun t ↦ max (h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.sup (integrable_const (0 : ℝ))) f.continuous
    have hin : Integrable (fun t ↦ max (-h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.neg.sup (integrable_const (0 : ℝ))) f.continuous
    apply sub_eq_zero.mp
    rw [←integral_sub hip hin]
    convert hz f f.continuous using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [] with t
    rcases le_total 0 (h t) with ht|ht
    · rw [max_eq_left ht,max_eq_right (neg_nonpos.mpr ht),zero_mul,sub_zero]
    · rw [max_eq_right ht,max_eq_left (neg_nonneg.mpr ht),zero_mul,zero_sub]; ring
  have hae := (withDensity_eq_iff_of_sigmaFinite hm.ennreal_ofReal.aemeasurable hm.neg.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hae] with t ht
  have hh := congrArg ENNReal.toReal ht
  simp only [ENNReal.toReal_ofReal',Pi.neg_apply] at hh
  change h t=0
  rcases le_total 0 (h t) with hle|hle
  · rw [max_eq_left hle,max_eq_right (neg_nonpos.mpr hle)] at hh; exact hh
  · rw [max_eq_right hle,max_eq_left (neg_nonneg.mpr hle)] at hh; linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ActualAxialFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma actualAxialFlux_integrable {E : Set Torus} (hE : MeasurableSet E)
    (μ : FiniteMeasure NormalBundle) (H : ℝ) (i : Fin 3) :
    Integrable (actualAxialFlux E μ H i) :=
  (integrable_const _).add (((axialSliceVolume_real_integrable hE i).sub (integrable_const _)).const_mul _)

lemma actualAxialFlux_measurable {E : Set Torus} (hE : MeasurableSet E)
    (μ : FiniteMeasure NormalBundle) (H : ℝ) (i : Fin 3) :
    Measurable (actualAxialFlux E μ H i) :=
  measurable_const.add (measurable_const.mul ((axialSliceVolume_measurable hE i).ennreal_toReal.sub measurable_const))

lemma axialSurface_density_eq_flux_oai {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal)=ᵐ[volume]
      actualAxialFlux E μ H i := by
  let d : AxisCircle → ℝ := fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal
  have hd : Measurable d := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hdi : Integrable d := Measure.integrable_toReal_rnDeriv
  have hac := axialSurfaceMarginal_absolutelyContinuous hH i
  have hh := integrable_circle_eq_zero_of_continuous_pairing
    (hd.sub (actualAxialFlux_measurable hE μ H i))
    (hdi.sub (actualAxialFlux_integrable hE μ H i)) ?_
  · filter_upwards [hh] with t ht
    exact sub_eq_zero.mp ht
  intro f hf
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvf := circle_integrable_mul_continuous (axialSliceVolume_real_integrable hE i) hf
  have hh := axial_circle_flux_integral hH i hf
  rw [axisCircleLebesgue_eq_volume,←realVolume_lift hE,
    axialVolumeMarginal_eq_withDensity hE i,
    integral_withDensity_eq_integral_toReal_smul (axialSliceVolume_measurable hE i)
      (ae_of_all _ fun t ↦ lt_of_le_of_lt (axialSliceVolume_le_one E i t) ENNReal.one_lt_top)] at hh
  simp only [smul_eq_mul] at hh
  simp only [Pi.sub_apply,sub_mul]
  rw [integral_sub (circle_integrable_mul_continuous hdi hf)
    (circle_integrable_mul_continuous (actualAxialFlux_integrable hE μ H i) hf)]
  have hleft : (∫ t,d t*f t)=∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle) :=
    integral_toReal_rnDeriv_mul hac
  rw [hleft]
  have hright : (∫ t,actualAxialFlux E μ H i t*f t)=
      axialTransverseMass μ i*(∫ t,f t)+H*((∫ t,(axialSliceVolume E i t).toReal*f t)-torusVolume.real E*(∫ t,f t)) := by
    simp only [actualAxialFlux,add_mul,mul_assoc,sub_mul]
    have hsub : Integrable (fun t ↦ (axialSliceVolume E i t).toReal*f t-torusVolume.real E*f t) := by
      exact (hvf.sub (hfint.const_mul (torusVolume.real E))).congr (ae_of_all _ fun t ↦ rfl)
    rw [integral_add (hfint.const_mul (axialTransverseMass μ i)) (hsub.const_mul H),
      integral_const_mul,integral_const_mul,integral_sub hvf (hfint.const_mul (torusVolume.real E)),integral_const_mul]
  rw [hright]
  linarith only [hh]

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.axialSurface_density_eq_flux_oai := @OAI.CubicTorus.axialSurface_density_eq_flux_oai
