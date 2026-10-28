-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:28:50.757862+00:00
-- url     : https://prove2.me/submissions/2c17adc5-f0fa-4c5a-b694-a2fd2ba66eeb

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_planar_profile_circle

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

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

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

end CubicTorus

namespace CubicTorus

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

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

lemma normal_axisCircle_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)

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

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalTransverseLength
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

lemma normalTransverseLength_nonneg (i : Fin 3) (z : NormalBundle) :
    0≤normalTransverseLength i z := Real.sqrt_nonneg _

lemma normalTransverseLength_sq (i : Fin 3) (z : NormalBundle) :
    (normalTransverseLength i z)^2+((z.2 : Cover) i)^2=1 := by
  rw [normalTransverseLength,Real.sq_sqrt (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i))]
  ring

lemma axialPerimeterMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPerimeterMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialPerimeterDensity_nonneg (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) :
    0≤axialPerimeterDensity μ i t := ENNReal.toReal_nonneg

lemma axialPerimeterDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialPerimeterDensity μ i) := Measure.integrable_toReal_rnDeriv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma bounded_real_locallyIntegrable {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) : LocallyIntegrable f volume := by
  apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono hf.aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hb t

lemma circleSmoothApprox_bounded_contDiff {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed
    (bounded_real_locallyIntegrable hf hb)

lemma circleSmoothApprox_nonneg {f : ℝ → ℝ} (hf : ∀ t,0≤f t) (n : ℕ) (t : ℝ) :
    0 ≤ circleSmoothApprox f n t := by
  rw [circleSmoothApprox,convolution_def]
  exact integral_nonneg fun x ↦ mul_nonneg ((circleMollifier n).nonneg_normed x) (hf (t-x))

lemma circleSmoothApprox_bounded_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    ∀ᵐ t : ℝ,Tendsto (fun n ↦ circleSmoothApprox f n t) atTop (𝓝 (f t)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    circleMollifier_tendsto (K := 2) _ (bounded_real_locallyIntegrable hf hb)
  exact Eventually.of_forall fun n ↦ by dsimp [circleMollifier]; ring_nf; rfl

lemma circleSmoothApprox_lift_ae_tendsto {f : AxisCircle → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
    let hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
    ∀ᵐ t : AxisCircle,Tendsto (fun n ↦ (circleSmoothApprox_periodic hp n).lift t) atTop (𝓝 (f t)) := by
  intro F hp
  have hfm : Measurable F := hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := ae_restrict_of_ae (s := Ioc (0 : ℝ) 1) (circleSmoothApprox_bounded_ae_tendsto hfm (fun t ↦ hb _))
  have hmp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [←hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable (measurableSet_tendsto_fun
    (fun n ↦ (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
      (circleSmoothApprox_bounded_contDiff hfm (fun t ↦ hb _) n).continuous).measurable) hf)).mpr
  simpa only [Function.Periodic.lift_coe] using hh

theorem integrable_circle_nonneg_of_smooth_pairing {h : AxisCircle → ℝ} (hi : Integrable h)
    (hw : ∀ (ψ : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) ψ → ∀ hp : Function.Periodic ψ 1,
      (∀ t,0≤ψ t) → 0≤∫ t,h t*hp.lift t) : 0≤ᵐ[volume] h := by
  apply ae_nonneg_of_forall_setIntegral_nonneg hi
  intro s hs _
  let f : AxisCircle → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
  have hf : Measurable f := measurable_const.indicator hs
  have hb (t : AxisCircle) : |f t|≤1 := by
    by_cases ht : t∈s <;> simp [f,ht]
  have hn (t : ℝ) : 0≤F t := by apply indicator_nonneg; intro _ _; norm_num
  have hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
  have hc n := circleSmoothApprox_bounded_contDiff (hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable)
    (fun t ↦ hb _) n
  have hl : Tendsto (fun n ↦ ∫ t,h t*(circleSmoothApprox_periodic hp n).lift t) atTop
      (𝓝 (∫ t,h t*f t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖h t‖)
    · intro n
      exact hi.aestronglyMeasurable.mul (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
        (hc n).continuous).aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards [] with t
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      induction t using Quotient.inductionOn with | h t =>
        exact circleSmoothApprox_bound (fun t ↦ by simpa only [Real.norm_eq_abs] using hb (t : AxisCircle)) n t
    · filter_upwards [circleSmoothApprox_lift_ae_tendsto hf hb] with t ht
      exact tendsto_const_nhds.mul ht
  have hh : 0≤∫ t,h t*f t := ge_of_tendsto hl (Eventually.of_forall fun n ↦
    hw _ (hc n) (circleSmoothApprox_periodic hp n) (circleSmoothApprox_nonneg hn n))
  have he : (fun t ↦ h t*f t)=s.indicator h := by
    funext t
    by_cases ht : t∈s <;> simp [f,ht]
  rwa [he,integral_indicator hs] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_indicator {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (f : Torus → ℝ) (t : AxisCircle) :
    axialSliceIntegral E i f t=∫ y,E.indicator f ((torusAxialSplit i).symm (t,y)) := by
  rw [axialSliceIntegral,←integral_indicator (axialSlice_measurable hE i t)]
  congr 1

lemma axialSliceIntegral_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Integrable f torusVolume) : Integrable (axialSliceIntegral E i f) := by
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hf.indicator hE)
  have hh := hg.integral_prod_left
  simpa only [Function.comp_apply,←axialSliceIntegral_indicator hE] using hh

lemma axialSliceIntegral_pairing {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Continuous f) {ψ : AxisCircle → ℝ} (hψ : Continuous ψ) :
    (∫ t,ψ t*axialSliceIntegral E i f t)=∫ z in E,ψ (z i)*f z ∂torusVolume := by
  have hi : Integrable (fun z : Torus ↦ ψ (z i)*f z) torusVolume :=
    ((hψ.comp (PiLp.continuous_apply 2 _ i)).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hi.indicator hE)
  rw [←integral_indicator hE,←(torusAxialSplit_measurePreserving i).symm.integral_comp'
    (E.indicator (fun z : Torus ↦ ψ (z i)*f z))]
  change _=∫ z,((E.indicator (fun z : Torus ↦ ψ (z i)*f z)) ∘ (torusAxialSplit i).symm) z ∂volume.prod volume
  rw [integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [axialSliceIntegral_indicator hE,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : (torusAxialSplit i).symm (t,y)∈E <;> simp [hy]

lemma normal_transverse_inner_bound (i : Fin 3) (z : NormalBundle) (v : Cover)
    (hv : v i=0) (hb : ‖v‖≤1) : ⟪(z.2 : Cover),v⟫≤normalTransverseLength i z := by
  let n : Cover := (z.2 : Cover)-((z.2 : Cover) i) • EuclideanSpace.single i 1
  have hn : ‖n‖=normalTransverseLength i z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (normalTransverseLength_nonneg i z)).mp
    have hz : ‖(z.2 : Cover)‖=1 := z.2.property
    have hs := normalTransverseLength_sq i z
    dsimp only [n]
    rw [norm_sub_sq_real,real_inner_smul_right,EuclideanSpace.inner_single_right,norm_smul,
      PiLp.norm_single,Real.norm_eq_abs,Real.norm_eq_abs,abs_one,mul_one,hz]
    simp only [conj_trivial,one_mul] at *
    nlinarith [sq_abs ((z.2 : Cover) i)]
  have he : ⟪n,v⟫=⟪(z.2 : Cover),v⟫ := by
    simp [n,inner_sub_left,real_inner_smul_left,EuclideanSpace.inner_single_left,hv]
  rw [←he]
  calc
    _ ≤ ‖n‖*‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖n‖ := mul_le_of_le_one_right (norm_nonneg _) hb
    _ = _ := hn

lemma axialPerimeterDensity_pairing_continuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_weight_divergence {i : Fin 3} {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Cover) :
    divergence (fun y : Cover ↦ ψ (y i) • F y) x=ψ (x i)*divergence F x := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ ψ (y i)) x :=
    ((hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).differentiable (by simp)).differentiableAt
  rw [divergence_smul_function hd
    (hF.differentiable (by simp)).differentiableAt,inner_gradient_left,
    axial_scalar_fderiv (hψ.differentiable (by simp)),hFi,mul_zero,add_zero]

theorem axialSliceIntegral_weighted_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1)
    (hn : ∀ t,0≤ψ t) :
    (∫ t,hp.lift t*axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t)≤
      ∫ t,hp.lift t*axialPerimeterDensity μ i t := by
  let G : Cover → Cover := fun x ↦ ψ (x i) • F x
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul hF.1
  have hGp : ∀ m x,G (x+latticeVector m)=G x := by
    intro m x
    dsimp only [G]
    rw [axial_scalar_periodic hp i m x,hF.2.1]
  obtain ⟨C,hC,hCb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (show 0<C+1 by linarith) (fun x ↦ (hCb x).trans (by linarith))
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hp' := continuous_periodic_lift hp hψ.continuous
  rw [axialSliceIntegral_pairing hE i hd hp']
  have he : (fun z : Torus ↦ hp.lift (z i)*divergence F (representative z))=
      (fun z : Torus ↦ divergence G (representative z)) := by
    funext z
    rw [axial_weight_divergence hF.1 hFi hψ]
    congr 1
    have hh := congrArg (fun a : Torus ↦ hp.lift (a i)) (quotientMap_representative z)
    exact hh.symm
  rw [he,setIntegral_lift (continuous_divergence hG) (divergence_periodic hGp) hE,←hflux]
  simp_rw [mul_comm (hp.lift _) (axialPerimeterDensity μ i _)]
  rw [axialPerimeterDensity_pairing_continuous i ha hp']
  apply integral_mono
  · exact (normalTest G hG.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((normalTransverseLength_continuous i).mul (hp'.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),ψ ((z.1 : Cover) i) • F z.1⟫≤_
    simp only [real_inner_smul_right,Function.Periodic.lift_coe]
    rw [mul_comm (normalTransverseLength i z)]
    exact mul_le_mul_of_nonneg_left (normal_transverse_inner_bound i z _ (hFi _) (hF.2.2 _)) (hn _)

theorem axialSliceIntegral_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0) :
    axialSliceIntegral E i (fun z ↦ divergence F (representative z))≤ᵐ[volume]axialPerimeterDensity μ i := by
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hdI := hd.integrable_of_hasCompactSupport (μ := torusVolume) (HasCompactSupport.of_compactSpace _)
  have hs := axialSliceIntegral_integrable hE i hdI
  have hi := axialPerimeterDensity_integrable μ i
  have hh := integrable_circle_nonneg_of_smooth_pairing (hi.sub hs) (by
    intro ψ hψ hp hn
    have hc := continuous_periodic_lift hp hψ.continuous
    simp only [Pi.sub_apply,sub_mul]
    rw [integral_sub (circle_integrable_mul_continuous hi hc) (circle_integrable_mul_continuous hs hc)]
    apply sub_nonneg.mpr
    simpa only [mul_comm] using axialSliceIntegral_weighted_le hE hμ i ha hF hFi hψ hp hn)
  filter_upwards [hh] with t ht
  exact sub_nonneg.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axialSliceIntegral_ae_all_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,∀ (F : Cover → Cover) (_hF : AdmissibleField F),
      (∀ x,F x i=0) →
      axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t≤axialPerimeterDensity μ i t := by
  obtain ⟨S,hS,hSc,hSd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace (axialDivergenceClass i)).exists_countable_dense_subset
  have hh : ∀ f∈S,∀ᵐ t : AxisCircle,axialSliceFunctional E i t f≤axialPerimeterDensity μ i t := by
    intro f hf
    obtain ⟨F,hF,hFi,rfl⟩ := hS hf
    exact axialSliceIntegral_ae_le hE hμ i ha hF hFi
  filter_upwards [(ae_ball_iff hSc).mpr hh] with t ht
  intro F hF hFi
  let f : C(Torus,ℝ) := ⟨fun z ↦ divergence F (representative z),
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩
  have hf : f∈axialDivergenceClass i := ⟨F,hF,hFi,rfl⟩
  have hc : IsClosed {f : C(Torus,ℝ) | axialSliceFunctional E i t f≤axialPerimeterDensity μ i t} :=
    isClosed_le (axialSliceFunctional E i t).continuous continuous_const
  exact (closure_minimal ht hc) (hSd hf)

theorem axialTestPerimeter_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,axialTestPerimeter E i t≤ENNReal.ofReal (axialPerimeterDensity μ i t) := by
  filter_upwards [axialSliceIntegral_ae_all_le hE hμ i ha] with t ht
  exact iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ENNReal.ofReal_le_ofReal (ht F hF hFi)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisEmbedding_norm (i : Fin 3) (y : Plane) : ‖planeAxisEmbedding i y‖=‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
  simp

lemma planeAxisProjection_norm_le (i : Fin 3) (x : Cover) : ‖planeAxisProjection i x‖≤‖x‖ := by
  have hh : ‖planeAxisProjection i x‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
    simp only [planeAxisProjection_apply]
    nlinarith [sq_nonneg ‖x i‖]
  nlinarith [norm_nonneg (planeAxisProjection i x),norm_nonneg x]

lemma liftPlanarField_admissible (i : Fin 3) {G : Plane → Plane}
    (hG : PlanarAdmissibleField G) : AdmissibleField (liftPlanarField i G) := by
  refine ⟨(planeAxisEmbedding i).contDiff.comp (hG.1.comp (planeAxisProjection i).contDiff),?_,?_⟩
  · intro n x
    unfold liftPlanarField
    rw [map_add]
    exact congrArg (planeAxisEmbedding i) (hG.2.1 (fun j ↦ n (i.succAbove j)) _)
  · intro x
    rw [liftPlanarField,planeAxisEmbedding_norm]
    exact hG.2.2 _

lemma divergence_liftPlanarField (i : Fin 3) {G : Plane → Plane}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (liftPlanarField i G) x=planeDivergence G (planeAxisProjection i x) := by
  have hd := (planeAxisEmbedding i).hasFDerivAt.comp x
    (((hG.differentiable (by simp) (planeAxisProjection i x)).hasFDerivAt).comp x
      (planeAxisProjection i).hasFDerivAt)
  change HasFDerivAt (liftPlanarField i G) _ x at hd
  rw [divergence,hd.fderiv,Fin.sum_univ_succAbove _ i]
  simp [ContinuousLinearMap.comp_apply,planeDivergence,Fin.sum_univ_two]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisAt_contDiff (i : Fin 3) (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (planeAxisAt i a) :=
  contDiff_const.add (planeAxisEmbedding i).contDiff

lemma planeAxisAt_hasFDerivAt (i : Fin 3) (a : ℝ) (y : Plane) :
    HasFDerivAt (planeAxisAt i a) (planeAxisEmbedding i) y := by
  exact (planeAxisEmbedding i).hasFDerivAt.const_add (a • EuclideanSpace.single i (1 : ℝ))

lemma tracePlanarField_admissible (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : AdmissibleField F) : PlanarAdmissibleField (tracePlanarField i a F) := by
  refine ⟨(planeAxisProjection i).contDiff.comp (hF.1.comp (planeAxisAt_contDiff i a)),?_,?_⟩
  · intro n y
    have he : planeAxisAt i a (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        planeAxisAt i a y+latticeVector (i.insertNth (α := fun _ : Fin 3 ↦ ℤ) 0 n) := by
      ext k
      rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
        simp [latticeVector,planeAxisAt,map_add,add_assoc]
    unfold tracePlanarField
    rw [he,hF.2.1]
  · intro y
    exact (planeAxisProjection_norm_le i _).trans (hF.2.2 _)

lemma planeDivergence_tracePlanarField (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0) (y : Plane) :
    planeDivergence (tracePlanarField i a F) y=divergence F (planeAxisAt i a y) := by
  have hd := (planeAxisProjection i).hasFDerivAt.comp y
    (((hF.differentiable (by simp) (planeAxisAt i a y)).hasFDerivAt).comp y
      (planeAxisAt_hasFDerivAt i a y))
  change HasFDerivAt (tracePlanarField i a F) _ y at hd
  have hz : (fderiv ℝ F (planeAxisAt i a y) (EuclideanSpace.single i 1)) i=0 := by
    rw [←fderiv_component (hF.differentiable (by simp) _) i]
    simp only [hFi]
    simp
  rw [planeDivergence,hd.fderiv,divergence,Fin.sum_univ_succAbove _ i,hz]
  simp [ContinuousLinearMap.comp_apply,Fin.sum_univ_two]

lemma planeAxisProjection_representative (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    planeAxisProjection i (representative ((torusAxialSplit i).symm (t,y)))=planarRepresentative y := by
  ext j
  simp [representative,planarRepresentative]

lemma representative_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    representative ((torusAxialSplit i).symm (t,y))=
      planeAxisAt i (((AddCircle.equivIco (1 : ℝ) 0) t) : ℝ) (planarRepresentative y) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
    simp [representative,planarRepresentative]

theorem axialTestPerimeter_eq_planar (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialTestPerimeter E i t=planarTorusPerimeter (axialSlice E i t) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let a : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) t : ℝ)
    have hb : ENNReal.ofReal (∫ y in axialSlice E i t,
        planeDivergence (tracePlanarField i a F) (planarRepresentative y))≤
        planarTorusPerimeter (axialSlice E i t) :=
      le_iSup_of_le (tracePlanarField i a F)
        (le_iSup_of_le (tracePlanarField_admissible i a hF) le_rfl)
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [planeDivergence_tracePlanarField i a hF.1 hFi,representative_axialSplit]
  · refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
    have hb : ENNReal.ofReal (axialSliceIntegral E i
        (fun z ↦ divergence (liftPlanarField i G) (representative z)) t)≤axialTestPerimeter E i t :=
      le_iSup_of_le (liftPlanarField i G)
        (le_iSup_of_le (liftPlanarField_admissible i hG)
          (le_iSup_of_le (liftPlanarField_same i G) le_rfl))
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [divergence_liftPlanarField i hG.1,planeAxisProjection_representative]

theorem planarTorusPerimeter_slice_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,planarTorusPerimeter (axialSlice E i t)≤ENNReal.ofReal (axialPerimeterDensity μ i t) := by
  simpa only [axialTestPerimeter_eq_planar] using axialTestPerimeter_ae_le hE hμ i ha

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

lemma sqrt_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma sqrt_square_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
    (ne_of_gt hp) using 1
  · rfl
  · dsimp
    ring

lemma cutoff_pos : 0 < cutoff := by
  unfold cutoff
  positivity

lemma cutoff_sq : cutoff ^ 2 = 48 / 49 := by
  norm_num [cutoff, div_pow]

lemma cutoff_lt_one : cutoff < 1 := by
  nlinarith [cutoff_sq, cutoff_pos]

lemma rawWeight_lower {x : ℝ} (hx : x ∈ Ico 0 1) : ell ≤ rawWeight x := by
  have hrad : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hs2 := Real.sq_sqrt (le_of_lt hrad)
  unfold rawWeight ell lambda
  apply (le_div_iff₀ hs).2
  nlinarith [sq_nonneg (7 * Real.sqrt (1 - x ^ 2) - 1)]

lemma hasDerivAt_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt rawWeight
      (x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3)) x := by
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hs0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hh := ((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 98 * x * hs2

lemma continuousOn_rawWeight : ContinuousOn rawWeight (Icc 0 cutoff) := by
  have hs : ∀ x ∈ Icc 0 cutoff, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    apply ne_of_gt (Real.sqrt_pos.2 _)
    have hxl : x < 1 := lt_of_le_of_lt hx.2 cutoff_lt_one
    nlinarith [hx.1, sq_nonneg x]
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn) hs

lemma antitoneOn_rawWeight : AntitoneOn rawWeight (Icc 0 cutoff) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x =>
    x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3))
    (convex_Icc 0 cutoff) continuousOn_rawWeight ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_rawWeight ⟨hx.1, lt_trans hx.2 cutoff_lt_one⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx.1)
    have hsq : x ^ 2 ≤ cutoff ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hx.1) (le_of_lt hx.2) 2
    nlinarith [cutoff_sq]

lemma weight_mem {x : ℝ} (hx : 0 ≤ x) : weight x ∈ Icc ell 1 := by
  have hm : min x cutoff ∈ Icc 0 cutoff :=
    ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩
  constructor
  · exact rawWeight_lower ⟨hm.1, lt_of_le_of_lt hm.2 cutoff_lt_one⟩
  · have hh := antitoneOn_rawWeight ⟨le_rfl, le_of_lt cutoff_pos⟩ hm hm.1
    simpa [weight, rawWeight] using hh

lemma antitoneOn_weight : AntitoneOn weight (Ici 0) := by
  intro x hx y hy hxy
  exact antitoneOn_rawWeight
    ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩
    ⟨le_min hy (le_of_lt cutoff_pos), min_le_right _ _⟩ (min_le_min hxy le_rfl)

end CubicTorus.Nesting

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
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

lemma unitPlanarProfile_nonneg (s : ℝ) : 0≤unitPlanarProfile s := by
  dsimp only [unitPlanarProfile]
  exact le_min (by positivity) (le_min (by norm_num) (by positivity))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SharpSectionWeight
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

lemma unitPlanarProfile_pos {s : ℝ} (hs : s∈Ioo 0 1) : 0<unitPlanarProfile s := by
  have hs0 : 0 < s := hs.1
  unfold unitPlanarProfile
  apply lt_min
  · positivity
  · apply lt_min (by norm_num)
    have : 0<1-s := sub_pos.mpr hs.2
    positivity

lemma sharpSectionWeight_zero (H : ℝ) : sharpSectionWeight H 0=1 := by
  simp [sharpSectionWeight,Nesting.weight,Nesting.rawWeight,Nesting.cutoff_pos.le]

lemma sharpSectionWeight_one (H : ℝ) : sharpSectionWeight H 1=Nesting.ell := by
  simp [sharpSectionWeight]

lemma sharpSectionWeight_le {H s d : ℝ} (hH : 0≤H) (hs : s∈Icc 0 1)
    (hd : 0≤d) (hp : unitPlanarProfile s≤d) :
    sharpSectionWeight H s≤Nesting.weight (H*s/d) := by
  by_cases hz : s=0
  · subst s
    rw [sharpSectionWeight_zero]
    simp [Nesting.weight,Nesting.rawWeight,Nesting.cutoff_pos.le]
  by_cases ho : s=1
  · subst s
    rw [sharpSectionWeight_one]
    exact (Nesting.weight_mem (div_nonneg (mul_nonneg hH (by norm_num)) hd)).1
  have hs' : s∈Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hz),lt_of_le_of_ne hs.2 ho⟩
  have hpp := unitPlanarProfile_pos hs'
  rw [sharpSectionWeight,ite_eq_left ⟨hs.1,hs'.2⟩]
  apply Nesting.antitoneOn_weight
  · exact div_nonneg (mul_nonneg hH hs.1) hd
  · exact div_nonneg (mul_nonneg hH hs.1) hpp.le
  · exact div_le_div_of_nonneg_left (mul_nonneg hH hs.1) hpp hp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
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

theorem isMinimizerAt_sharp_section_weight_ae_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ} (hH : 0≤H)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,sharpSectionWeight H ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (H*(axialSliceVolume (openRepresentative E) i t).toReal/axialPerimeterDensity μ i t) := by
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hO := (isOpen_openRepresentative E).measurableSet
  have hp := planarTorusPerimeter_slice_ae_le hO (hμ.congr_ae hOE.symm) i ha
  filter_upwards [hp,isMinimizerAt_planar_profile_circle hV hE hmin hR hd i] with t ht hs
  apply sharpSectionWeight_le hH
  · refine ⟨ENNReal.toReal_nonneg,?_⟩
    simpa using (ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞)≠⊤)
      (axialSliceVolume_le_one (openRepresentative E) i t))
  · exact axialPerimeterDensity_nonneg μ i t
  · have hh := ENNReal.toReal_mono (by simp) (hs.trans ht)
    simpa only [axialSliceVolume,measureReal_def,ENNReal.toReal_ofReal (unitPlanarProfile_nonneg _),
      ENNReal.toReal_ofReal (axialPerimeterDensity_nonneg μ i t)] using hh

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae_oai := @OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae_oai
