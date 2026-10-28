-- Prove2me | solution 1 for OAI.CubicTorus.axial_integrated_flux
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:16:43.902725+00:00
-- url     : https://prove2.me/submissions/99141328-ebe7-4319-bcb6-0ad51d45ec09

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

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

end CubicTorus

end
end

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

lemma normal_component_abs_le_one (ν : NormalSphere) (i : Fin 3) :
    |(ν : Cover) i|≤1 := by
  have hh := normalSphere_coordinate_sq_le ν i
  nlinarith [sq_abs ((ν : Cover) i),abs_nonneg ((ν : Cover) i)]

lemma axialPositiveFluxMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPositiveFluxMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialPositiveFluxMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialPositiveFluxMarginal μ i : Measure AxisCircle))=
      ∫ z,(1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1+((z.2 : Cover) i))) :=
    (continuous_const.add (normal_component_continuous i)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (by have hh := (abs_le.mp (normal_component_abs_le_one z.2 i)).1; linarith),smul_eq_mul]

lemma axialAreaMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialAreaMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  exact integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable

lemma axialNormalDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalDensity μ i) :=
  Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

lemma axialNormalDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialNormalDensity μ i) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma axialNormalDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialNormalDensity μ i t*f t)=
      ∫ z,((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPositiveFluxMarginal_absolutelyContinuous i ha
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    (hf.comp (normal_axisCircle_continuous i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi'' : Integrable (fun z : NormalBundle ↦ (1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    ((continuous_const.add (normal_component_continuous i)).mul (hf.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [axialNormalDensity,sub_mul]
  rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr (hi _))
    ((integrable_toReal_rnDeriv_mul_iff ha).mpr (hi _)),
    integral_toReal_rnDeriv_mul hp,integral_toReal_rnDeriv_mul ha,
    axialPositiveFluxMarginal_integral μ i hf,axialAreaMarginal_integral μ i hf,←integral_sub hi'' hi']
  apply integral_congr_ae
  filter_upwards [] with z
  ring

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

lemma normalTransverseLength_le_one (i : Fin 3) (z : NormalBundle) :
    normalTransverseLength i z≤1 := by
  have h := normalTransverseLength_sq i z
  nlinarith [sq_nonneg ((z.2 : Cover) i)]

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

lemma axialPerimeterDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialPerimeterDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
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

lemma axialAreaDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialAreaDensity μ i) := Measure.integrable_toReal_rnDeriv
lemma axialSecondDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialSecondDensity μ i) := Measure.integrable_toReal_rnDeriv
lemma axialSecondDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialSecondDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma axialAreaDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialAreaDensity μ i t*f t)=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialAreaDensity]
  rw [integral_toReal_rnDeriv_mul ha,axialAreaMarginal_integral μ i hf]

lemma axialSurfaceMarginal_ac_of_area {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialSecondDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialSecondDensity μ i t*f t)=
      ∫ z,(normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialSecondDensity]
  rw [integral_toReal_rnDeriv_mul (axialSurfaceMarginal_ac_of_area i ha),
    axialSurfaceMarginal_integral μ i hf]
  apply integral_congr_ae
  filter_upwards [] with z
  have hh := normalTransverseLength_sq i z
  rw [show 1-((z.2 : Cover) i)^2=(normalTransverseLength i z)^2 by linarith]
  ring

lemma axialPerimeterDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
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

theorem axial_moment_nonneg_ae {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (a b c d : ℝ)
    (hpos : ∀ z : NormalBundle,0≤a+b*normalTransverseLength i z+
      c*(normalTransverseLength i z)^2+d*((z.2 : Cover) i)) :
    ∀ᵐ t,0≤a*axialAreaDensity μ i t+b*axialPerimeterDensity μ i t+
      c*axialSecondDensity μ i t+d*axialNormalDensity μ i t := by
  have hi := (((axialAreaDensity_integrable μ i).const_mul a).add
    ((axialPerimeterDensity_integrable μ i).const_mul b)).add
    ((axialSecondDensity_integrable μ i).const_mul c) |>.add ((axialNormalDensity_integrable μ i).const_mul d)
  apply integrable_circle_nonneg_of_smooth_pairing hi
  intro ψ hψ hp hn
  let f := hp.lift
  have hf : Continuous f := continuous_periodic_lift hp hψ.continuous
  have hfn (t : AxisCircle) : 0≤f t := by
    induction t using Quotient.inductionOn with | h t => exact hn t
  have hA := circle_integrable_mul_continuous (axialAreaDensity_integrable μ i) hf
  have hP := circle_integrable_mul_continuous (axialPerimeterDensity_integrable μ i) hf
  have hT := circle_integrable_mul_continuous (axialSecondDensity_integrable μ i) hf
  have hD := circle_integrable_mul_continuous (axialNormalDensity_integrable μ i) hf
  change 0≤∫ t,(a*axialAreaDensity μ i t+b*axialPerimeterDensity μ i t+
    c*axialSecondDensity μ i t+d*axialNormalDensity μ i t)*f t
  simp only [add_mul,mul_assoc]
  have hAP : Integrable (fun t ↦ a*(axialAreaDensity μ i t*f t)+b*(axialPerimeterDensity μ i t*f t)) :=
    (hA.const_mul a).add (hP.const_mul b)
  have hAPT : Integrable (fun t ↦ a*(axialAreaDensity μ i t*f t)+b*(axialPerimeterDensity μ i t*f t)+
      c*(axialSecondDensity μ i t*f t)) := hAP.add (hT.const_mul c)
  rw [integral_add hAPT (hD.const_mul d),integral_add hAP (hT.const_mul c),
    integral_add (hA.const_mul a) (hP.const_mul b)]
  simp only [integral_const_mul]
  rw [axialAreaDensity_pairing i ha hf,axialPerimeterDensity_pairing i ha hf,
    axialSecondDensity_pairing i ha hf,axialNormalDensity_pairing i ha hf]
  have hci (g : NormalBundle → ℝ) (hg : Continuous g) : Integrable g (μ : Measure NormalBundle) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hk : Continuous (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) :=
    hf.comp (normal_axisCircle_continuous i)
  have hα := normalTransverseLength_continuous i
  have hν := normal_component_continuous i
  rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,←integral_const_mul]
  have hia : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) := hci _ (continuous_const.mul hk)
  have hib : Integrable (fun z : NormalBundle ↦ b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul (hα.mul hk))
  have hic : Integrable (fun z : NormalBundle ↦ c*((normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul ((hα.pow 2).mul hk))
  have hid : Integrable (fun z : NormalBundle ↦ d*(((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul (hν.mul hk))
  have hiab : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)+b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hia.add hib
  have hiabc : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)+b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))+c*((normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hiab.add hic
  rw [←integral_add hia hib,←integral_add hiab hic,←integral_add hiabc hid]
  apply integral_nonneg
  intro z
  convert mul_nonneg (hpos z) (hfn (((z.1 : Cover) i) : AxisCircle)) using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

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

lemma sqrt_cutoff : Real.sqrt (1 - cutoff ^ 2) = 1 / 7 := by
  rw [cutoff_sq]
  norm_num

lemma rawWeight_cutoff : rawWeight cutoff = ell := by
  rw [rawWeight, sqrt_cutoff, cutoff_sq]
  norm_num [lambda, ell]

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

lemma weight_le_rawWeight {x : ℝ} (hx : x ∈ Ico 0 1) : weight x ≤ rawWeight x := by
  by_cases hxc : x ≤ cutoff
  · simp [weight, min_eq_left hxc]
  · rw [weight, min_eq_right (le_of_not_ge hxc), rawWeight_cutoff]
    exact rawWeight_lower hx

end CubicTorus.Nesting

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

lemma rational_quadratic_discriminant {a b c : ℝ}
    (h : ∀ q : ℚ,0≤a*(q : ℝ)^2-2*b*(q : ℝ)+c) : b^2≤a*c := by
  have hr (r : ℝ) : 0≤a*r^2-2*b*r+c := by
    exact Rat.denseRange_cast.induction_on r (isClosed_le continuous_const (by fun_prop)) h
  have hh := discrim_le_zero (a := a) (b := -2*b) (c := c) (fun r ↦ by
    have ht := hr r
    nlinarith only [ht])
  dsimp [discrim] at hh
  nlinarith only [hh]

theorem axial_moment_bounds {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t,axialSecondDensity μ i t≤axialAreaDensity μ i t ∧
      axialSecondDensity μ i t≤axialPerimeterDensity μ i t ∧
      (axialPerimeterDensity μ i t)^2≤axialAreaDensity μ i t*axialSecondDensity μ i t ∧
      (axialNormalDensity μ i t)^2≤axialAreaDensity μ i t*
        (axialAreaDensity μ i t-axialSecondDensity μ i t) := by
  have hta := axial_moment_nonneg_ae i ha 1 0 (-1) 0 (fun z ↦ by
    have hh := normalTransverseLength_sq i z
    nlinarith [sq_nonneg ((z.2 : Cover) i)])
  have htp := axial_moment_nonneg_ae i ha 0 1 (-1) 0 (fun z ↦ by
    have h0 := normalTransverseLength_nonneg i z
    have h1 := normalTransverseLength_le_one i z
    nlinarith)
  have hp : ∀ᵐ t,∀ q : ℚ,0≤axialAreaDensity μ i t*(q : ℝ)^2-
      2*axialPerimeterDensity μ i t*(q : ℝ)+axialSecondDensity μ i t := by
    apply ae_all_iff.mpr
    intro q
    have hh := axial_moment_nonneg_ae i ha ((q : ℝ)^2) (-2*q) 1 0 (fun z ↦ by
      nlinarith [sq_nonneg (normalTransverseLength i z-(q : ℝ))])
    filter_upwards [hh] with t ht
    nlinarith only [ht]
  have hd : ∀ᵐ t,∀ q : ℚ,0≤axialAreaDensity μ i t*(q : ℝ)^2-
      2*axialNormalDensity μ i t*(q : ℝ)+(axialAreaDensity μ i t-axialSecondDensity μ i t) := by
    apply ae_all_iff.mpr
    intro q
    have hh := axial_moment_nonneg_ae i ha ((q : ℝ)^2+1) 0 (-1) (-2*q) (fun z ↦ by
      have hh := normalTransverseLength_sq i z
      nlinarith [sq_nonneg (((z.2 : Cover) i)-(q : ℝ))])
    filter_upwards [hh] with t ht
    nlinarith only [ht]
  filter_upwards [hta,htp,hp,hd] with t hta htp hp hd
  exact ⟨by linarith,by linarith,rational_quadratic_discriminant hp,rational_quadratic_discriminant hd⟩

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus.Nesting

lemma moment_weight_bound_pos {a p t d : ℝ} (ha : 0<a) (hp : 0<p)
    (ht : 0≤t) (hta : t≤a) (hp2 : p^2≤a*t) (hd2 : d^2≤a*(a-t)) :
    weight (t/p)*|d|≤a-lambda*t := by
  have hw := weight_mem (div_nonneg ht hp.le)
  have hw0 : 0≤weight (t/p) := (by norm_num [ell] : (0 : ℝ)≤ell).trans hw.1
  rcases lt_or_eq_of_le hta with hta|rfl
  · let q := Real.sqrt (t/a)
    have hq0 : 0≤q := Real.sqrt_nonneg _
    have hq2 : q^2=t/a := Real.sq_sqrt (div_nonneg ht ha.le)
    have haq : a*q^2=t := by rw [hq2]; field_simp
    have hq1 : q<1 := by
      have hh : t/a<1 := (div_lt_one ha).mpr hta
      nlinarith
    have hqp : q*p≤t := by
      have hb := mul_le_mul_of_nonneg_right hp2 (sq_nonneg q)
      have he : a*t*q^2=t^2 := by rw [show a*t*q^2=(a*q^2)*t by ring,haq]; ring
      rw [he] at hb
      nlinarith [mul_nonneg hq0 hp.le]
    have hqm : q≤t/p := (le_div_iff₀ hp).mpr hqp
    have hW := (antitoneOn_weight hq0 (div_nonneg ht hp.le) hqm).trans
      (weight_le_rawWeight ⟨hq0,hq1⟩)
    let s := Real.sqrt (1-q^2)
    have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
    have hs2 : s^2=1-q^2 := Real.sq_sqrt (by nlinarith)
    have has : (a*s)^2=a*(a-t) := by
      linear_combination a^2*hs2-a*haq
    have hd : |d|≤a*s := by nlinarith [sq_abs d,abs_nonneg d,mul_pos ha hs]
    calc
      weight (t/p)*|d|≤weight (t/p)*(a*s) := mul_le_mul_of_nonneg_left hd hw0
      _ ≤ rawWeight q*(a*s) := mul_le_mul_of_nonneg_right hW (mul_nonneg ha.le hs.le)
      _=a-lambda*t := by
        rw [show rawWeight q*(a*s)=a*(rawWeight q*s) by ring]
        have he : rawWeight q*s=1-lambda*q^2 := by
          exact div_mul_cancel₀ _ hs.ne'
        rw [he]
        rw [show a*(1-lambda*q^2)=a-lambda*(a*q^2) by ring,haq]
  · have hd : d=0 := by nlinarith [sq_nonneg d]
    rw [hd,abs_zero,mul_zero]
    norm_num [lambda]
    linarith

lemma moment_weight_bound {a p t d : ℝ} (ha : 0≤a) (hp : 0≤p)
    (ht : 0≤t) (hta : t≤a) (htp : t≤p) (hp2 : p^2≤a*t) (hd2 : d^2≤a*(a-t)) :
    weight (t/p)*|d|≤a-lambda*t := by
  rcases eq_or_lt_of_le ha with ha|ha
  · subst a
    have ht0 : t=0 := le_antisymm hta ht
    have hp0 : p=0 := by nlinarith [sq_nonneg p]
    have hd0 : d=0 := by nlinarith [sq_nonneg d]
    simp [ht0,hp0,hd0]
  rcases eq_or_lt_of_le hp with hp|hp
  · subst p
    have ht0 : t=0 := le_antisymm htp ht
    have hd : |d|≤a := by rw [ht0] at hd2; nlinarith [sq_abs d,abs_nonneg d]
    have hw : weight 0=1 := by simp [weight,min_eq_left cutoff_pos.le,rawWeight]
    simpa [ht0,hw] using hd
  · exact moment_weight_bound_pos ha hp ht hta hp2 hd2

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  apply continuousOn_rawWeight.comp (continuous_id.min continuous_const).continuousOn
  intro x hx
  exact ⟨le_min hx cutoff_pos.le,min_le_right _ _⟩

end CubicTorus.Nesting

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_nesting_weight_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (hn : ∀ x,0≤f x) : Measurable (fun x ↦ Nesting.weight (f x)) := by
  have hc : Continuous (fun t : ℝ ↦ Nesting.weight (max t 0)) :=
    Nesting.continuousOn_weight.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have hh := hc.measurable.comp hf
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact congrArg Nesting.weight (max_eq_left (hn x)).symm

lemma axialAreaDensity_integral {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,axialAreaDensity μ i t)=(μ.mass : ℝ) := by
  have hh := axialAreaDensity_pairing i ha (f := fun _ ↦ 1) continuous_const
  simpa only [mul_one,integral_const,smul_eq_mul,mul_one,Measure.real_def,
    ←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal] using hh

lemma axialSecondDensity_integral {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,axialSecondDensity μ i t)=axialTransverseMass μ i := by
  have hh := axialSecondDensity_pairing i ha (f := fun _ ↦ 1) continuous_const
  simp only [mul_one] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with z
  have he := normalTransverseLength_sq i z
  linarith

lemma axial_weighted_normal_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (fun t ↦ Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|) := by
  have hf := measurable_nesting_weight_comp
    ((axialSecondDensity_measurable μ i).div (axialPerimeterDensity_measurable μ i))
    (fun t ↦ div_nonneg ENNReal.toReal_nonneg (axialPerimeterDensity_nonneg μ i t))
  apply Integrable.mono' (axialNormalDensity_integrable μ i).abs
    (hf.mul (axialNormalDensity_measurable μ i).abs).aestronglyMeasurable
  filter_upwards [] with t
  have hm := Nesting.weight_mem (div_nonneg (show 0≤axialSecondDensity μ i t from ENNReal.toReal_nonneg)
    (axialPerimeterDensity_nonneg μ i t))
  have hn : 0≤Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t) :=
    (by norm_num [Nesting.ell] : (0 : ℝ)≤Nesting.ell).trans hm.1
  change ‖Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
    |axialNormalDensity μ i t|‖≤|axialNormalDensity μ i t|
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hn,abs_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) hm.2

theorem axial_integrated_flux_oai {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(μ.mass : ℝ) := by
  have hh := integral_mono_ae (axial_weighted_normal_integrable μ i)
    ((axialAreaDensity_integrable μ i).sub ((axialSecondDensity_integrable μ i).const_mul Nesting.lambda)) ?_
  · simp only [Pi.sub_apply] at hh
    rw [integral_sub (axialAreaDensity_integrable μ i)
      ((axialSecondDensity_integrable μ i).const_mul Nesting.lambda),integral_const_mul,
      axialAreaDensity_integral i ha,axialSecondDensity_integral i ha] at hh
    linarith
  filter_upwards [axial_moment_bounds i ha] with t ht
  exact Nesting.moment_weight_bound ENNReal.toReal_nonneg (axialPerimeterDensity_nonneg μ i t)
    ENNReal.toReal_nonneg ht.1 ht.2.1 ht.2.2.1 ht.2.2.2

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.axial_integrated_flux_oai := @OAI.CubicTorus.axial_integrated_flux_oai
