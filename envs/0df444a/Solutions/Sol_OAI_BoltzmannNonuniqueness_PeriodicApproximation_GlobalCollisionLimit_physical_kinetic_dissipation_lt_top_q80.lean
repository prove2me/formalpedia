-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:20:43.290176+00:00
-- url     : https://prove2.me/submissions/48017310-4162-44c2-8715-bad3c6db89a8

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_physical_entropy_dissipation_q80

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Lower semicontinuity of entropy production

The extended scalar entropy production is lower semicontinuous along positive
approximations of nonnegative products. In particular its value is infinite
when exactly one limiting product vanishes. Weighted Fatou then passes this
production to a limit, without a domination hypothesis or a finite-production
assumption. The final specialization applies to positive regularizations of
four nonnegative factors.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem measurable_extendedEntropyProduction {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => extendedEntropyProduction (a x) (b x)) := by
  unfold extendedEntropyProduction
  apply Measurable.ite
    ((measurableSet_eq_fun ha measurable_const).inter
      (measurableSet_eq_fun hb measurable_const)) measurable_const
  exact Measurable.ite
    ((measurableSet_lt measurable_const ha).inter (measurableSet_lt measurable_const hb))
    ((ha.sub hb).mul ((ha.div hb).log)).ennreal_ofReal measurable_const

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]


omit [MeasurableSpace X] in
theorem postRate_formula (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change collisionKernel (scatterLeft z.1.2.1 z.1.2.2 z.2) (scatterRight z.1.2.1 z.1.2.2 z.2) z.2*
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [collisionKernel_scatter _ _ _ hw]

theorem preRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) : Measurable (preRate f) := by
  unfold preRate collisionKernel normalComponent
  fun_prop

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r671c35_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem collisionGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := by
  have ha := (measurePreserving_prodAssoc μ (volume : Measure Velocity) (volume : Measure Velocity)).symm.prod
    (MeasurePreserving.id sphereArea)
  have hb := measurePreserving_prodAssoc (μ.prod (volume : Measure Velocity))
    (volume : Measure Velocity) sphereArea
  have he : (⇑(collisionGrouping (X := X))) =
      MeasurableEquiv.prodAssoc ∘ Prod.map (MeasurableEquiv.prodAssoc.symm)
        (id : Sphere → Sphere) := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using hb.comp ha

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Slice mass bounds for the physical gain and loss -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem gainDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gainDensity f) :=
  ((preRate_measurable hf).comp (scatterTriple_measurable.comp
    collisionGrouping.symm.measurable)).stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_MeasurableResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurability of a parameter-dependent interval primitive -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive
variable {P : Type*} [MeasurableSpace P]

theorem measurable_interval_primitive {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (fun z : ℝ × P => ∫ s in 0..z.1, f (s,z.2)) := by
  have hm : Measurable (fun q : (ℝ × P) × ℝ => f (q.2,q.1.2)) :=
    hf.comp (measurable_snd.prodMk measurable_fst.snd)
  have hplus : Measurable (fun q : (ℝ × P) × ℝ =>
      if 0 < q.2 ∧ q.2 ≤ q.1.1 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
  have hminus : Measurable (fun q : (ℝ × P) × ℝ =>
      if q.1.1 < q.2 ∧ q.2 ≤ 0 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) measurable_const
  have hp := (hplus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hn := (hminus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hp.sub hn using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change (∫ s in Ioc 0 z.1, f (s,z.2))-(∫ s in Ioc z.1 0, f (s,z.2)) = _
  rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator,mem_Ioc,Pi.sub_apply]

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalFrequencyWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical loss frequency in kinetic spacetime coordinates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem kineticFrequency_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kineticFrequency f) := by
  have hm : Measurable (fun p : (X × Velocity) × Velocity => ‖p.1.2-p.2‖*f (p.1.1,p.2)) := by
    fun_prop
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ExtendedProductionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneity of the extended entropy production, including its infinite cases -/

noncomputable section

open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_scale {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    extendedEntropyProduction (c*a) (c*b) = ENNReal.ofReal c*extendedEntropyProduction a b := by
  by_cases hcz : c = 0
  · subst c
    simp [extendedEntropyProduction]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
  have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcp)
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      simp [extendedEntropyProduction,hbz,(mul_pos hcp hbp).ne',hcn]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  by_cases hbz : b = 0
  · subst b
    simp [extendedEntropyProduction,haz,(mul_pos hcp hap).ne',hcn]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hcap := mul_pos hcp hap
  have hcbp := mul_pos hcp hbp
  simp only [extendedEntropyProduction,hap,hbp,hcap,hcbp,haz,hbz,hcap.ne',hcbp.ne',
    and_self,↓reduceIte]
  have hdiv : c*a/(c*b) = a/b := by field_simp
  rw [hdiv,← ENNReal.ofReal_mul hc]
  congr 1
  ring

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision-rate dissipation is the physical entropy dissipation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea : SFinite ((volume : Measure BoltzmannNonuniqueness.Velocity).prod
    BoltzmannNonuniqueness.sphereArea) := Measure.prod.instSFinite

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem kernelEntropyProduction_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kernelEntropyProduction f) := by
  have hpost : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2)*
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  have hpre : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,p.2.1)*f (p.1,p.2.2.1)) := by fun_prop
  have hK : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      collisionKernel p.2.1 p.2.2.1 p.2.2.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact hK.ennreal_ofReal.mul (measurable_extendedEntropyProduction hpost hpre)

theorem collisionEntropyGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionEntropyGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea))) :=
  (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).comp (collisionGrouping_measurePreserving μ)

theorem rateProduction_eq_kernel {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction (postRate f z) (preRate f z) =
      kernelEntropyProduction f (collisionEntropyGrouping z) := by
  rw [postRate_formula]
  change extendedEntropyProduction
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)) =
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*extendedEntropyProduction
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  simpa only [mul_assoc] using
    extendedEntropyProduction_scale (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

theorem rateDissipation_eq_kernel {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    rateDissipation μ f = (4:ℝ≥0∞)⁻¹ * ∫⁻ p, kernelEntropyProduction f p
      ∂μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) := by
  unfold rateDissipation
  simp_rw [rateProduction_eq_kernel hf]
  rw [(collisionEntropyGrouping_measurePreserving μ).lintegral_comp
    (kernelEntropyProduction_measurable hfm)]

end BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness

theorem kineticDensity_rateDissipation {F : Evolution}
    (hFm : Measurable (fun p : ℝ × Phase => F p.1 p.2))
    (hFn : ∀ t z, 0 ≤ F t z) (T : ℝ) :
    CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume T) (kineticDensity F) =
      ∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t) := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  rw [CollisionCompactness.rateDissipation_eq_kernel hkin (fun p => hFn _ _)]
  let ν := (volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)
  let G : ℝ × (Position × (Velocity × (Velocity × Sphere))) → ℝ≥0∞ :=
    fun p => CollisionCompactness.kernelEntropyProduction (F p.1) p.2
  have hG : Measurable G := by
    have hm := CollisionCompactness.kernelEntropyProduction_measurable hkin
    change Measurable (fun p : ℝ × (Position × (Velocity × (Velocity × Sphere))) =>
      CollisionCompactness.kernelEntropyProduction (kineticDensity F) ((p.1,p.2.1),p.2.2))
    exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have he := (measurePreserving_prodAssoc (volume.restrict (Icc (0:ℝ) T))
    (volume : Measure Position) ν).lintegral_comp hG
  change (4:ℝ≥0∞)⁻¹ * ∫⁻ p, G (MeasurableEquiv.prodAssoc p)
    ∂((volume.restrict (Icc (0:ℝ) T)).prod (volume : Measure Position)).prod ν = _
  rw [he,lintegral_prod _ hG.aemeasurable]
  rw [← lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  rfl

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicWeakCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak velocity averages of the same global periodic limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.kineticProfile_measurable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) : Measurable G.kineticProfile :=
  G.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicPhysicalGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The full physical gain is the almost-everywhere limit on characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem physicalCharacteristicGain_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (physicalCharacteristicGain f) :=
  (gainDensity_measurable hfm).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicStrongAverages
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual physical frequencies and survival along torus characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem physicalCharacteristicFrequency_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hf : Measurable f) : Measurable (physicalCharacteristicFrequency f) :=
  (kineticFrequency_measurable hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalLinearContinuous
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint measurability of the actual linear characteristic profile -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (physicalLinearProfile f F) := by
  have hk := physicalCharacteristicFrequency_measurable hFm
  have hg := physicalCharacteristicGain_measurable hFm
  have hK := TransportPrimitive.measurable_interval_primitive hk
  have hA := TransportPrimitive.measurable_interval_primitive (hK.exp.mul hg)
  exact hK.neg.exp.mul ((hfm.comp measurable_snd).add hA)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEvolution
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The measurable nonnegative evolution defined by the characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalEvolution_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (fun z : ℝ × Phase => physicalEvolution f F z.1 z.2) := by
  apply measurable_const.max
  exact (physicalLinearProfile_measurable hfm hFm).comp
    (measurable_fst.prodMk (TorusFlight.measurable_flight.comp
      (measurable_fst.neg.prodMk measurable_snd)))

theorem physicalEvolution_nonneg (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (t : ℝ) (p : Phase) : 0 ≤ physicalEvolution f F t p := le_max_left _ _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Physical collision fibers and separate normalized gain/loss integrability -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80_oai
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))
      (kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)) < ⊤ := by
  have hEm := physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable
  have hDn : (∫⁻ s in Icc (0:ℝ) T,
      entropyDissipation (physicalEvolution f G.weakLimit.kineticProfile s)) ≤
      ENNReal.ofReal (relativeEntropy f) :=
    (le_add_of_nonneg_left zero_le).trans (G.physical_entropy_dissipation_q80 hf hi hT)
  change rateDissipation (AnnularEnvelope.timePositionVolume T)
    (kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)) < ⊤
  rw [kineticDensity_rateDissipation hEm (fun _ _ => physicalEvolution_nonneg _ _ _ _) T]
  exact hDn.trans_lt ENNReal.ofReal_lt_top

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80_oai
