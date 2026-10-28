-- Prove2me | solution 1 for OAI.CoulombAtom.actual_scaled_original_cap_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:41:58.999477+00:00
-- url     : https://prove2.me/submissions/7553a20b-66ec-4ee7-a692-eb06f5633d15

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_OwnProbabilityTailTiltState_expandedAnnulus_small_event_integral
import Theorems.Thm_OAI_CoulombAtom_OwnProbabilityTailTiltState_rare_cap_event_of_cell

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawPotential_measurable {N : ℕ} (y : Space) : Measurable (rawPotential (N := N) y) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.div (configuration_distance_measurable y i))

lemma formRawLaw_ae_no_poles {N : ℕ} (ψ : FormVector N) (y : Space) :
    ∀ᵐ x ∂formRawLaw ψ, ∀ i, x i ≠ y := by
  apply (withDensity_absolutelyContinuous volume _).ae_le
  exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_upper {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : masterWidth c₁ r₀ s x ≤ c₁*masterBaseDistance r₀ x*s^masterExponent := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_min hD.le hs.le) (min_le_right _ _) masterExponent_nonneg)
    (mul_nonneg hc hD.le)

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_mass {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    ∫ y, masterKernel c₁ r₀ s g x y = 1 := by
  unfold masterKernel
  rw [integral_sub_right_eq_self (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) x,
    scaledRealPacket_mass (masterWidth_pos hc hr hs x) g,hgn]

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_MasterPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma scaled_packet_density_radial (b : ℝ) {g : Space → ℝ} (hr : IsRadial g) :
    IsRadial (fun x => (scaledRealPacket b g x)^2) := by
  intro x y hxy
  dsimp only
  rw [scaledRealPacket_radial b hr x y hxy]

lemma scaled_packet_density_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) (x : Space) (hx : (scaledRealPacket b g x)^2 ≠ 0) :
    ‖x‖ ≤ b := (scaledRealPacket_support hb hs (by intro hz; exact hx (by rw [hz]; norm_num))).le

lemma scaled_packet_potential_le {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : x ≠ 0) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x ≤ 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact pow_two _
  have hh := radial_potential_le_point (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (fun z => sq_nonneg _)
    (scaled_packet_density_radial b hr) hb.le (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma masterKernel_potential_centered (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    tfPotential (masterKernel c₁ r₀ s g x) y =
      tfPotential (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) (y-x) :=
  integral_translated_pole (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) y x

lemma masterKernel_potential_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ tfPotential (masterKernel c₁ r₀ s g x) y :=
  tfPotential_nonneg (ae_of_all _ (masterKernel_nonneg c₁ r₀ s g x)) y

lemma masterKernel_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    tfPotential (masterKernel c₁ r₀ s g x) y ≤ 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_le (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (sub_ne_zero.mpr hxy.symm)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

lemma scaled_packet_density_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
  convert! (scaledRealPacket_compact hb hg).mul_right (f' := scaledRealPacket b g) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact pow_two _

lemma masterKernel_pole_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (y : Space) :
    Measurable (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

lemma masterKernel_pole_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x y : Space) :
    Integrable (fun z => masterKernel c₁ r₀ s g x z/‖y-z‖) := by
  have hη := scaled_packet_density_compact (masterWidth_pos hc hr hs x) hcg
  have hηc := (scaledRealPacket_smooth (masterWidth c₁ r₀ s x) hg).continuous.pow 2
  exact translated_pole_integrable (hηc.integrable_of_hasCompactSupport hη)
    (hηc.memLp_of_hasCompactSupport hη) y x

lemma master_configuration_potential_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (masterKernel_pole_measurable hc hr hs hg.continuous y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_potential_nonneg c₁ r₀ s g (x i) y))]
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i)

lemma master_configuration_pole_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖)
      (ν.prod volume) := by
  have hm : Measurable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖) :=
    (Finset.measurable_sum _ (fun i _ => (masterKernel_joint_continuous hc hr hs hg.continuous).measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).div (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => ?_),?_⟩
  · simp only [Finset.sum_div]
    exact integrable_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)
  · have hp := master_configuration_potential_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Finset.sum_div]
    simp_rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
      div_nonneg (masterKernel_nonneg c₁ r₀ s g (x i) _) (norm_nonneg _)))]
    exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)

theorem master_configuration_potential_fubini {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    tfPotential (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y =
      ∫ x, ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y ∂ν := by
  change (∫ z, (∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν)/‖y-z‖) = _
  calc
    _ = ∫ z, ∫ x, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖ ∂ν := by simp only [integral_div]
    _ = ∫ x, (∫ z, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖) ∂ν :=
      integral_integral_swap (master_configuration_pole_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs).swap
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [Finset.sum_div]
        exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y))

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma originalRawKernel_comp {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) :
    originalRawKernel μ ell j ∘ₘ ((physicalObservationLaw μ K).map (originalDatum ell j)) = μ := by
  rw [originalRawKernel,condDistrib_comp_map (originalDatum_measurable ell j).aemeasurable
    measurable_fst.aemeasurable]
  simp [physicalObservationLaw,Measure.map_fst_prod]

lemma originalRawKernel_ae {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {P : Configuration N → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ᵐ x ∂originalRawKernel μ ell j (originalDatum ell j z), P x := by
  rw [←originalRawKernel_comp μ ell j] at hP
  exact ae_of_ae_map (originalDatum_measurable ell j).aemeasurable (Measure.ae_ae_of_ae_comp hP)

lemma originalRawKernel_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {f : Configuration N → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      Integrable f (originalRawKernel μ ell j (originalDatum ell j z)) := by
  have hx := originalDatum_measurable (N := N) ell j
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hi0 : Integrable (fun a : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f a.1)
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  have hi1 : Integrable (fun p : OriginalDatum N K ell j × Configuration N => f p.2)
      ((physicalObservationLaw μ K).map (fun a => (originalDatum ell j a,a.1))) := by
    apply (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      (hx.prodMk measurable_fst).aemeasurable).mpr
    exact hi0
  exact hi1.condDistrib_ae hx.aemeasurable measurable_fst.aemeasurable

lemma kernelPosteriorTest_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    Integrable (fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z))
      (physicalObservationLaw μ K) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  exact integrable_condExp.congr (kernelPosteriorTest_eq μ ell j hg hi0)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterRecovery
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma masterKernel_test_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆
      closedBall y (2*masterWidth c₁ r₀ s y) :=
  ((masterKernel_uniform_test_constants hg hgs).choose_spec.2 c₁ r₀ s hc hcL hr hs hs1 y).1

lemma masterCenteredKernel_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (masterCenteredKernel c₁ r₀ s g y) ⊆
      closedBall 0 (2*masterWidth c₁ r₀ s y) := by
  intro x hx
  have hh := masterKernel_test_support hg hgs hc hcL hr hs hs1 y hx
  simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_nonneg {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) :
    0 ≤ jointMasterPosterior μ ell j c₁ r₀ s g z y :=
  integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

lemma masterKernel_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    Integrable (masterKernel c₁ r₀ s g x) := by
  by_contra h
  have hm := masterKernel_mass hc hr hs hgn x
  rw [integral_undef h] at hm
  norm_num at hm

lemma masterConfigurationKernel_integrable {N : ℕ} (ν : Measure (Configuration N)) [IsFiniteMeasure ν]
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)
      (ν.prod volume) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  apply (integrable_prod_iff ((Finset.measurable_sum _ (fun i _ => hm.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)).mpr
  refine ⟨ae_of_all _ (fun x => integrable_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))),?_⟩
  have he (x : Configuration N) :
      (∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) = (N:ℝ) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) _))]
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp only [masterKernel_mass hc hr hs hgn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  change Integrable (fun x : Configuration N => ∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) ν
  simpa only [he] using (integrable_const (N:ℝ) : Integrable (fun _ : Configuration N => (N:ℝ)) ν)

lemma jointMasterPosterior_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    Integrable (jointMasterPosterior μ ell j c₁ r₀ s g z) :=
  (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn).integral_prod_right

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

lemma masterKernel_global_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖masterKernel c₁ r₀ s g x y‖ ≤ C := by
  have hc2 : HasCompactSupport (fun x => (g x)^2) := hcg.mul_left
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport hc2.norm
  let δ := c₁*r₀^(1+masterExponent)
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos hr _)
  refine ⟨δ⁻¹^3*‖(g z)^2‖,by positivity,fun x y => ?_⟩
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ δ⁻¹ := by
    apply inv_anti₀ hδ
    exact masterWidth_lower hc.le hr hrs x
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x),norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) 3)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hz _) (norm_nonneg _) (by positivity)

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma masterConfigurationDensity_bound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, ‖masterConfigurationDensity (N := N) c₁ r₀ s g z y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterKernel_global_bound hc hr hs hrs hg hcg
  refine ⟨N*C,by positivity,fun z y => ?_⟩
  calc
    _ ≤ ∑ i : Fin N, ‖masterKernel c₁ r₀ s g (z i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hC (z i) y)
    _ = N*C := by simp

lemma jointMasterPosterior_global_bound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d y, ‖jointMasterPosterior μ ell j c₁ r₀ s g d y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  refine ⟨C,hCn,fun d y => ?_⟩
  calc
    _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j d :=
      norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun z => hC z y)
    _ = C := by simp

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma originalMasterField_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (originalMasterField μ ell j c₁ r₀ s g)) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (((originalDatum_measurable ell j).comp measurable_fst).prodMk measurable_snd)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchOscillationConstant_pos : 0 < tfPatchOscillationConstant :=
  (Classical.choose_spec (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)).1

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterPosteriorPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma jointMasterPosterior_potential_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact master_configuration_potential_fubini _ y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_potential_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchDensityCapConstant_pos : 0 < tfPatchDensityCapConstant := by
  exact Real.rpow_pos_of_pos (div_pos tfPatchCapConstant_pos (mul_pos (by norm_num) tfKinetic_pos)) _

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_UnshiftedCellCountBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_radius_lower {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    c₁*r^(1+masterExponent) ≤ masterWidth c₁ r₀ s y := by
  have hd : r ≤ masterBaseDistance r₀ y := hy.trans (le_max_left _ _)
  have hm : r ≤ min (masterBaseDistance r₀ y) s := le_min hd hrs
  rw [masterWidth,Real.rpow_add hr]
  simp only [Real.rpow_one]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hd (Real.rpow_le_rpow hr.le hm masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hd)) hc

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

lemma sharpFreshKineticConstant_one_le : 1 ≤ sharpFreshKineticConstant := by
  have := localizationIMSConstant_nonneg
  have := actualCellMomentConstant_one_le
  have := sharpFreshFieldConstant_one_le
  have hh : 0 ≤ localizationIMSConstant*actualCellMomentConstant+
      sharpFreshFieldConstant*actualCellMomentConstant := by positivity
  unfold sharpFreshKineticConstant
  linarith only [hh]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma sharpOrdinaryDensityConstant_nonneg : 0 ≤ sharpOrdinaryDensityConstant := by
  have hc := le_trans zero_le_one actualCellMomentConstant_one_le
  have hk := le_trans zero_le_one sharpFreshKineticConstant_one_le
  unfold sharpOrdinaryDensityConstant
  positivity

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CapBudgetHomogeneityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpLocalPotentialBudget_nonneg {a m u : ℝ} (ha : 0 < a) (_hm : 0 ≤ m)
    (hu : 0 ≤ u) : 0 ≤ sharpLocalPotentialBudget a m u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  positivity

lemma sharpPatchRemainder_scale {a b m t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (ht : 1 ≤ t) :
    sharpPatchRemainder a b (t*m) ≤ t^2*sharpPatchRemainder a b m := by
  let L := localizationIMSConstant/b^2*Real.sqrt (8*b/a)*actualCellMomentConstant+
    b⁻¹^2*neumannRemainderConstant*actualCellMomentConstant+
    (((2*Real.pi+1)/2)/b)*actualCellMomentConstant+
    ((packetDirichlet canonicalRealPacket/2)*b⁻¹^2)*(768*sharpFreshFieldConstant)
  let P := b⁻¹^2*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)
  let Q := sharpFreshFieldConstant/a*Real.sqrt (8*b/a)*actualCellMomentConstant
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hPP : 0 ≤ P := by dsimp [P]; positivity
  have he (v : ℝ) : sharpPatchRemainder a b v = L*v+P*v^(4/3:ℝ)+Q*v^2 := by
    dsimp [sharpPatchRemainder,L,P,Q]
    ring
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htt : t ≤ t^2 := by nlinarith
  have htp : t^(4/3:ℝ) ≤ t^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (4/3:ℝ) ≤ 2)
  rw [he,he,Real.mul_rpow ht0 hm,mul_pow]
  calc
    _ ≤ L*(t^2*m)+P*(t^2*m^(4/3:ℝ))+Q*(t^2*m^2) := by
      gcongr
    _ = _ := by ring

lemma sharpLocalPotentialBudget_scale {a m u t : ℝ} (ha : 0 < a) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (ht : 1 ≤ t) :
    sharpLocalPotentialBudget a (t*m) u ≤ t^2*sharpLocalPotentialBudget a m u := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpLocalPotentialBudget a (t*m) u =
      t^(6/5:ℝ)*sharpLocalPotentialBudget a m u := by
    unfold sharpLocalPotentialBudget
    rw [show sharpOrdinaryDensityConstant*(t*m)^2/a =
      t^2*(sharpOrdinaryDensityConstant*m^2/a) by ring,
      Real.mul_rpow (sq_nonneg t) (by positivity),←Real.rpow_natCast,←Real.rpow_mul ht0]
    norm_num
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (sharpLocalPotentialBudget_nonneg ha hm hu)
  rw [←Real.rpow_two]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (6/5:ℝ) ≤ 2)

lemma localOffsetMass_scale {y : Space} {D t : ℝ}
    (ht : 1 ≤ t) : localOffsetMass (t^2*D) y ≤ t*localOffsetMass D y := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hM : 0 ≤ max (1/(localCellRadius y)^3) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  unfold localOffsetMass
  rw [mul_assoc,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht0]
  nlinarith

lemma sharpPotentialRemainder_scale {a b m D q t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 0 ≤ m) (hq : 0 < q) (ht : 1 ≤ t) :
    sharpPotentialRemainder a b (t*m) (t^2*D) q ≤
      t^2*sharpPotentialRemainder a b m D q := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htt : t ≤ t^2 := by nlinarith
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hT := tfPatchDensityCapConstant_pos.le
  have hpatch := sharpPatchRemainder_scale ha hb hm ht
  have hs : Real.sqrt ((2/q)*(t^2*D+sharpPatchRemainder a b (t*m))) ≤
      t^2*Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m)) := by
    calc
      _ ≤ Real.sqrt ((2/q)*(t^2*D+t^2*sharpPatchRemainder a b m)) := by
        apply Real.sqrt_le_sqrt
        gcongr
      _ = t*Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m)) := by
        rw [show (2/q)*(t^2*D+t^2*sharpPatchRemainder a b m) =
          t^2*((2/q)*(D+sharpPatchRemainder a b m)) by ring,
          Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht0]
      _ ≤ _ := mul_le_mul_of_nonneg_right htt (Real.sqrt_nonneg _)
  have hL1 := sharpLocalPotentialBudget_scale ha hm (by positivity : 0 ≤ q+Real.sqrt 3*b) ht
  have hL2 := sharpLocalPotentialBudget_scale ha hm (by positivity : 0 ≤ Real.sqrt 3*b) ht
  have hc : 2*Real.pi*tfPatchDensityCapConstant*q^2/a^6 ≤
      t^2*(2*Real.pi*tfPatchDensityCapConstant*q^2/a^6) :=
    le_mul_of_one_le_left (by positivity) ht2
  have hl : (Real.sqrt (8*b/a)*actualCellMomentConstant*(t*m))/a ≤
      t^2*((Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a) := by
    calc
      _ = t*((Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right htt (by positivity)
  unfold sharpPotentialRemainder
  nlinarith only [hs,hL1,hL2,hc,hl]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpBudgetMonotoneBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpPatchRemainder_mono {a b m n : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) : sharpPatchRemainder a b m ≤ sharpPatchRemainder a b n := by
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hn : 0 ≤ n := hm.trans hmn
  unfold sharpPatchRemainder
  gcongr

lemma sharpLocalPotentialBudget_mono {a m n u v : ℝ} (ha : 0 < a)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hu : 0 ≤ u) (huv : u ≤ v) :
    sharpLocalPotentialBudget a m u ≤ sharpLocalPotentialBudget a n v := by
  have hC : 0 ≤ sharpOrdinaryDensityConstant := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  gcongr

lemma sharpPotentialRemainder_mono {a b m n D E q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hDE : D ≤ E) (hq : 0 < q) :
    sharpPotentialRemainder a b m D q ≤ sharpPotentialRemainder a b n E q := by
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  unfold sharpPotentialRemainder
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (add_le_add hDE (sharpPatchRemainder_mono ha hb hm hmn)) (by positivity))
        · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
      · exact le_rfl
    · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
  · gcongr

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CapProbabilityWeightBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma physicalFieldCapBudget_scale {y : Space} (hy : y ≠ 0) {b q u D t : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hu : 0 ≤ u) (ht : 1 ≤ t) :
    physicalFieldCapBudget (t^2*D) y b q u ≤ t^2*physicalFieldCapBudget D y b q u := by
  have ha := localCellRadius_pos hy
  have hm : 0 ≤ localOffsetMass D y := le_trans zero_le_one (localOffsetMass_one_le _ _)
  have hm' : 0 ≤ localOffsetMass (t^2*D) y :=
    le_trans zero_le_one (localOffsetMass_one_le _ _)
  have hM := localOffsetMass_scale (y := y) (D := D) ht
  have hS := sharpPotentialRemainder_mono (D := t^2*D) ha hb hm' hM le_rfl hq
  have hL := sharpLocalPotentialBudget_mono ha hm' hM hu le_rfl
  have hPS := sharpPotentialRemainder_scale (D := D) ha hb hm hq ht
  have hLS := sharpLocalPotentialBudget_scale ha hm hu ht
  have hC := tfPatchCapConstant_pos.le
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hcap : tfPatchCapConstant/(localCellRadius y)^4 ≤
      t^2*(tfPatchCapConstant/(localCellRadius y)^4) :=
    le_mul_of_one_le_left (by positivity) ht2
  unfold physicalFieldCapBudget
  nlinarith only [hS,hL,hPS,hLS,hcap]

lemma probability_weighted_cap {y : Space} (hy : y ≠ 0) {b q u D p : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hu : 0 ≤ u) (hp : 0 < p) (hp1 : p ≤ 1) :
    p*physicalFieldCapBudget D y b q u ≤
      p^(3/4:ℝ)*physicalFieldCapBudget (p^(1/4:ℝ)*D) y b q u := by
  have ht : 1 ≤ p^(-(1/8):ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by norm_num)
  have he : (p^(-(1/8):ℝ))^2*p^(1/4:ℝ) = 1 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le,←Real.rpow_add hp]
    norm_num
  have h := physicalFieldCapBudget_scale (D := p^(1/4:ℝ)*D) hy hb hq hu ht
  rw [←mul_assoc,he,one_mul] at h
  have hh := mul_le_mul_of_nonneg_left h hp.le
  have he' : p*(p^(-(1/8):ℝ))^2 = p^(3/4:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
    calc p*p^(-(1/8)*2:ℝ) = p^(1:ℝ)*p^(-(1/8)*2:ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [←Real.rpow_add hp]; norm_num
  simpa only [←mul_assoc,he'] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WidthKernelAmplitude
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WidthKernelAmplitude_scope

open Set Metric
open scoped NNReal

lemma scaledDensity_active_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) (hz : h (a⁻¹ • z) ≠ 0) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  have hap := hq.trans_le ha
  have hbp := hq.trans_le hb
  have hn : ‖a⁻¹ • z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hs hz
  have he : a⁻¹ • z-b⁻¹ • z = (b⁻¹*(b-a)) • (a⁻¹ • z) := by
    rw [smul_smul,←sub_smul]
    congr 1
    field_simp
  have hd : ‖a⁻¹ • z-b⁻¹ • z‖ ≤ q⁻¹*‖a-b‖ := by
    rw [he,norm_smul,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hbp.le),norm_sub_rev b a]
    calc
      _ ≤ (b⁻¹*‖a-b‖)*1 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right (inv_anti₀ hq hb) (norm_nonneg (a-b))
  have hdiff := hh.dist_le_mul (a⁻¹ • z) (b⁻¹ • z)
  simp only [dist_eq_norm] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hd H.coe_nonneg)
  have hi : ‖b⁻¹^3‖ ≤ q⁻¹^3 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hbp.le) _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbp.le) (inv_anti₀ hq hb) 3
  have hid := invCube_norm_sub_le hq ha hb
  have halg : a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z) =
      (a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)+b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z)) := by ring
  rw [halg]
  calc
    _ ≤ ‖(a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)‖+‖b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z))‖ := norm_add_le _ _
    _ = ‖a⁻¹^3-b⁻¹^3‖*‖h (a⁻¹ • z)‖+‖b⁻¹^3‖*‖h (a⁻¹ • z)-h (b⁻¹ • z)‖ := by rw [norm_mul,norm_mul]
    _ ≤ (3*q⁻¹^4*‖a-b‖)*M+(q⁻¹^3)*((H:ℝ)*(q⁻¹*‖a-b‖)) :=
      add_le_add (mul_le_mul hid (hbound _) (norm_nonneg _) (by positivity))
        (mul_le_mul hi hdiff' (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma scaledDensity_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  by_cases hz : h (a⁻¹ • z) ≠ 0
  · exact scaledDensity_active_width_error hq ha hb hh hM hbound hs z hz
  by_cases hz' : h (b⁻¹ • z) ≠ 0
  · simpa only [norm_sub_rev b a,norm_sub_rev (b⁻¹^3*h (b⁻¹ • z)) _] using
      scaledDensity_active_width_error hq hb ha hh hM hbound hs z hz'
  simp only [not_ne_iff] at hz hz'
  simp only [hz,hz',mul_zero,sub_zero,norm_zero]
  positivity

theorem widthKernel_freeze_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (y x : Space) :
    ‖widthKernel t h x y-widthKernel (fun _ => t y) h x y‖ ≤
      32*(3*M+(H:ℝ))*(T:ℝ)*(t y)⁻¹^3 := by
  have hty := hp y
  by_cases hd : ‖x-y‖ ≤ 2*t y
  · have hcl := congrFun (widthKernel_clamp ht hp (by linarith) hs y) x
    rw [hcl]
    have hq : 0 < t y/2 := half_pos (hp y)
    have hby : t y/2 ≤ t y := by linarith [hp y]
    have hh' := scaledDensity_width_error hq (le_max_right (t x) (t y/2)) hby hh hM hbound hs (y-x)
    have htd := (ht.max_const (t y/2)).dist_le_mul x y
    simp only [max_eq_left hby,dist_eq_norm] at htd
    have hd' := htd.trans (mul_le_mul_of_nonneg_left hd T.coe_nonneg)
    have hcoeff : 0 ≤ (3*M+(H:ℝ))*(t y/2)⁻¹^4 := by positivity
    apply hh'.trans
    calc
      _ ≤ ((3*M+(H:ℝ))*(t y/2)⁻¹^4)*((T:ℝ)*(2*t y)) := mul_le_mul_of_nonneg_left hd' hcoeff
      _ = _ := by field_simp [(hp y).ne']; ring
  · have hv : widthKernel t h x y = 0 := by
      by_contra hn
      exact hd (by simpa only [mem_closedBall,dist_eq_norm] using widthKernel_support_local ht hp hT hs y hn)
    have hf : widthKernel (fun _ => t y) h x y = 0 :=
      widthKernel_eq_zero_of_far (fun _ => hp y) hs (by linarith [lt_of_not_ge hd,hp y])
    rw [hv,hf,sub_self,norm_zero]
    positivity

end Work_WidthKernelAmplitude_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

open CoulombAnalysis

lemma widthKernel_frozen_mass {b : ℝ} (hb : 0 < b) (h : Space → ℝ) (y : Space) :
    (∫ x, widthKernel (fun _ => b) h x y) = ∫ x, h x := by
  unfold widthKernel
  rw [integral_sub_left_eq_self (fun z => b⁻¹^3*h (b⁻¹ • z)) volume y,
    integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume h hb.le,
    space_finrank,smul_eq_mul,←mul_assoc,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow,one_mul]

lemma widthKernel_integrable {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    Integrable (fun x => widthKernel t h x y) := by
  apply (widthKernel_local_lipschitz ht hp hT hh hM hbound hs y).continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y (2*t y))
    (widthKernel_support_local ht hp hT hs y)

theorem widthKernel_mass_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    ‖(∫ x, widthKernel t h x y)-(∫ x, h x)‖ ≤
      ((1024/3:ℝ)*Real.pi*(3*M+(H:ℝ)))*(T:ℝ) := by
  have hty := hp y
  have hk := widthKernel_integrable ht hp hT hh hM hbound hs y
  have hconst : LipschitzWith 0 (fun _ : Space => t y) := LipschitzWith.const _
  have hk0 := widthKernel_integrable hconst (fun _ => hp y) (by norm_num) hh hM hbound hs y
  rw [←widthKernel_frozen_mass hty h y,←integral_sub hk hk0]
  have hs0 := widthKernel_support_local hconst (fun _ => hp y) (by norm_num) hs y
  have hs1 := widthKernel_support_local ht hp hT hs y
  have he : (∫ x in closedBall y (2*t y), widthKernel t h x y-widthKernel (fun _ => t y) h x y) =
      ∫ x, widthKernel t h x y-widthKernel (fun _ => t y) h x y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h1 : widthKernel t h x y = 0 := by
      by_contra hn; exact hx (hs1 hn)
    have h0 : widthKernel (fun _ => t y) h x y = 0 := by
      by_contra hn; exact hx (hs0 hn)
    rw [h1,h0,sub_self]
  rw [←he]
  have hh' := norm_setIntegral_le_of_norm_le_const
    ((isCompact_closedBall y (2*t y)).measure_lt_top (μ := volume))
    (fun x (_ : x ∈ closedBall y (2*t y)) => widthKernel_freeze_error ht hp hT hh hM hbound hs y x)
  apply hh'.trans_eq
  rw [Measure.addHaar_real_closedBall_center volume,tfSpace_closedBall_real (2*t y) (by positivity)]
  field_simp [hty.ne']
  ring

theorem masterKernel_approximate_mass {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c₁ r₀ s : ℝ),
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ y : Space, ‖(∫ x, masterKernel c₁ r₀ s g x y)-1‖ ≤ C*c₁*s^masterExponent := by
  have hp := masterProfile_support hgs
  have hcomp : HasCompactSupport (fun z => (g z)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1) hp
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  obtain ⟨z₀,hz₀⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
  let M := ‖(g z₀)^2‖
  have hM : 0 ≤ M := norm_nonneg _
  let A := (1024/3:ℝ)*Real.pi*(3*M+(H:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw := masterExponent_pos
  refine ⟨A*(1+masterExponent)+1,by positivity,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have hT : c₁*(1+masterExponent)*s^masterExponent ≤ (1/2:ℝ) := by
    have hsp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
    have hcp : 0 ≤ c₁*(1+masterExponent) := by positivity
    calc
      _ ≤ c₁*(1+masterExponent)*1 := mul_le_mul_of_nonneg_left hsp hcp
      _ ≤ _ := by norm_num [masterExponent] at *; nlinarith
  have hh := widthKernel_mass_error (masterWidth_lipschitz hc.le hr hs)
    (masterWidth_pos hc hr hs) hT hH hM hz₀ hp y
  change _ ≤ A*(c₁*(1+masterExponent)*s^masterExponent) at hh
  rw [hgn] at hh
  apply hh.trans
  have hn : 0 ≤ c₁*s^masterExponent := by positivity
  nlinarith only [hn]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseKernelMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseKernelMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma masterCenteredKernel_ball_mass {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s R : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space)
    (hR : 2*masterWidth c₁ r₀ s y < R) :
    (∫ x, masterCenteredKernel c₁ r₀ s g y x ∂ballMeasure R) =
      ∫ x, masterKernel c₁ r₀ s g x y := by
  have hsup := masterCenteredKernel_support hg hgs hc hcL hr hs hs1 y
  change (∫ x in ball 0 R, masterCenteredKernel c₁ r₀ s g y x) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact integral_add_left_eq_self (fun x => masterKernel c₁ r₀ s g x y) y
  · by_contra hne
    have hh := hsup hne
    exact hx (mem_ball.mpr ((mem_closedBall.mp hh).trans_lt hR))

theorem masterCenteredKernel_mass_tendsto {ι : Type*} {l : Filter ι}
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    {r₀ s R : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, 2*masterWidth c₁ (r₀ i) (s i) (y i) < R i) :
    Tendsto (fun i => ∫ x, masterCenteredKernel c₁ (r₀ i) (s i) g (y i) x
      ∂ballMeasure (R i)) l (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := masterKernel_approximate_mass hg hgs hgn
  have hzero : Tendsto (fun i => C*c₁*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (C*c₁)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hzero
  filter_upwards [hr,hs,hR,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hri hsi hRi hs1
  rw [masterCenteredKernel_ball_mass hg hgs hc hcL hri hsi hs1.le _ hRi]
  exact hbound c₁ (r₀ i) (s i) hc hcL hri hsi hs1.le (y i)

end Work_InverseKernelMass_barrier_scope

open Filter
open scoped Topology

open CoulombAnalysis

lemma rpow_inv_pow_bound {a t c e w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (ht : c*a^w ≤ t) (n : ℕ) :
    a^e*t⁻¹^n ≤ c⁻¹^n*a^(e-w*n) := by
  have hct : 0 < c*a^w := mul_pos hc (Real.rpow_pos_of_pos ha _)
  have hi := pow_le_pow_left₀ (inv_nonneg.mpr ((hct.trans_le ht).le))
    (inv_anti₀ hct ht) n
  have he : (c*a^w)⁻¹^n = c⁻¹^n*a^(-w*n) := by
    rw [mul_inv,mul_pow,←Real.rpow_neg ha.le,←Real.rpow_natCast (a^(-w)),←Real.rpow_mul ha.le]
  calc
    _ ≤ a^e*(c*a^w)⁻¹^n := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg ha.le _)
    _ = c⁻¹^n*(a^e*a^(-w*n)) := by rw [he]; ring
    _ = _ := by rw [←Real.rpow_add ha]; congr 2; ring

lemma inverse_duality_rescale {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (n L : ℝ) :
    (a^6)^2*((16*(n*t)^3*(L*t⁻¹^4)^2)*a^(-7+(1/100:ℝ))) =
      (16*n^3*L^2)*(a^(5+(1/100:ℝ))*t⁻¹^5) := by
  have he : a^12*a^(-7+(1/100:ℝ)) = a^(5+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  have he' : t^3*(t⁻¹^4)^2 = t⁻¹^5 := by
    field_simp
  calc
    _ = (16*n^3*L^2)*((a^12*a^(-7+(1/100:ℝ)))*(t^3*(t⁻¹^4)^2)) := by ring
    _ = _ := by rw [he,he']

lemma inverse_retained_rescale {a t A : ℝ} (ha : 0 < a) :
    a^6*(A*t⁻¹^3*a^(-3+(1/100:ℝ))) =
      A*(a^(3+(1/100:ℝ))*t⁻¹^3) := by
  have he : a^6*a^(-3+(1/100:ℝ)) = a^(3+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  calc
    _ = A*((a^6*a^(-3+(1/100:ℝ)))*t⁻¹^3) := by ring
    _ = _ := by rw [he]

theorem inverse_duality_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c n L : ℝ} (hc : 0 < c) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*Real.sqrt ((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (5+(1/100:ℝ))-(1+masterExponent)*5 := by norm_num [masterExponent]
  have hpow := ha0.rpow_const_nhds_zero he
  have hbound : Tendsto (fun i => (16*n^3*L^2*c⁻¹^5)*
      (a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) l (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (16*n^3*L^2*c⁻¹^5)
  have hscaled : Tendsto (fun i => ((a i)^6)^2*((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      positivity
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      rw [inverse_duality_rescale hai hti']
      calc
        _ ≤ (16*n^3*L^2)*(c⁻¹^5*(a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) :=
          mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 5) (by positivity)
        _ = _ := by ring
  have hh := hscaled.sqrt
  rw [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [ha,ht] with i hai hti
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_nonneg hai.le _)]

theorem inverse_retained_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*(A*(t i)⁻¹^3*(a i)^(-3+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (3+(1/100:ℝ))-(1+masterExponent)*3 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => (A*c⁻¹^3)*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3))
      l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero he).const_mul (A*c⁻¹^3)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht] with i hai hti
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    positivity
  · filter_upwards [ha,ht] with i hai hti
    rw [inverse_retained_rescale hai]
    calc
      _ ≤ A*(c⁻¹^3*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3)) :=
        mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 3) hA
      _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_InverseObservationScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis

lemma inverse_observation_geometry_tendsto {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*ell i)) l (𝓝 0) := by
  have he1 : 0 < (21/5:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have he2 : 0 < (401/100:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
      (2*E*c⁻¹^4)*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) l (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((ha0.rpow_const_nhds_zero he1).const_mul (c⁻¹^4)).add
        ((ha0.rpow_const_nhds_zero he2).const_mul (2*E*c⁻¹^4))
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have hli := helli.1
    positivity
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have he1' : (a i)^3*(a i)^(6/5:ℝ) = (a i)^(21/5:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    have he2' : (a i)^3*(a i)^(101/100:ℝ) = (a i)^(401/100:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    calc
      _ ≤ (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*(E*(a i)^(101/100:ℝ))) := by
        gcongr
        exact helli.2
      _ = ((a i)^3*(a i)^(6/5:ℝ))*(t i)⁻¹^4+
          (2*E)*((a i)^3*(a i)^(101/100:ℝ))*(t i)⁻¹^4 := by ring
      _ = (a i)^(21/5:ℝ)*(t i)⁻¹^4+(2*E)*((a i)^(401/100:ℝ)*(t i)⁻¹^4) := by
        rw [he1',he2']; ring
      _ ≤ c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
          (2*E)*(c⁻¹^4*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) :=
        add_le_add (rpow_inv_pow_bound hai hc hti 4)
          (mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 4) (by positivity))
      _ = _ := by ring

theorem inverse_observation_error_tendsto {ι : Type*} {l : Filter ι}
    {a t ell Q : ι → ℝ} {c E L q : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ))
    (hQ : Tendsto (fun i => (a i)^3*Q i) l (𝓝 q)) :
    Tendsto (fun i => (a i)^6*(Q i*(L*(t i)⁻¹^4*Real.sqrt 3*
      ((a i)^(6/5:ℝ)+2*ell i)))) l (𝓝 0) := by
  have hh := (hQ.mul (inverse_observation_geometry_tendsto hc hE ha ha0 ht hell)).const_mul (L*Real.sqrt 3)
  simp only [mul_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun i => by ring)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpectedRadialCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma scaled_mass_four_thirds {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    (M/a^3)^(4/3:ℝ) = M^(4/3:ℝ)/a^4 := by
  rw [Real.div_rpow hM (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

lemma sharpPatchRemainder_rescale {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) :
    a^7*sharpPatchRemainder a (a*β) (M/a^3) = dimensionlessPatchRemainder a β M := by
  have hs : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPatchRemainder dimensionlessPatchRemainder
  rw [hs,scaled_mass_four_thirds ha hM]
  field_simp
  ring

lemma sharpLocalPotentialBudget_rescale {a M u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    a^4*sharpLocalPotentialBudget a (M/a^3) (a*u) = dimensionlessLocalPotential M u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpOrdinaryDensityConstant*(M/a^3)^2/a =
      sharpOrdinaryDensityConstant*M^2/a^7 := by field_simp
  have hp : (a^7)^(3/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le]; norm_num
  have hprod : a^4*a^(1/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  unfold sharpLocalPotentialBudget dimensionlessLocalPotential
  rw [he,Real.div_rpow (mul_nonneg hC (sq_nonneg M)) (by positivity),hp,
    Real.mul_rpow ha.le hu]
  have hne : a^(21/5:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  calc _ = (a^4*a^(1/5:ℝ)/a^(21/5:ℝ))*
        ((sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)) := by ring
       _ = _ := by rw [hprod,div_self hne,one_mul]

lemma sharpPotentialRemainder_rescale {a β M E τ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) (hτ : 0 < τ) :
    a^4*sharpPotentialRemainder a (a*β) (M/a^3) (E/a^7) (a*τ) =
      dimensionlessPotentialRemainder a β M E τ := by
  have hR := sharpPatchRemainder_rescale ha hβ hM
  have hroot : a^4*Real.sqrt ((2/(a*τ))*(E/a^7+sharpPatchRemainder a (a*β) (M/a^3))) =
      Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M)) := by
    rw [←Real.sqrt_sq (by positivity : 0 ≤ a^4),←Real.sqrt_mul (sq_nonneg (a^4))]
    congr 1
    rw [←hR]
    field_simp
  have hpot1 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ τ+Real.sqrt 3*β)
  have hpot2 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ Real.sqrt 3*β)
  have he1 : a*τ+Real.sqrt 3*(a*β) = a*(τ+Real.sqrt 3*β) := by ring
  have he2 : Real.sqrt 3*(a*β) = a*(Real.sqrt 3*β) := by ring
  have he3 : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPotentialRemainder dimensionlessPotentialRemainder
  rw [mul_add,mul_add,mul_add,mul_add]
  rw [hroot,he1,he2,hpot1,hpot2,he3]
  field_simp

lemma localOffsetMass_rescale {D : ℝ} {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) :
    (localCellRadius y)^3*localOffsetMass D y = 1+Real.sqrt (D*(localCellRadius y)^7) := by
  have ha := localCellRadius_pos hy
  have hh : (localCellRadius y)^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hmax : max (1/(localCellRadius y)^3) 1 = 1/(localCellRadius y)^3 :=
    max_eq_left ((le_div_iff₀ (by positivity : 0 < (localCellRadius y)^3)).mpr (by simpa using hh))
  unfold localOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ ha.ne'),←Real.sqrt_sq (by positivity : 0 ≤ (localCellRadius y)^3),
    ←Real.sqrt_mul (sq_nonneg ((localCellRadius y)^3))]
  congr 2
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma dyadicUniformEventBudget_nonneg {r p₀ δ : ℝ}
    (hr : 0 < r) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hδ : 0 ≤ δ) :
    0 ≤ dyadicUniformEventBudget r p₀ δ := by
  have hlog : 0 ≤ Real.log (Real.exp 1/p₀) := by
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  unfold dyadicUniformEventBudget
  exact add_nonneg (mul_nonneg (mul_nonneg observationFisherConstant_pos.le
    (Real.rpow_nonneg hr.le _)) (pow_nonneg hlog _)) hδ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpErrorLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma patch_power_ratio {a : ℝ} (ha : 0 < a) (p w : ℝ) :
    (a^p/(a^(1/5:ℝ))^2)/a^w = a^(p-2/5-w) := by
  rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_sub ha,←Real.rpow_sub ha]
  norm_num

lemma patch_sqrt_ratio {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Real.sqrt (8*a^(1/5:ℝ))/a^w = Real.sqrt 8*a^(1/10-w) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8),Real.sqrt_eq_rpow (a^(1/5:ℝ)),
    ←Real.rpow_mul ha.le]
  norm_num
  rw [mul_div_assoc,←Real.rpow_sub ha]

lemma dimensionlessPatchRemainder_weight {a : ℝ} (ha : 0 < a) (M w : ℝ) :
    dimensionlessPatchRemainder a (a^(1/5:ℝ)) M/a^w = weightedDimensionlessPatch a M w := by
  have h2 : (a^2/(a^(1/5:ℝ))^2)/a^w = a^(8/5-w) := by
    convert patch_power_ratio ha 2 w using 1 <;> norm_num
  have h1 : (a/(a^(1/5:ℝ))^2)/a^w = a^(3/5-w) := by
    convert patch_power_ratio ha 1 w using 1 <;> norm_num
  have h3 : (a^3/a^(1/5:ℝ))/a^w = a^(14/5-w) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub ha,←Real.rpow_sub ha]
    norm_num
  have hr := patch_sqrt_ratio ha w
  unfold dimensionlessPatchRemainder weightedDimensionlessPatch
  rw [←h2,←h1,←h3,←hr]
  ring

theorem dimensionlessPatchRemainder_div_tendsto {ι : Type*} {l : Filter ι}
    {a M : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : w < 1/10) :
    Tendsto (fun i => dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)/(a i)^w)
      l (𝓝 0) := by
  have hpow (p : ℝ) (hp : 0 < p) := ha0.rpow_const_nhds_zero hp
  have hs : Tendsto (fun i => Real.sqrt (8*(a i)^(1/5:ℝ))) l (𝓝 0) := by
    simpa using ((hpow (1/5) (by norm_num)).const_mul 8).sqrt
  have h1 := ((hpow (8/5-w) (by linarith)).mul_const localizationIMSConstant).mul
    ((hs.mul_const actualCellMomentConstant).mul hM)
  have h2 := (((hpow (3/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    ((actualCellMomentConstant)^(2/3:ℝ))).mul (hM.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 4/3)))
  have h3 := (((hpow (8/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    actualCellMomentConstant).mul hM
  have h4 := (((hpow (14/5-w) (by linarith)).mul_const ((2*Real.pi+1)/2)).mul_const
    actualCellMomentConstant).mul hM
  have h5 := ((((hpow (1/10-w) (by linarith)).const_mul (Real.sqrt 8)).const_mul
    sharpFreshFieldConstant).mul_const actualCellMomentConstant).mul (hM.pow 2)
  have h6 := ((((hpow (8/5-w) (by linarith)).mul_const (packetDirichlet canonicalRealPacket/2)).mul_const
    768).mul_const sharpFreshFieldConstant).mul hM
  have hh : Tendsto (fun i => weightedDimensionlessPatch (a i) (M i) w) l (𝓝 0) := by
    simpa only [weightedDimensionlessPatch,zero_mul,mul_zero,add_zero] using
      ((((h1.add h2).add h3).add h4).add h5).add h6
  apply hh.congr'
  filter_upwards [ha] with i hi
  exact (dimensionlessPatchRemainder_weight hi (M i) w).symm

lemma dimensionlessLocalPotential_tendsto {ι : Type*} {l : Filter ι}
    {M u : ι → ℝ} {M₀ : ℝ} (hM : Tendsto M l (𝓝 M₀)) (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => dimensionlessLocalPotential (M i) (u i)) l (𝓝 0) := by
  have h1 := ((hM.pow 2).const_mul sharpOrdinaryDensityConstant).rpow_const
    (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  have h2 := hu.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  simpa only [dimensionlessLocalPotential,mul_zero] using
    (h1.mul_const ((8*Real.pi)^(2/5:ℝ))).mul h2

theorem dimensionlessPotentialRemainder_tendsto {ι : Type*} {l : Filter ι}
    {a M E : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : 0 < w) (hw' : w < 1/10)
    (hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0)) :
    Tendsto (fun i => dimensionlessPotentialRemainder (a i) ((a i)^(1/5:ℝ)) (M i) (E i) ((a i)^w))
      l (𝓝 0) := by
  have hR := dimensionlessPatchRemainder_div_tendsto ha ha0 hM hw'
  have hτ := ha0.rpow_const_nhds_zero hw
  have hβ := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have hroot : Tendsto (fun i => Real.sqrt ((2/(a i)^w)*
      (E i+dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)))) l (𝓝 0) := by
    have ht := ((hE.add hR).const_mul 2).sqrt
    convert ht using 1
    · funext i
      congr 1
      ring
    · simp
  have hu1 : Tendsto (fun i => (a i)^w+Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hτ.add (hβ.const_mul (Real.sqrt 3))
  have hu2 : Tendsto (fun i => Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hβ.const_mul (Real.sqrt 3)
  have hcap := (hτ.pow 2).const_mul (2*Real.pi*tfPatchDensityCapConstant)
  have hdel := (((hβ.const_mul 8).sqrt).mul_const actualCellMomentConstant).mul hM
  simpa only [dimensionlessPotentialRemainder,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),
    Real.sqrt_zero,add_zero] using
    (((hroot.add (dimensionlessLocalPotential_tendsto hM hu1)).add hcap).add
      (dimensionlessLocalPotential_tendsto hM hu2)).add hdel

end Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma microscopicWidth_eq {a : ℝ} (ha : 0 < a) :
    a*a^(1/5:ℝ) = a^(6/5:ℝ) := by
  calc _ = a^(1:ℝ)*a^(1/5:ℝ) := by rw [Real.rpow_one]
       _ = _ := by rw [←Real.rpow_add ha]; norm_num

lemma microscopic_collar {a m : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hm : 1/a^3 ≤ m) : a ≤ (a*a^(1/5:ℝ))^2*m := by
  have hβ : a ≤ a^(1/5:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1/5:ℝ) ≤ 1)
  have hb : a^2 ≤ a*a^(1/5:ℝ) := by nlinarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hsq : a^4 ≤ (a*a^(1/5:ℝ))^2 := by nlinarith [sq_nonneg (a*a^(1/5:ℝ)-a^2)]
  calc a = a^4*(1/a^3) := by field_simp
       _ ≤ a^4*m := mul_le_mul_of_nonneg_left hm (by positivity)
       _ ≤ (a*a^(1/5:ℝ))^2*m := mul_le_mul_of_nonneg_right hsq hm0

lemma normalized_excess_ratio {a D w : ℝ} (ha : 0 < a) :
    (D*a^7)/a^w = D*a^(7-w) := by
  rw [mul_div_assoc,←Real.rpow_natCast,←Real.rpow_sub ha]
  norm_num

theorem physical_local_mass_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)) l (𝓝 1) := by
  let a := fun i => localCellRadius (y i)
  have hp : Tendsto (fun i => (a i)^w) l (𝓝 0) := hy0.rpow_const_nhds_zero hw
  have hE : Tendsto (fun i => D i*(a i)^7) l (𝓝 0) := by
    have ht := hD.mul hp
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hy] with i hi
    have ha := localCellRadius_pos hi
    change D i*(a i)^(7-w)*(a i)^w = D i*(a i)^7
    rw [mul_assoc,←Real.rpow_add ha]
    norm_num [a]
  have ht : Tendsto (fun i => 1+Real.sqrt (D i*(a i)^7)) l (𝓝 1) := by
    simpa using hE.sqrt.const_add 1
  apply ht.congr'
  filter_upwards [hy,hy0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi ha1
  exact (localOffsetMass_rescale hi ha1.le).symm

theorem physical_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      sharpPotentialRemainder (localCellRadius (y i))
        ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  let E := fun i => D i*(a i)^7
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0) := by
    apply hD.congr'
    filter_upwards [ha] with i hi
    exact (normalized_excess_ratio hi).symm
  have ht := dimensionlessPotentialRemainder_tendsto ha hy0 hM hw hw' hE
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPotentialRemainder_rescale (E := E i) hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi (Real.rpow_pos_of_pos hi w)
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  have henergy : E i/(a i)^7 = D i := by dsimp [E]; field_simp
  rw [hmass,henergy,microscopicWidth_eq hi] at he
  exact he.symm

theorem physical_patch_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (D i+sharpPatchRemainder (localCellRadius (y i))
      ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)))*
        (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := hD.add (dimensionlessPatchRemainder_div_tendsto ha hy0 hM hw')
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPatchRemainder_rescale hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hmass,microscopicWidth_eq hi] at he
  rw [←he,add_mul]
  congr 1
  rw [mul_comm ((a i)^7),normalized_excess_ratio hi]

theorem physical_master_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D u : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0))
    (hu : ∀ᶠ i in l, 0 ≤ u i) (hu0 : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*sharpLocalPotentialBudget
      (localCellRadius (y i)) (localOffsetMass (D i) (y i))
      ((localCellRadius (y i))*u i)) l (𝓝 0) := by
  let M := fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := dimensionlessLocalPotential_tendsto hM hu0
  apply ht.congr'
  filter_upwards [hy,hu] with i hi hui
  have ha := localCellRadius_pos hi
  have he := sharpLocalPotentialBudget_rescale (M := M i) ha hui
  have hm : M i/(localCellRadius (y i))^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hm] at he
  exact he.symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseBudgetScaleBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_gap_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (C G : ℝ) :
    a^4*((C/R^4)/a^(-7+(1/100:ℝ)))*G =
      (C*(a/R)^4)*(G*a^(7-(1/100:ℝ))) := by
  have he : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]
    congr 1
    ring
  rw [he,div_inv_eq_mul]
  field_simp

lemma inverse_high_gap_rescale {a : ℝ} (ha : 0 < a) (H G : ℝ) :
    a^4*(H/a^(-7+(1/100:ℝ))+2/a^(-3+(1/100:ℝ)))*G =
      (a^4*H+2)*(G*a^(7-(1/100:ℝ))) := by
  have he1 : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he2 : a^(-3+(1/100:ℝ)) = (a^(3-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he3 : a^4*a^(3-(1/100:ℝ)) = a^(7-(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  rw [he1,he2,div_inv_eq_mul,div_inv_eq_mul]
  calc _ = (a^4*H)*(G*a^(7-(1/100:ℝ)))+2*G*(a^4*a^(3-(1/100:ℝ))) := by ring
       _ = _ := by rw [he3]; ring

lemma inverse_low_gap_tendsto {ι : Type*} {l : Filter ι}
    {a R G : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*((C/(R i)^4)/(a i)^(-7+(1/100:ℝ)))*G i)
      l (𝓝 0) := by
  have hh := bdd_le_mul_tendsto_zero (f := fun i => C*(a i/R i)^4)
    (b := 0) (B := C) (by
      filter_upwards [ha,hR] with i hai hRi
      positivity) (by
      filter_upwards [ha,hR] with i hai hRi
      have hRi' := hai.trans_le hRi
      have hb := pow_le_one₀ (div_nonneg hai.le hRi'.le) ((div_le_one hRi').mpr hRi) (n := 4)
      exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_one C)) hG
  apply hh.congr'
  filter_upwards [ha,hR] with i hai hRi
  exact (inverse_gap_rescale hai (hai.trans_le hRi) C (G i)).symm

lemma inverse_high_gap_tendsto {ι : Type*} {l : Filter ι}
    {a H G : ι → ℝ} {h : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h))
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(H i/(a i)^(-7+(1/100:ℝ))+
      2/(a i)^(-3+(1/100:ℝ)))*G i) l (𝓝 0) := by
  have hh := (hH.add_const 2).mul hG
  simp only [mul_zero] at hh
  apply hh.congr'
  exact ha.mono fun i hi => (inverse_high_gap_rescale hi (H i) (G i)).symm

theorem inverse_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D t : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (ht : ∀ᶠ i in l, 0 ≤ t i)
    (ht0 : Tendsto (fun i => t i/localCellRadius (y i)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*(
      sharpPotentialRemainder (localCellRadius (y i)) ((localCellRadius (y i))^(6/5:ℝ))
        (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^masterExponent)+
      sharpLocalPotentialBudget (localCellRadius (y i)) (localOffsetMass (D i) (y i))
        (2*t i))) l (𝓝 0) := by
  have hpot := physical_potential_error_tendsto hy ha0 masterExponent_pos
    (by norm_num [masterExponent] : masterExponent < 1/10) hD
  have hu : ∀ᶠ i in l, 0 ≤ 2*(t i/localCellRadius (y i)) := by
    filter_upwards [hy,ht] with i hyi hti
    have hai := localCellRadius_pos hyi
    positivity
  have hu0 : Tendsto (fun i => 2*(t i/localCellRadius (y i))) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul 2
  have hmaster := physical_master_error_tendsto hy ha0 masterExponent_pos hD hu hu0
  have hh := hpot.add hmaster
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hy] with i hyi
  have hai := localCellRadius_pos hyi
  rw [show localCellRadius (y i)*(2*(t i/localCellRadius (y i))) = 2*t i by field_simp]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshRetainedMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshRetainedMass_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators NNReal ENNReal

open CoulombAnalysis CoulombNeumann

lemma canonicalMasterAmplitude_pos : 0 < canonicalMasterAmplitude :=
  (Classical.choose_spec masterCenteredKernel_amplitude).1

end Work_FreshRetainedMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_continuous : Continuous localTFResponse := by
  unfold localTFResponse
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma localTFResponse_rescale {a : ℝ} (ha : 0 < a) (h : ℝ) :
    a^6*localTFResponse h = localTFResponse (a^4*h) := by
  have he : max (a^4*h) 0 = a^4*max h 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _),mul_zero]
  have hT := tfKinetic_pos
  unfold localTFResponse
  rw [he,mul_div_assoc,Real.mul_rpow (pow_nonneg ha.le _) (by positivity),
    ←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
  norm_num

lemma inverse_oscillation_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (C n t : ℝ) :
    a^4*(C/R*(n*t))*R⁻¹^4 = C*n*(t/a)*(a/R)^5 := by
  field_simp

lemma inverse_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} {C n : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht : ∀ᶠ i in l, 0 ≤ t i) (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(C/R i*(n*t i))*(R i)⁻¹^4) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    positivity
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    rw [inverse_oscillation_rescale hai hRi']
    have hh : (a i/R i)^5 ≤ 1 := pow_le_one₀ (div_nonneg hai.le hRi'.le)
      ((div_le_one hRi').mpr hRi)
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (mul_one _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseThresholdMarginsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseThresholdMargins_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis

lemma eventually_forall_mem_of_selections {ι α : Type*} {l : Filter ι}
    {S : ι → Set α} {P : ι → α → Prop} (d : ι → α)
    (hd : ∀ᶠ i in l, d i ∈ S i)
    (h : ∀ f : ι → α, (∀ᶠ i in l, f i ∈ S i) → ∀ᶠ i in l, P i (f i)) :
    ∀ᶠ i in l, ∀ x ∈ S i, P i x := by
  classical
  let f : ι → α := fun i => if hi : ∃ x ∈ S i, ¬P i x then Classical.choose hi else d i
  have hf : ∀ᶠ i in l, f i ∈ S i := by
    filter_upwards [hd] with i hi
    dsimp only [f]
    split_ifs with hn
    · exact (Classical.choose_spec hn).1
    · exact hi
  filter_upwards [h f hf] with i hi
  intro x hx
  by_contra hn
  have hex : ∃ x ∈ S i, ¬P i x := ⟨x,hx,hn⟩
  exact (Classical.choose_spec hex).2 (by simpa only [f,dite_eq_left hex] using hi)

lemma localTFResponse_nonneg (h : ℝ) : 0 ≤ localTFResponse h := by
  have hT := tfKinetic_pos
  unfold localTFResponse
  exact Real.rpow_nonneg (div_nonneg (le_max_right _ _) (by positivity)) _

lemma localTFResponse_strict_mono {h H : ℝ} (hh : 0 ≤ h) (hH : h < H) :
    localTFResponse h < localTFResponse H := by
  have hT : 0 < (5/3:ℝ)*tfKinetic := mul_pos (by norm_num) tfKinetic_pos
  unfold localTFResponse
  rw [max_eq_left hh,max_eq_left (hh.trans hH.le)]
  exact Real.rpow_lt_rpow (div_nonneg hh hT.le) ((div_lt_div_iff_of_pos_right hT).mpr hH) (by norm_num)

lemma inverse_low_density_margin {ι : Type*} {l : Filter ι}
    {a T E F : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f)) (htf : t < f) :
    ∀ᶠ i in l, T i+E i < F i := by
  have hh := (hT.add hE).eventually_lt hF (by simpa using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  linarith

lemma inverse_high_density_margin {ι : Type*} {l : Filter ι}
    {a T E F M : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f))
    (hM : Tendsto (fun i => (a i)^6*M i) l (𝓝 0)) (hf : 0 ≤ f) (htf : f < t) :
    ∀ᶠ i in l, max (F i) (M i)+E i < T i := by
  have hh := ((hF.max hM).add hE).eventually_lt hT (by simpa [max_eq_left hf] using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  rw [mul_add,mul_max_of_nonneg _ _ (pow_nonneg hai.le _)]
  exact hi

end Work_InverseThresholdMargins_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma observation_relative_tendsto {ι : Type*} {l : Filter ι} {a ell : ι → ℝ}
    {E : ℝ} (_hE : 0 ≤ E) (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => ell i/a i) l (𝓝 0) := by
  have hh : Tendsto (fun i => E*(a i)^(1/100:ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/100)).const_mul E
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hell] with i hai hei
    exact div_nonneg hei.1 hai.le
  · filter_upwards [ha,hell] with i hai hei
    calc _ ≤ E*(a i)^(101/100:ℝ)/a i := div_le_div_of_nonneg_right hei.2 hai.le
         _ = _ := by
           have heq : (a i)^(101/100:ℝ)/a i = (a i)^(1/100:ℝ) := by
             calc _ = (a i)^((101/100:ℝ)-1) := by rw [Real.rpow_sub hai,Real.rpow_one]
                  _ = _ := by norm_num
           rw [mul_div_assoc,heq]

lemma microscopic_relative_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => (a i)^(6/5:ℝ)/a i) l (𝓝 0) := by
  have hh := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  apply hh.congr'
  filter_upwards [ha] with i hai
  calc _ = (a i)^((6/5:ℝ)-1) := by norm_num
       _ = _ := by rw [Real.rpow_sub hai,Real.rpow_one]

theorem inverse_geometry_eventually {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0))
    (hell0 : Tendsto (fun i => ell i/a i) l (𝓝 0)) :
    ∀ᶠ i in l,
      a i ≤ 1 ∧
      0 < (a i)^(6/5:ℝ) ∧ 2*(a i)^(6/5:ℝ) ≤ a i ∧
      0 < a i*(a i)^masterExponent ∧
      a i*(a i)^masterExponent+Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 4*a i ∧
      a i*(a i)^masterExponent ≤ 3*(5*a i-4*(a i)^(6/5:ℝ))/4 ∧
      a i ≤ ((a i)^(6/5:ℝ))^2*(1/(a i)^3) ∧
      3*t i ≤ (5*a i-4*(a i)^(6/5:ℝ))/12 ∧
      2*t i+Real.sqrt 3*((a i)^(6/5:ℝ)+2*ell i) < a i := by
  have hb0 := microscopic_relative_tendsto ha ha0
  have hq0 := ha0.rpow_const_nhds_zero masterExponent_pos
  filter_upwards [ha,
    ha0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hb0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hq0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    ht0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hell0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100))]
    with i hai ha1 hbi hqi hti heli
  have hb : (a i)^(6/5:ℝ) < a i/100 := by linarith [(div_lt_iff₀ hai).mp hbi]
  have ht : t i < a i/100 := by linarith [(div_lt_iff₀ hai).mp hti]
  have he : ell i < a i/100 := by linarith [(div_lt_iff₀ hai).mp heli]
  have hq : a i*(a i)^masterExponent < a i/100 := by nlinarith
  have hbpos : 0 < (a i)^(6/5:ℝ) := Real.rpow_pos_of_pos hai _
  have hqpos : 0 < a i*(a i)^masterExponent := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hroot : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
  have hprod : Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 2*(a i)^(6/5:ℝ) :=
    mul_le_mul_of_nonneg_right hroot hbpos.le
  have hcol := microscopic_collar hai ha1.le (m := 1/(a i)^3) le_rfl
  rw [microscopicWidth_eq hai] at hcol
  refine ⟨ha1.le,hbpos,by linarith,hqpos,by linarith,by linarith,hcol,by linarith,?_⟩
  have he' : Real.sqrt 3*ell i < 2*a i/100 := by
    calc _ < Real.sqrt 3*(a i/100) := mul_lt_mul_of_pos_left he (Real.sqrt_pos.mpr (by norm_num))
         _ ≤ _ := by nlinarith
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseNumericalStatementsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseNumericalStatements_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis

lemma scaled_div_pow_constant {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (n : ℕ) (c : ℝ) :
    Tendsto (fun i => (a i)^n*(c/(a i)^n)) l (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [ha] with i hai
  field_simp

end Work_InverseNumericalStatements_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_unscaled_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) (C n : ℝ) :
    Tendsto (fun i => C/R i*(n*t i)) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  have hm := bdd_le_mul_tendsto_zero (f := fun i => a i/R i) (b := 0) (B := 1)
    (by filter_upwards [ha,hR] with i hai hRi; exact div_nonneg hai.le (hai.le.trans hRi))
    (by filter_upwards [ha,hR] with i hai hRi; exact (div_le_one (hai.trans_le hRi)).mpr hRi) hh
  apply hm.congr'
  filter_upwards [ha,hR] with i hai hRi
  have hRi' := hai.trans_le hRi
  field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BandInverseNumericsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BandInverseNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma quantumInverseCountConstant_square : universalCellCountConstant < quantumInverseCountConstant^2 := by
  have := universalCellCountConstant_one_le
  unfold quantumInverseCountConstant
  nlinarith [sq_nonneg universalCellCountConstant]

lemma inverse_count_margin_eventually {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0)) :
    ∀ᶠ i in l, universalCellCountConstant*(localOffsetMass (D i) (y i))^2 <
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hm := physical_local_mass_tendsto hy ha0 masterExponent_pos hD
  have hh := ((hm.pow 2).const_mul universalCellCountConstant).eventually_lt
    (tendsto_const_nhds (x := quantumInverseCountConstant^2))
    (by simpa using quantumInverseCountConstant_square)
  filter_upwards [hy,hh] with i hyi hi
  have ha := localCellRadius_pos hyi
  have hscale : (localCellRadius (y i))^6*
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 = quantumInverseCountConstant^2 := by
    field_simp
  apply (mul_lt_mul_iff_right₀ (pow_pos ha 6)).mp
  rw [hscale]
  nlinarith only [hi]

end Work_BandInverseNumerics_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OwnProbabilityFieldCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma originalQueryField_integrable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Space) :
    Integrable (fun z => originalQueryField F Z lam r j c₁ r₀ s z y)
      (physicalObservationLaw (graphRawLaw F) K) := by
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable
      (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  exact (integrable_const (Z/‖y‖-lam)).sub
    (jointMasterPosterior_potential_integrable (graphRawLaw F)
      (fun k : Fin K => dyadicObservationWidth r k) j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
      canonicalRealPacket_radial canonicalRealPacket_support)

lemma originalQueryField_le_nuclear {N K : ℕ} (F : fermionGraph N)
    (Z r : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) :
    originalQueryField F Z lam r j c₁ r₀ s z y ≤ Z/‖y‖ := by
  have he := tfPotential_nonneg (ae_of_all volume (fun x =>
    jointMasterPosterior_nonneg (graphRawLaw F)
      (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
      (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) x)) y
  change 0 ≤ tfPotential (originalQueryDensity F r j c₁ r₀ s z) y at he
  change Z/‖y‖-lam-_ ≤ _
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityBudgetScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma own_probability_log_cost_tendsto {v : ℝ} (hv : 0 < v) :
    Tendsto (fun p : ℝ => p^v*(Real.log (Real.exp 1/p))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := v/5
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun p : ℝ => p^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub hlog).pow 5
  simp only [sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  rw [Real.log_div (Real.exp_pos 1).ne' hp.ne',Real.log_exp]
  rw [show p^q-Real.log p*p^q = p^q*(1-Real.log p) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
  congr 2
  dsimp [q]
  ring

lemma own_probability_weighted_budget_tendsto {ι : Type*} {l : Filter ι}
    {r p : ι → ℝ} {v δ : ℝ} (hr : ∀ᶠ i in l, 0 < r i)
    (hr0 : Tendsto r l (𝓝 0)) (hp : ∀ᶠ i in l, 0 < p i)
    (hp0 : Tendsto p l (𝓝 0)) (hv : 2.02 < v) :
    Tendsto (fun i => (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(r i)^v)
      l (𝓝 0) := by
  have hlog := (own_probability_log_cost_tendsto (by norm_num : (0:ℝ) < 1/4)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hp0,hp⟩)
  have hrp := hr0.rpow_const_nhds_zero (by linarith : 0 < v-2.02)
  have hrp' := hr0.rpow_const_nhds_zero (by linarith : 0 < v)
  have hpp := hp0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/4)
  have hh := ((hlog.mul hrp).const_mul observationFisherConstant).add
    ((hpp.mul hrp').const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [hr] with i hi
  have he : (r i)^(-2.02:ℝ)*(r i)^v = (r i)^(v-2.02) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [show (p i)^(1/4:ℝ)*
    (observationFisherConstant*(r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/p i))^5+δ)*(r i)^v =
      observationFisherConstant*((p i)^(1/4:ℝ)*(Real.log (Real.exp 1/p i))^5)*
        ((r i)^(-2.02:ℝ)*(r i)^v)+δ*((p i)^(1/4:ℝ)*(r i)^v) by ring,he]
  dsimp only [Function.comp_apply]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeightedCapLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

lemma physical_field_cap_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D t : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (ht : ∀ᶠ i in l, 0 ≤ t i)
    (ht0 : Tendsto (fun i => t i/localCellRadius (y i)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      physicalFieldCapBudget (D i) (y i) ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent) (2*t i))
      l (𝓝 tfPatchCapConstant) := by
  have hh := (inverse_potential_error_tendsto hy ha0 hD ht ht0).const_add tfPatchCapConstant
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hy] with i hi
  have ha := localCellRadius_pos hi
  unfold physicalFieldCapBudget
  field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialDeterministicBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma potential_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) :
    Measurable (fun p : Ω × TFSpace => tfPotential (ρ p.1) p.2) := by
  have h : Measurable (fun p : (Ω × TFSpace) × TFSpace => ρ p.1.1 p.2/‖p.1.2-p.2‖) :=
    (hm.comp (measurable_fst.fst.prodMk measurable_snd)).div
      (measurable_fst.snd.sub measurable_snd).norm
  exact h.stronglyMeasurable.integral_prod_right.measurable

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_le {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    tfPotential ρ x ≤ 2*Real.pi*M+∫ z, ρ z := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  calc
    _ ≤ ∫ z, M*truncatedCoulomb 1 (x-z)+ρ z := integral_mono
      (bounded_L1_potential_integrable hm hi hM hn hb x) ((hk.const_mul M).add hi)
      (bounded_coulomb_majorant hM hn hb x)
    _ = _ := by
      rw [integral_add (hk.const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
        truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball (by norm_num : (0:ℝ) < 1)]
      ring

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma bounded_L1_pair_integrable {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) (hiη : Integrable η) :
    Integrable (fun p : Space × Space => η p.1*ρ p.2/‖p.1-p.2‖) := by
  rw [Measure.volume_eq_prod]
  have hj : Measurable (fun p : Space × Space => η p.1*ρ p.2/‖p.1-p.2‖) :=
    ((hmη.comp measurable_fst).mul (hm.comp measurable_snd)).div
      (measurable_fst.sub measurable_snd).norm
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x => by
      simpa only [mul_div_assoc] using
        (bounded_L1_potential_integrable hm hi hM hn hb x).const_mul (η x)
  · have hpot := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
    have hprod : Integrable (fun x => ‖η x‖*tfPotential ρ x) := by
      apply (hiη.norm.mul_const (2*Real.pi*M+∫ z, ρ z)).mono'
        (hmη.norm.mul hpot.measurable).aestronglyMeasurable
      exact ae_of_all _ fun x => by
        change ‖‖η x‖*tfPotential ρ x‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (tfPotential_nonneg (ae_of_all _ hn) x))]
        exact mul_le_mul_of_nonneg_left (bounded_L1_potential_le hm hi hM hn hb x) (norm_nonneg _)
    have he : (fun x => ∫ z, ‖η x*ρ z/‖x-z‖‖) =
        (fun x => ‖η x‖*tfPotential ρ x) := by
      funext x
      simp only [mul_div_assoc,norm_mul,
        Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _)),
        integral_const_mul,tfPotential]
    change Integrable (fun x => ∫ z, ‖η x*ρ z/‖x-z‖‖)
    rw [he]
    exact hprod

lemma bounded_L1_potential_radial_average_le {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) {R B : ℝ} (hR : 0 ≤ R)
    (hnη : ∀ z, 0 ≤ η z) (hsη : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbη : ∀ z, |η z| ≤ B) (hrη : IsRadial η) (h1η : ∫ z, η z = 1) (y : Space) :
    (∫ z, tfPotential ρ z*η (z-y)) ≤ tfPotential ρ y := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hsη x hx
  have hiη := bounded_compact_integrable hmη (isCompact_closedBall _ _) hsupport hbη
  have hpη := bounded_compact_memLp hmη (isCompact_closedBall _ _) hsupport hbη (5/3)
  have htη := bounded_compact_integrable (translatedDensity_measurable hmη y)
    (isCompact_closedBall y R) (translatedDensity_support hsη y) (fun _ => hbη _)
  have hpair := bounded_L1_pair_integrable hm hi hM hn hb
    (translatedDensity_measurable hmη y) htη
  calc
    _ = ∫ z, translatedDensity η y z*tfPotential ρ z := by
      apply integral_congr_ae; exact ae_of_all _ fun _ => mul_comm _ _
    _ = ∫ z, ρ z*tfPotential (translatedDensity η y) z := coulomb_potential_pair_comm hpair
    _ ≤ tfPotential ρ y := by
      have hswap : Integrable (fun p : Space × Space => ρ p.1*translatedDensity η y p.2/‖p.1-p.2‖) := by
        have hh := hpair
        rw [Measure.volume_eq_prod] at hh ⊢
        apply hh.swap.congr
        exact ae_of_all _ fun p => by dsimp; rw [norm_sub_rev]; ring
      apply integral_mono_ae (coulomb_potential_pair_integrable hswap)
        (bounded_L1_potential_integrable hm hi hM hn hb y)
      filter_upwards [volume.ae_ne y] with z hz
      rw [potential_translatedDensity]
      have hd := radial_potential_le_point hiη hpη hnη hrη hR hsη (sub_ne_zero.mpr hz)
      rw [h1η] at hd
      have hh := mul_le_mul_of_nonneg_left hd (hn z)
      simpa only [norm_sub_rev y z,div_eq_mul_inv,one_div,one_mul] using hh

theorem bounded_L1_field_radial_submean {ρ η : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hmη : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hnη : ∀ z, 0 ≤ η z) (hsη : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbη : ∀ z, |η z| ≤ B) (hrη : IsRadial η) (h1η : ∫ z, η z = 1)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    Z/‖y‖-lam-tfPotential ρ y ≤
      ∫ z, (Z/‖z‖-lam-tfPotential ρ z)*η (z-y) := by
  let k := translatedDensity η y
  have hkm : Measurable k := translatedDensity_measurable hmη y
  have hks := translatedDensity_support hsη y
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall y R) hks (fun _ => hbη _)
  have hkp : MemLp k (5/3) := bounded_compact_memLp hkm (isCompact_closedBall y R) hks (fun _ => hbη _) _
  have hk1 : (∫ z, k z) = 1 := by rw [translatedDensity_mass,h1η]
  have hknuc : Integrable (fun z => Z/‖z‖*k z) := by
    have hh := (tfPotential_integrable hki hkp (0:Space)).const_mul Z
    apply hh.congr
    exact ae_of_all _ fun z => by
      dsimp only
      rw [zero_sub,norm_neg]
      ring
  have hkpot : Integrable (fun z => tfPotential ρ z*k z) := by
    simpa only [mul_comm] using coulomb_potential_pair_integrable (bounded_L1_pair_integrable hm hi hM hn hb hkm hki)
  have hnucint : (∫ z, Z/‖z‖*k z) = Z/‖y‖ := by
    calc
      _ = Z*tfPotential k 0 := by
        rw [tfPotential,←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun z => by dsimp; rw [zero_sub,norm_neg]; ring
      _ = _ := by
        rw [radial_translatedDensity_potential hmη hR hsη hbη hrη h1η y 0
          (by simpa only [zero_sub,norm_neg] using hnuc),zero_sub,norm_neg]
        ring
  have hp := bounded_L1_potential_radial_average_le hm hi hM hn hb hmη hR.le hnη hsη hbη hrη h1η y
  change _ ≤ ∫ z, (Z/‖z‖-lam-tfPotential ρ z)*k z
  simp_rw [sub_mul]
  have hsub : Integrable (fun z => Z/‖z‖*k z-lam*k z) := hknuc.sub (hki.const_mul lam)
  rw [integral_sub hsub hkpot,
    integral_sub hknuc (hki.const_mul lam),integral_const_mul,hk1,mul_one,hnucint]
  exact sub_le_sub_left hp _

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma ballAverageKernel_average (f : Space → ℝ) (y : Space) (R : ℝ) :
    (∫ z, f z*ballAverageKernel R (z-y)) =
      (1/(R^3*(Real.pi*4/3)))*(∫ z in closedBall y R, f z) := by
  rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    have hz : z-y ∈ closedBall (0:Space) R ↔ z ∈ closedBall y R := by
      simp only [mem_closedBall,dist_eq_norm,sub_zero]
    by_cases h : z ∈ closedBall y R
    · simp only [ballAverageKernel,indicator_of_mem h,indicator_of_mem (hz.mpr h)]
      ring
    · simp only [ballAverageKernel,indicator_of_notMem h,indicator_of_notMem (mt hz.mp h),mul_zero]

lemma bounded_L1_field_ball_submean {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) {R : ℝ} (hR : 0 < R)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    Z/‖y‖-lam-tfPotential ρ y ≤
      (1/(R^3*(Real.pi*4/3)))*(∫ z in closedBall y R, Z/‖z‖-lam-tfPotential ρ z) := by
  simpa only [ballAverageKernel_average] using
    bounded_L1_field_radial_submean hm hi hM hn hb
      (ballAverageKernel_measurable R) hR (ballAverageKernel_nonneg hR)
      (ballAverageKernel_support R) (ballAverageKernel_bound hR)
      (ballAverageKernel_radial R) (ballAverageKernel_mass hR) y hnuc Z lam

lemma originalQueryDensity_bounded_L1 {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ),
      Measurable (originalQueryDensity F r j c₁ r₀ s z) ∧
      Integrable (originalQueryDensity F r j c₁ r₀ s z) ∧
      (∀ y, 0 ≤ originalQueryDensity F r j c₁ r₀ s z y) ∧
      (∀ y, originalQueryDensity F r j c₁ r₀ s z y ≤ M) := by
  let ell := fun k : Fin K => dyadicObservationWidth r k
  have hm := originalMasterField_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  obtain ⟨M,hM,hb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr₀ hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  refine ⟨M,hM,fun z => ⟨?_,?_,?_,?_⟩⟩
  · exact hm.comp ((measurable_const (a := z)).prodMk measurable_id)
  · exact jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr₀ hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized (originalDatum ell j z)
  · exact jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)
  · intro y
    apply (le_abs_self _).trans
    change |jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y| ≤ M
    simpa only [Real.norm_eq_abs] using hb (originalDatum ell j z) y

theorem originalQueryField_ball_submean {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {R : ℝ} (hR : 0 < R) (y : Space) (hnuc : R ≤ ‖y‖) :
    originalQueryField F Z lam r j c₁ r₀ s z y ≤
      (1/(R^3*(Real.pi*4/3)))*(∫ x in closedBall y R,
        originalQueryField F Z lam r j c₁ r₀ s z x) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  exact bounded_L1_field_ball_submean (hρ z).1 (hρ z).2.1 hM (hρ z).2.2.1
    (hρ z).2.2.2 hR y hnuc Z lam

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SpatialCapSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis

lemma cap_interior_ball_subset {u : ℝ} (hu : 0 < u) {y : Space}
    (hyl : 5*u/4 ≤ ‖y‖) (hyh : ‖y‖ ≤ 7*u/4) :
    closedBall y (u/8) ⊆ closedAnnularShell u (2*u) := by
  intro x hx
  have hxy : ‖x-y‖ ≤ u/8 := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hl := norm_le_norm_sub_add y x
  rw [norm_sub_rev y x] at hl
  have hh := norm_le_norm_sub_add x y
  constructor <;> linarith

lemma scalar_cap_excess_mono {a b C f : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C) :
    max (a^4*f-C) 0 ≤ max (b^4*f-C) 0 := by
  by_cases hf : 0 ≤ f
  · apply max_le_max_right
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 4) hf) C
  · have haf : a^4*f-C ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha 4) (le_of_not_ge hf)]
    rw [max_eq_right haf]
    exact le_max_right _ _

lemma submean_le_capBandStatistic {u C : ℝ} (hu : 0 < u) {f : Space → ℝ}
    (hf : ContinuousOn f (closedAnnularShell u (2*u))) {y : Space}
    (hyl : 5*u/4 ≤ ‖y‖) (hyh : ‖y‖ ≤ 7*u/4)
    (hmean : f y ≤ (1/((u/8)^3*(Real.pi*4/3)))*(∫ x in closedBall y (u/8), f x)) :
    (u/100000)^4*f y ≤ C+capBandStatistic u C f := by
  let A := closedAnnularShell u (2*u)
  let B := closedBall y (u/8)
  let a := (u/100000)^4
  let V := (u/8)^3*(Real.pi*4/3)
  let e := fun x => max (a*f x-C) 0
  have hBA : B ⊆ A := cap_interior_ball_subset hu hyl hyh
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr (isCompact_closedBall y (u/8)).measure_ne_top
  have hfi : IntegrableOn f B := (hf.mono hBA).integrableOn_compact (isCompact_closedBall _ _)
  have hec : ContinuousOn e A := ((hf.const_mul a).sub continuousOn_const).sup continuousOn_const
  have hei : IntegrableOn e A := hec.integrableOn_compact (closedAnnularShell_compact _ _)
  have heB : IntegrableOn e B := hei.mono_set hBA
  have hv : volume.real B = V := space_closedBall_real y (by positivity : 0 ≤ u/8)
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : a*(∫ x in B, f x)-V*C ≤ ∫ x in B, e x := by
    have hh : (∫ x in B, a*f x-C) ≤ ∫ x in B, e x :=
      integral_mono_ae ((hfi.const_mul a).sub (integrable_const C)) heB
        (ae_of_all _ fun x => le_max_left (a*f x-C) 0)
    rw [integral_sub (hfi.const_mul a) (integrable_const C),integral_const_mul,
      integral_const] at hh
    simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hh
    change a*(∫ x in B, f x)-volume.real B*C ≤ ∫ x in B, e x at hh
    rw [hv] at hh
    exact hh
  have hEA : (∫ x in B, e x) ≤ ∫ x in A, e x :=
    setIntegral_mono_set hei (ae_of_all _ fun x => le_max_right _ _) (ae_of_all _ fun _ hx => hBA hx)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  calc
    a*f y ≤ a*((1/V)*(∫ x in B, f x)) := mul_le_mul_of_nonneg_left hmean ha
    _ = C+(1/V)*(a*(∫ x in B, f x)-V*C) := by field_simp; ring
    _ ≤ C+(1/V)*(∫ x in A, e x) := by
      have ht := mul_le_mul_of_nonneg_left (hE.trans hEA) (show 0 ≤ 1/V by positivity)
      linarith only [ht]
    _ = C+capBandStatistic u C f := rfl

theorem capBandStatistic_simultaneous_cap {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    {f : Space → ℝ} (hf : ContinuousOn f (closedAnnularShell u (2*u)))
    (hm : ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      f y ≤ (1/((u/8)^3*(Real.pi*4/3)))*(∫ x in closedBall y (u/8), f x))
    (hstat : capBandStatistic u C f ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 → (localCellRadius y)^4*f y ≤ 16*(C+1) := by
  intro y hyl hyh
  have hb := submean_le_capBandStatistic (C := C) hu hf hyl hyh (hm y hyl hyh)
  have ha : 0 ≤ u/100000 := by positivity
  have hay : localCellRadius y ≤ 2*(u/100000) := by dsimp [localCellRadius]; linarith
  have hpy := pow_le_pow_left₀ (show 0 ≤ localCellRadius y by dsimp [localCellRadius]; positivity) hay 4
  have hp : (localCellRadius y)^4 ≤ 16*(u/100000)^4 := by nlinarith only [hpy]
  by_cases hfy : 0 ≤ f y
  · have hh := mul_le_mul_of_nonneg_right hp hfy
    nlinarith only [hh,hb,hstat]
  · have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg
      (show 0 ≤ localCellRadius y by dsimp [localCellRadius]; positivity) 4) (le_of_not_ge hfy)
    nlinarith only [hh,hC]

open MeasureTheory Set Metric

open CoulombAnalysis

lemma capBandStatistic_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {u C : ℝ} {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u))))) :
    Integrable (fun z => capBandStatistic u C (f z)) μ :=
  hi.integral_prod_left.const_mul _

lemma capBandStatistic_nonneg (u C : ℝ) (hu : 0 < u) (f : Space → ℝ) :
    0 ≤ capBandStatistic u C f := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun _ => le_max_right _ _

lemma capBandStatistic_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u C b : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u)))))
    (hp : ∀ x ∈ closedAnnularShell u (2*u),
      (∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ b) :
    (∫ z, capBandStatistic u C (f z) ∂μ) ≤ 4096*b := by
  let A := closedAnnularShell u (2*u)
  let V := (u/8)^3*(Real.pi*4/3)
  have hV : 0 < V := by dsimp [V]; positivity
  have hAc : IsCompact A := closedAnnularShell_compact _ _
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAc.measure_ne_top
  have hvol : volume.real A ≤ (2*u)^3*(Real.pi*4/3) := by
    rw [←space_closedBall_real (0:Space) (by positivity : 0 ≤ 2*u)]
    refine measureReal_mono ?_ (isCompact_closedBall (0:Space) (2*u)).measure_ne_top
    intro x hx
    simpa only [mem_closedBall,dist_zero_right] using hx.2
  have hpt : (∫ x in A, ∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ volume.real A*b := by
    have hh := integral_mono_ae hi.integral_prod_right (integrable_const b)
      ((ae_restrict_mem hAc.measurableSet).mono fun x hx => hp x hx)
    rw [integral_const] at hh
    simpa only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ] using hh
  calc
    _ = (1/V)*(∫ x in A, ∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) := by
      unfold capBandStatistic
      rw [integral_const_mul,integral_integral_swap hi]
    _ ≤ (1/V)*(volume.real A*b) := mul_le_mul_of_nonneg_left hpt (by positivity)
    _ ≤ (1/V)*(((2*u)^3*(Real.pi*4/3))*b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvol hb) (by positivity)
    _ = 4096*b := by dsimp [V]; field_simp; ring

theorem capBandStatistic_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u C b : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u)))))
    (hp : ∀ x ∈ closedAnnularShell u (2*u),
      (∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ b) :
    μ.real {z | 1 < capBandStatistic u C (f z)} ≤ 4096*b := by
  have ht := capBandStatistic_integrable μ hi
  have hn : 0 ≤ᵐ[μ] (fun z => capBandStatistic u C (f z)) :=
    ae_of_all _ fun z => capBandStatistic_nonneg u C hu (f z)
  have hh := ht.measure_le_integral hn (s := {z | 1 < capBandStatistic u C (f z)})
    (fun _ hz => hz.le)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] at hr
  exact hr.trans (capBandStatistic_expectation μ hu hb hi hp)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SpatialCapActualBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_joint_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) :
    Measurable (fun p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) × Space =>
      originalQueryField F Z lam r j c₁ r₀ s p.1 p.2) := by
  have hm := originalMasterField_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs canonicalRealPacket_smooth.continuous
  exact ((measurable_const.div measurable_snd.norm).sub measurable_const).sub
    (potential_joint_measurable hm)

lemma originalQueryField_continuousOn_annulus {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u : ℝ} (hu : 0 < u) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) (closedAnnularShell u (2*u)) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact ne_of_gt (hu.trans_le hx.1)

lemma original_capBand_excess_prod_integrable {N K : ℕ} (F : fermionGraph N)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (r : ℝ) (j : ℕ)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C) :
    Integrable (fun p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) × Space =>
      max ((u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s p.1 p.2-C) 0)
      ((physicalObservationLaw (graphRawLaw F) K).prod
        (volume.restrict (closedAnnularShell u (2*u)))) := by
  have hAc := closedAnnularShell_compact u (2*u)
  let : IsFiniteMeasure (volume.restrict (closedAnnularShell u (2*u))) :=
    isFiniteMeasure_restrict.mpr hAc.measure_ne_top
  have hm := originalQueryField_joint_measurable (K := K) F Z lam r j hc hr₀ hs
  apply Integrable.of_bound ((hm.const_mul _).sub measurable_const |>.max measurable_const).aestronglyMeasurable
    ((u/100000)^4*(Z/u))
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hAc.measurableSet)] with p hp
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  apply max_le
  · have hq := originalQueryField_le_nuclear F Z r hlam j c₁ r₀ s p.1 p.2
    have hz : Z/‖p.2‖ ≤ Z/u := div_le_div_of_nonneg_left hZ hu hp.1
    have hh := mul_le_mul_of_nonneg_left (hq.trans hz) (show 0 ≤ (u/100000)^4 by positivity)
    change (u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s p.1 p.2-C ≤ _
    linarith only [hh,hC]
  · positivity

lemma original_capBandStatistic_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    (u C : ℝ) :
    Measurable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z)) := by
  have hm := originalQueryField_joint_measurable (K := K) F Z lam r j hc hr₀ hs
  exact (((hm.const_mul _).sub measurable_const).max measurable_const).stronglyMeasurable.integral_prod_right'.measurable.const_mul _

theorem original_capBandStatistic_controls_field {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    (hstat : capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      (localCellRadius y)^4*originalQueryField F Z lam r j c₁ r₀ s z y ≤ 16*(C+1) := by
  apply capBandStatistic_simultaneous_cap hu hC
    (originalQueryField_continuousOn_annulus F Z lam r j hc hr₀ hs hrs z hu) _ hstat
  intro y hyl _
  exact originalQueryField_ball_submean F Z lam r j hc hr₀ hs hrs z (by positivity) y (by linarith)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PolynomialProbabilityBudgetBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma polynomial_log_cost_tendsto (n : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun r : ℝ => r^v*(Real.log (Real.exp 1/r^n))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := v/5
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub (hlog.const_mul (n:ℝ))).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr n).ne',Real.log_exp,Real.log_pow]
  rw [show r^q-n*(Real.log r*r^q) = r^q*(1-n*Real.log r) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 2
  dsimp [q]
  ring

lemma polynomial_probability_budget_tendsto (n : ℕ) {v : ℝ} (hv : 2.02 < v) (δ : ℝ) :
    Tendsto (fun r : ℝ => dyadicUniformEventBudget r (r^n) δ*r^v)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^v) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero (by linarith : 0 < v)).mono_left inf_le_left
  have hh := ((polynomial_log_cost_tendsto n (by linarith : 0 < v-2.02)).const_mul
    observationFisherConstant).add (hp.const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have he : r^(-2.02:ℝ)*r^v = r^(v-2.02) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [add_mul]
  rw [show observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^n))^5*r^v =
    observationFisherConstant*(r^(-2.02:ℝ)*r^v)*(Real.log (Real.exp 1/r^n))^5 by ring,he]
  ring

end Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityRareCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma originalQueryField_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryField F Z lam r j c₁ r₀ s z y) :=
  measurable_const.sub (jointMasterPosterior_potential_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j y hc hr₀ hs canonicalRealPacket_smooth.continuous)

lemma integral_positive_excess_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hi : Integrable f μ)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hA : MeasurableSet {z | C/a < f z}) :
    (∫ z, max (a*f z-C) 0 ∂μ) ≤ a*(∫ z in {z | C/a < f z}, f z ∂μ) := by
  let A := {z | C/a < f z}
  have he : (fun z => max (a*f z-C) 0) = A.indicator (fun z => a*f z-C) := by
    funext z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      exact max_eq_left (by have hz' := (div_lt_iff₀ ha).mp hz; nlinarith)
    · rw [indicator_of_notMem hz]
      apply max_eq_right
      have hz' : f z ≤ C/a := not_lt.mp hz
      have hh := (le_div_iff₀ ha).mp hz'
      nlinarith
  rw [he,integral_indicator hA,integral_sub (hi.const_mul a).integrableOn (integrable_const C),
    integral_const_mul,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  exact sub_le_self _ (mul_nonneg ENNReal.toReal_nonneg hC)

end Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualSimultaneousCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ActualSimultaneousCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_smaller_cap_excess_integral {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C) {y : Space} (hy : u ≤ ‖y‖) :
    (∫ z, max ((u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s z y-C) 0
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
    (∫ z, max ((localCellRadius y)^4*originalQueryField F Z lam r j c₁ r₀ s z y-C) 0
      ∂physicalObservationLaw (graphRawLaw F) K) := by
  have hi := originalQueryField_integrable (K := K) F Z lam r j hc hr₀ hs y
  apply integral_mono_ae (((hi.const_mul _).sub (integrable_const C)).sup (integrable_const 0))
    (((hi.const_mul _).sub (integrable_const C)).sup (integrable_const 0))
  exact ae_of_all _ fun _ => scalar_cap_excess_mono (by positivity)
    (by dsimp [localCellRadius]; linarith) hC

end Work_ActualSimultaneousCap_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusWidthNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier CoulombObservation

theorem fresh_threshold_response_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ n sign h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hn : 2 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*(
      localTFResponse (H i+sign*(tfPatchOscillationConstant/R i*
        (n*masterWidth c₁ (r₀ i) (s i) (y i)))*(R i)⁻¹^4)*
        (∫ x, masterCenteredKernel c₁ (r₀ i) (s i) canonicalRealPacket (y i) x ∂ballMeasure (R i))+
      sign*Real.sqrt ((16*(n*masterWidth c₁ (r₀ i) (s i) (y i))^3*
        ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ (r₀ i) (s i) (y i))⁻¹^4)^2)*(a i)^(-7+(1/100:ℝ)))))
      l (𝓝 (localTFResponse h)) := by
  let t := fun i => masterWidth c₁ (r₀ i) (s i) (y i)
  have ht : ∀ᶠ i in l, 0 < t i := by
    filter_upwards [hr,hs] with i hri hsi
    exact masterWidth_pos hc hri hsi (y i)
  have hosc := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by linarith : 0 ≤ n) ha hR (ht.mono fun _ hi => hi.le) hw0
  have hinner := hH.add (hosc.const_mul sign)
  simp only [mul_zero,add_zero] at hinner
  have hresp := localTFResponse_continuous.continuousAt.tendsto.comp hinner
  have hfit : ∀ᶠ i in l, 2*t i < R i := by
    filter_upwards [ha,hR,hw0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))]
      with i hai hRi hi
    have hh : t i < (1/2:ℝ)*a i := (div_lt_iff₀ hai).mp hi
    linarith
  have hmass := masterCenteredKernel_mass_tendsto canonicalRealPacket_smooth
    canonicalRealPacket_support canonicalRealPacket_normalized hc hcL hr hs hs0 hfit
  have herr := inverse_duality_tendsto (L := (masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ))
    hc₂ (by linarith : 0 ≤ n) ha ha0 hw
  have hh := (hresp.mul hmass).add (herr.const_mul sign)
  simp only [mul_one,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [ha] with i hai
  simp only [Function.comp_apply]
  rw [show (a i)^4*H i+sign*((a i)^4*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) =
      (a i)^4*(H i+sign*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) by ring,
    ←localTFResponse_rescale hai]
  dsimp only [t]
  ring

lemma freshLowThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshLowThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshLowThreshold,localTFResponse,neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using
    (fresh_threshold_response_tendsto_of_width (sign := -1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 2)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma freshHighThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshHighThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshHighThreshold,localTFResponse,one_mul] using
    (fresh_threshold_response_tendsto_of_width (sign := 1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 3)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma inverse_density_error_tendsto_of_width {ι : Type*} {l : Filter ι}
    {r₀ s ell : ι → ℝ} {y : ι → Space} {c₁ c₂ E C : ℝ}
    (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ)) :
    Tendsto (fun i => (localCellRadius (y i))^6*inverseDensityError c₁ (r₀ i) (s i) (ell i) C (y i)) l (𝓝 0) := by
  have ha := hy.mono fun i hi => localCellRadius_pos hi
  exact inverse_observation_error_tendsto hc₂ hE ha ha0 hw hell (scaled_div_pow_constant ha 3 C)

theorem low_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hh : 0 ≤ h) (hxi : 0 < xi)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, LowInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h+xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h+xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshLowThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_low_density_margin ha hT hdenerr hF
    (localTFResponse_strict_mono hh (by linarith : h < h+xi/2))
  have hgap := inverse_low_gap_tendsto tfPatchCapConstant_pos.le ha hR hG
  have hleft := (hH.add hgap).add hpot
  simp only [add_zero] at hleft
  have hright := scaled_div_pow_constant ha 4 (h+xi)
  have hsmall := hleft.eventually_lt hright (by linarith : h+xi/2 < h+xi)
  filter_upwards [ha,hdensity,hsmall] with i hai hdi hsi
  refine ⟨hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

theorem high_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, HighInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h-xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h-xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  have hgap := inverse_high_gap_tendsto ha hH hG
  have hmass := inverse_retained_tendsto hc₂ canonicalMasterAmplitude_pos.le ha ha0 hw
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshHighThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_high_density_margin ha hT hdenerr hF hmass
    (localTFResponse_nonneg (h-xi/2))
    (localTFResponse_strict_mono (by linarith : 0 ≤ h-xi/2) (by linarith : h-xi/2 < h))
  have hosc := inverse_unscaled_oscillation_tendsto ha hR hw0 tfPatchOscillationConstant 3
  have hoscsmall := hosc.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have hoscscaled := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by norm_num : (0:ℝ) ≤ 3) ha hR ht hw0
  have hleft := (scaled_div_pow_constant ha 4 (h-xi)).add hpot
  simp only [add_zero] at hleft
  have hright := (hH.sub hgap).sub (hoscscaled.const_mul 2)
  simp only [sub_zero,mul_zero] at hright
  have hsmall := hleft.eventually_lt hright (by linarith : h-xi < h-xi/2)
  filter_upwards [ha,hoscsmall,hdensity,hsmall] with i hai hosi hdi hsi
  refine ⟨hosi.le,hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusGeometry
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma fullAnnulus_local_radius_le {B u : ℝ} {y : Space}
    (hBu : 0 ≤ B*u) (hy : ‖y‖ ≤ B*u) : localCellRadius y ≤ B*u := by
  unfold localCellRadius
  linarith

lemma masterWidth_fullAnnulus_lower {c₁ B r₀ s : ℝ} {y : Space}
    (hc : 0 ≤ c₁) (hB : 1 ≤ B) (hy : y ≠ 0)
    (has : localCellRadius y ≤ B*s) :
    (c₁/B^(1+masterExponent))*(localCellRadius y)^(1+masterExponent) ≤
      masterWidth c₁ r₀ s y := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have ha := localCellRadius_pos hy
  have hr : 0 < localCellRadius y/B := div_pos ha hBp
  have hrs : localCellRadius y/B ≤ s := (div_le_iff₀ hBp).mpr (by nlinarith only [has])
  have hry : localCellRadius y/B ≤ ‖y‖ := by
    have hdiv : localCellRadius y/B ≤ localCellRadius y :=
      div_le_self ha.le hB
    apply hdiv.trans
    unfold localCellRadius
    linarith [norm_nonneg y]
  have hh := masterWidth_radius_lower (r₀ := r₀) hc hr hrs hry
  rw [Real.div_rpow ha.le hBp.le] at hh
  convert hh using 1 <;> first | rfl | ring

lemma fullAnnulus_local_radius_tendsto {ι : Type*} {l : Filter ι}
    {s u : ι → ℝ} {y : ι → Space} {B : ℝ} (hB : 0 ≤ B)
    (hs0 : Tendsto s l (𝓝 0)) (hu : ∀ᶠ i in l, 0 < u i)
    (hus : ∀ᶠ i in l, u i ≤ s i) (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) :
    Tendsto (fun i => localCellRadius (y i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => B*s i) l (𝓝 0) := by
    simpa only [mul_zero] using hs0.const_mul B
  apply squeeze_zero' (Eventually.of_forall (fun _ => by unfold localCellRadius; positivity)) _ hb
  filter_upwards [hu,hus,hy] with i hui husi hyi
  exact (fullAnnulus_local_radius_le (mul_nonneg hB hui.le) hyi).trans
    (mul_le_mul_of_nonneg_left husi hB)

theorem fullAnnulus_event_excess_tendsto (n : ℕ) {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {y : ι → Space} {B w δ : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => dyadicUniformEventBudget (u i) ((u i)^n) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := (polynomial_probability_budget_tendsto n (by linarith : (2.02:ℝ) < 7-w) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu0,hu⟩)
  have hb : Tendsto (fun i => B^(7-w)*
      (dyadicUniformEventBudget (u i) ((u i)^n) δ*(u i)^(7-w))) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using he.const_mul (B^(7-w))
  have hn : ∀ᶠ i in l, 0 ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ := by
    filter_upwards [hu,hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
    exact dyadicUniformEventBudget_nonneg hi (pow_pos hi _) (pow_le_one₀ hi.le hi1.le) hδ
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hu,hy,hn] with i hi hyi hni
    calc
      _ ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ*(B*u i)^(7-w) := by
        apply mul_le_mul_of_nonneg_left _ hni
        exact Real.rpow_le_rpow (by unfold localCellRadius; positivity)
          (fullAnnulus_local_radius_le (mul_nonneg hB hi.le) hyi) (by linarith)
      _ = _ := by rw [Real.mul_rpow hB hi.le]; ring

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation

theorem own_probability_fullAnnulus_excess_tendsto {ι : Type*} {l : Filter ι}
    {r p : ι → ℝ} {y : ι → Space} {B w δ : ℝ} (hB : 0 ≤ B)
    (hr : ∀ᶠ i in l, 0 < r i) (hr0 : Tendsto r l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*r i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := own_probability_weighted_budget_tendsto hr hr0 hp hp0 (δ := δ)
    (by linarith : (2.02:ℝ) < 7-w)
  have hn : ∀ᶠ i in l, 0 ≤ (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ := by
    filter_upwards [hr,hp,hp0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hpi hpi1
    exact mul_nonneg (Real.rpow_nonneg hpi.le _)
      (dyadicUniformEventBudget_nonneg hi hpi hpi1.le hδ)
  have hb : Tendsto (fun i => B^(7-w)*
      ((p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(r i)^(7-w))) l (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (B^(7-w))
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hr,hy,hn] with i hi hyi hni
    calc
      _ ≤ (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(B*r i)^(7-w) := by
        apply mul_le_mul_of_nonneg_left _ hni
        exact Real.rpow_le_rpow (by unfold localCellRadius; positivity)
          (fullAnnulus_local_radius_le (mul_nonneg hB hi.le) hyi) (by linarith)
      _ = _ := by rw [Real.mul_rpow hB hi.le]; ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpandedAnnulusGeometry
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma masterWidth_relative_tendsto_half {ι : Type*} {l : Filter ι}
    {c₁ : ℝ} (hc : 0 < c₁) {r₀ s : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0)) (hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖) :
    Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i))
      l (𝓝 0) := by
  have ht : Tendsto (fun i => (c₁*200000)*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (c₁*200000)
  apply squeeze_zero' _ _ ht
  · filter_upwards [hr,hs] with i hri hsi
    exact div_nonneg (masterWidth_pos hc hri hsi _).le (by unfold localCellRadius; positivity)
  · filter_upwards [hr,hs,hry] with i hri hsi hryi
    have hyi : y i ≠ 0 := norm_pos_iff.mp (by linarith)
    have ha := localCellRadius_pos hyi
    apply (div_le_iff₀ ha).mpr
    have hh := masterWidth_upper hc.le hri hsi (y i)
    have hmax : masterBaseDistance (r₀ i) (y i) ≤ 2*‖y i‖ := by
      exact max_le (by linarith [norm_nonneg (y i)]) hryi
    calc
      _ ≤ c₁*(2*‖y i‖)*(s i)^masterExponent := hh.trans (by gcongr)
      _ = _ := by unfold localCellRadius; ring

lemma half_band_observation_width_bound {u : ℝ} {y : Space} (hu : 0 < u) (hy : u/2 ≤ ‖y‖) :
    0 ≤ u^(101/100:ℝ) ∧
      u^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius y)^(101/100:ℝ) := by
  constructor
  · positivity
  · have hh := Real.rpow_le_rpow hu.le (by linarith : u ≤ 2*‖y‖)
      (by norm_num : (0:ℝ) ≤ 101/100)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [←Real.mul_rpow (by norm_num) (by unfold localCellRadius; positivity)]
    congr 1
    unfold localCellRadius
    ring

theorem expandedAnnulus_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      LowInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      HighInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      universalCellCountConstant*(localOffsetMass (dyadicUniformEventBudget (u i) ((u i)^40) δ) (y i))^2 <
        (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c₂ : ℝ := c₁/B^(1+masterExponent)
  have hc₂ : 0 < c₂ := div_pos hc (Real.rpow_pos_of_pos hBp _)
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyl := hband.mono fun _ hi => hi.2.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hu,hyl] with i hui hyi
    exact norm_pos_iff.mp (by linarith)
  have ha := hy.mono fun _ hi => localCellRadius_pos hi
  have ha0 := fullAnnulus_local_radius_tendsto hBp.le hs0 hu hus hyu
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤
      masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hy,hu,hus,hyu] with i hyi hui husi hyui
    apply masterWidth_fullAnnulus_lower hc.le hB hyi
    exact (fullAnnulus_local_radius_le (mul_nonneg hBp.le hui.le) hyui).trans
      (mul_le_mul_of_nonneg_left husi hBp.le)
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius (y i))^(101/100:ℝ) := by
    filter_upwards [hu,hyl] with i hui hyi
    exact half_band_observation_width_bound hui hyi
  have hD := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hDgap := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num : (1/100:ℝ) < 1/10) hδ
  have hgeom := inverse_geometry_eventually ha ha0 hwidth
    (observation_relative_tendsto (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) ha ha0 hell)
  have hlow := low_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) (by linarith : 0 ≤ h) hxi
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hhigh := high_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) hxi hxih
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hcount := inverse_count_margin_eventually hy ha0 hD
  filter_upwards [hgeom,hlow,hhigh,hcount] with i hi hlo hhi hci
  refine ⟨?_,hlo,hhi,hci⟩
  rcases hi with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier

theorem own_probability_expandedAnnulus_weighted_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s p : ι → ℝ} {y : ι → Space} {B c₁ δ : ℝ} (hB : 0 ≤ B)
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      (localCellRadius (y i))^4*(p i*originalFieldCapBudget (u i) (p i) δ c₁
        (r₀ i) (s i) (y i) ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)) ≤
      (p i)^(3/4:ℝ)*(tfPatchCapConstant+1) := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp (by linarith [hi.1,hi.2.1,hi.2.2.2.1])
  have ha0 := fullAnnulus_local_radius_tendsto hB hs0 hu hus hyu
  have hD := own_probability_fullAnnulus_excess_tendsto (δ := δ) hB hu hu0 hp hp0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hlim := physical_field_cap_tendsto hy ha0 hD ht hwidth
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    tfPatchCapConstant < tfPatchCapConstant+1))
  filter_upwards [hy,hp,ht,hbound,hp0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hyi hpi hti hbi hpi1
  have ha := localCellRadius_pos hyi
  have hh := probability_weighted_cap
    (b := (localCellRadius (y i))^(6/5:ℝ))
    (q := localCellRadius (y i)*(localCellRadius (y i))^masterExponent) (D := dyadicUniformEventBudget (u i) (p i) δ)
    hyi (by positivity) (by positivity) (by positivity : 0 ≤ 2*masterWidth c₁ (r₀ i) (s i) (y i)) hpi hpi1.le
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
  change (localCellRadius (y i))^4*(p i*
    physicalFieldCapBudget (dyadicUniformEventBudget (u i) (p i) δ) (y i)
      ((localCellRadius (y i))^(6/5:ℝ))
      (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)
      (2*masterWidth c₁ (r₀ i) (s i) (y i))) ≤ _
  calc _ ≤ _ := hmul
       _ = (p i)^(3/4:ℝ)*((localCellRadius (y i))^4*
          physicalFieldCapBudget ((p i)^(1/4:ℝ)*dyadicUniformEventBudget (u i) (p i) δ) (y i)
            ((localCellRadius (y i))^(6/5:ℝ))
            (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)
            (2*masterWidth c₁ (r₀ i) (s i) (y i))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hbi.le (Real.rpow_nonneg hpi.le _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpandedAnnulusCapNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

lemma cap_expandedAnnulus_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      originalFieldCapBudget (u i) ((u i)^80) δ c₁ (r₀ i) (s i) (y i)
        ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent) <
          (tfPatchCapConstant+2)/(localCellRadius (y i))^4 := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp (by linarith [hi.1,hi.2.1,hi.2.2.2.1])
  have ha0 := fullAnnulus_local_radius_tendsto (by linarith : 0 ≤ B) hs0 hu hus hyu
  have hD := fullAnnulus_event_excess_tendsto 80 (δ := δ) (by linarith : 0 ≤ B) hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hlim := physical_field_cap_tendsto hy ha0 hD ht hwidth
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    tfPatchCapConstant < tfPatchCapConstant+2))
  have hgeom := expandedAnnulus_inverse_numerics_eventually (h := 1) (xi := 1) (δ := 0) hB hc hcL
    (by norm_num) (by norm_num) (by norm_num) hs0 hband
  filter_upwards [hy,hbound,hgeom] with i hyi hi hgi
  refine ⟨hgi.1,?_⟩
  apply (lt_div_iff₀ (pow_pos (localCellRadius_pos hyi) 4)).mpr
  change _*physicalFieldCapBudget _ _ _ _ _ < _ at hi
  simpa only [originalFieldCapBudget,physicalFieldCapBudget,mul_comm] using hi

theorem own_probability_expandedAnnulus_cap_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s : ι → ℝ} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hr₀ : ∀ᶠ i in l, 0 < r₀ i) :
    ∀ᶠ i in l, ∀ (u : ℝ) (y : Space) (p : ℝ),
      r₀ i ≤ u → u ≤ s i → u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u → 0 < p → p ≤ u^80 →
      (localCellRadius y)^4*(p*originalFieldCapBudget u p δ c₁ (r₀ i) (s i) y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)) ≤
      p^(3/4:ℝ)*(tfPatchCapConstant+1) := by
  let A : ι → Type := fun i => {q : ℝ × Space × ℝ //
    r₀ i ≤ q.1 ∧ q.1 ≤ s i ∧ q.1/2 ≤ ‖q.2.1‖ ∧ ‖q.2.1‖ ≤ B*q.1 ∧
      0 < q.2.2 ∧ q.2.2 ≤ q.1^80}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have hπ : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧ r₀ (π q) ≤ q.2.1.1 ∧
      q.2.1.1 ≤ s (π q) ∧ q.2.1.1/2 ≤ ‖q.2.1.2.1‖ ∧ ‖q.2.1.2.1‖ ≤ B*q.2.1.1 := by
    filter_upwards [hπ.eventually hr₀] with q hq
    exact ⟨hq,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1⟩
  have hu0 : Tendsto (fun q : Σ i, A i => q.2.1.1) L (𝓝 0) :=
    squeeze_zero' (hb.mono fun _ h => (h.1.trans_le h.2.1).le)
      (hb.mono fun _ h => h.2.2.1) (hs0.comp hπ)
  have hp : ∀ᶠ q : Σ i, A i in L, 0 < q.2.1.2.2 :=
    Eventually.of_forall fun q => q.2.2.2.2.2.2.1
  have hp0 : Tendsto (fun q : Σ i, A i => q.2.1.2.2) L (𝓝 0) := by
    apply squeeze_zero' (hp.mono fun _ h => h.le)
      (Eventually.of_forall fun q => q.2.2.2.2.2.2.2)
    simpa using hu0.pow 80
  have hh := own_probability_expandedAnnulus_weighted_cap_eventually (by linarith : 0 ≤ B) hc hδ (hs0.comp hπ) hp hp0 hb
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro u y p hru hus hyl hyu hpv hpu
  exact hi ⟨i,⟨(u,y,p),hru,hus,hyl,hyu,hpv,hpu⟩⟩ rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpandedAnnulusCapExcess
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem actual_expandedAnnulus_cap_excess_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {y : ι → Space} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {j : ∀ i, Fin (K i+1)} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i ∧
      ((2:ℝ)^(j i).val*r₀ i)/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*((2:ℝ)^(j i).val*r₀ i))
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l,
      (∫ z, max ((localCellRadius (y i))^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^(j i).val*r₀ i)^60 := by
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hb : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i := by
    filter_upwards [hband] with i hi
    refine ⟨hi.1,?_,hi.2⟩
    dsimp only [u]
    exact le_mul_of_one_le_left hi.1.le (one_le_pow₀ (by norm_num))
  have hnum := cap_expandedAnnulus_numerics_eventually hB hc hcL hδ hs0 hb
  have hw := own_probability_expandedAnnulus_cap_uniform_eventually hB hc hδ hs0 (hb.mono fun _ hi => hi.1)
  filter_upwards [hb,hnum,hw,hstate,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hbi hni hwi hFi hsi
  have hui : 0 < u i := hbi.1.trans_le hbi.2.1
  have hsy : 0 < s i := hui.trans_le hbi.2.2.1
  have hy : y i ≠ 0 := norm_pos_iff.mp (by linarith [hbi.2.2.2.1])
  have ha := localCellRadius_pos hy
  have hu1 := hbi.2.2.1.trans hsi.le
  let A : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) := {z | (tfPatchCapConstant+2)/(localCellRadius (y i))^4 <
    originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)}
  have hA : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)] A :=
    measurableSet_lt measurable_const
      (originalQueryField_info_measurable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
  have hp := hFi.2.2.rare_cap_event_of_cell hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hy hu1 hni.1 hni.2
  have hsml := hFi.2.2.expandedAnnulus_small_event_integral hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hbi.2.2.2.1 hu1 hni.1
    (fun p hpp hpu => hwi (u i) (y i) p hbi.2.1 hbi.2.2.1 hbi.2.2.2.1 hbi.2.2.2.2 hpp hpu)
    A hA hp.le
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  have hh := integral_positive_excess_le (physicalObservationLaw (graphRawLaw (F i)) (K i))
    (originalQueryField_integrable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
    hC (pow_pos ha 4)
    ((observationInformation_le (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)) A hA)
  exact hh.trans hsml

theorem actual_expandedAnnulus_cap_excess_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i+1)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
      (∫ z, max ((localCellRadius y)^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^j.val*r₀ i)^60 := by
  let A : ι → Type := fun i => {p : Fin (K i+1) × Space //
    (2:ℝ)^p.1.val*r₀ i ≤ s i ∧
    ((2:ℝ)^p.1.val*r₀ i)/2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ B*((2:ℝ)^p.1.val*r₀ i)}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧
      (2:ℝ)^q.2.1.1.val*r₀ (π q) ≤ s (π q) ∧
      ((2:ℝ)^q.2.1.1.val*r₀ (π q))/2 ≤ ‖q.2.1.2‖ ∧
      ‖q.2.1.2‖ ≤ B*((2:ℝ)^q.2.1.1.val*r₀ (π q)) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := actual_expandedAnnulus_cap_excess_eventually
    (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1.1)
    hB hc hcL hδ (hs0.comp ht) hb (ht.eventually hstate)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j y hjs hyl hyu
  exact hi ⟨i,⟨(j,y),hjs,hyl,hyu⟩⟩ rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ScaledOriginalCap
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier

 theorem actual_scaled_original_cap_eventually_oai {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {a c₁ δ : ℝ} (ha : 1/2 ≤ a)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ j : Fin (K i+1), (2:ℝ)^j.val*r₀ i ≤ s i →
      let u := (2:ℝ)^j.val*r₀ i
      let T := fun z => capBandStatistic (a*u) (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
      Measurable T ∧
      (physicalObservationLaw (graphRawLaw (F i)) (K i)).real {z | 1 < T z} ≤
        4096*(tfPatchCapConstant+2)*u^60 ∧
      ∀ z, T z ≤ 1 → ∀ y, 5*(a*u)/4 ≤ ‖y‖ → ‖y‖ ≤ 7*(a*u)/4 →
        (localCellRadius y)^4*
          originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y ≤
          16*(tfPatchCapConstant+3) := by
  have ha0 : 0 < a := by linarith
  have hh := actual_expandedAnnulus_cap_excess_uniform_eventually (by linarith : 1 ≤ 2*a)
    hc hcL hδ hs0 hr₀ hstate
  filter_upwards [hh,hr₀,hstate] with i hi hri hFi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hv : 0 < a*u := mul_pos ha0 hu
  have hsi : 0 < s i := hu.trans_le hjs
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  refine ⟨original_capBandStatistic_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsi _ _,?_,?_⟩
  · have hp := capBandStatistic_failure_probability
      (physicalObservationLaw (graphRawLaw (F i)) (K i)) hv
      (show 0 ≤ (tfPatchCapConstant+2)*u^60 by positivity)
      (original_capBand_excess_prod_integrable (F i) hFi.1 hFi.2.1.le (r₀ i) j hc hri hsi hv hC)
      (fun y hy => (original_smaller_cap_excess_integral (F i) (Z i) (lam i) (r₀ i) j
        hc hri hsi hv hC hy.1).trans (hi j y hjs (by nlinarith [hy.1]) (by nlinarith [hy.2])))
    simpa only [mul_assoc] using hp
  · intro z hz
    have ht := original_capBandStatistic_controls_field (F i) (Z i) (lam i) (r₀ i) j
      hc hri hsi (hru.trans hjs) z hv hC hz
    simpa only [u,add_assoc,show (2:ℝ)+1 = 3 by norm_num] using ht

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombAtom.actual_scaled_original_cap_eventually_oai.{u_1} := @OAI.CoulombAtom.actual_scaled_original_cap_eventually_oai.{u_1}
