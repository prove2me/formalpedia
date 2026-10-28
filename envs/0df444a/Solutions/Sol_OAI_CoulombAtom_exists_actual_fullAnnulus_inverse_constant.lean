-- Prove2me | solution 1 for OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:45:21.520994+00:00
-- url     : https://prove2.me/submissions/ddc238d7-3b33-40ff-8dc6-14b65e44e52d

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_actual_expandedAnnulus_inverse_uniform_eventually
import Theorems.Thm_OAI_CoulombAtom_actual_scaled_original_cap_eventually

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierWeakMaxGeneralBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

lemma dyadicObservationWidth_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < dyadicObservationWidth r k := Real.rpow_pos_of_pos (by positivity) _

end CoulombObservation

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

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

lemma unorderedStatistic_measurable {N : ℕ} {g : Space → ℝ} (hg : Measurable g) :
    Measurable (unorderedStatistic (N := N) g) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : Configuration N => ∑ i, g (x i))
  exact Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))

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

lemma observedStatistic_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} (hg : Measurable g) :
    Measurable[observationInformation ell j]
      (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
        ∑ i, g (physicalObservedConfiguration ell k z i)) := by
  have h := (unorderedStatistic_measurable (N := N) hg).comp
    (comap_measurable (unorderedObservedConfiguration (N := N) ell k))
  apply h.mono
  · exact le_iSup_of_le k (by rw [ite_eq_left hk])
  · exact le_refl _

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

namespace CoulombObservation

lemma compactNoiseLaw_ae_support : ∀ᵐ u ∂compactNoiseLaw, |u| < 1 := by
  rw [compactNoiseLaw,ae_withDensity_iff compactNoiseDensity_measurable.ennreal_ofReal]
  apply ae_of_all
  intro u hu
  by_contra hn
  exact hu (by simp [compactNoiseDensity,compactNoiseWeight,hn])

lemma compactNoiseLaw_pi_ae_support {ι : Type*} [Fintype ι] :
    ∀ᵐ u ∂Measure.pi (fun _ : ι => compactNoiseLaw), ∀ i, |u i| < 1 :=
  eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => compactNoiseLaw) (i := i)).eventually
      compactNoiseLaw_ae_support)

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

lemma physicalObservedConfiguration_displacement {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (hk : 0 ≤ ell k) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hu : ∀ q, |z.2 q| < 1) (i : Fin N) :
    ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have he (a : Fin 3) : (physicalObservedConfiguration ell k z i-z.1 i) a =
      ell k*z.2 (k,i,a) := by
    change (z.1 i a+ell k*z.2 (k,i,a))-z.1 i a = _
    ring
  have hs : ‖physicalObservedConfiguration ell k z i-z.1 i‖^2 ≤ 3*(ell k)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [he]
    calc
      _ ≤ ∑ _a : Fin 3, (ell k)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have hsq : (z.2 (k,i,a))^2 ≤ 1 := by
          have := hu (k,i,a)
          have := abs_nonneg (z.2 (k,i,a))
          nlinarith [sq_abs (z.2 (k,i,a))]
        rw [mul_pow]
        exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq (mul_one _)
      _ = _ := by simp
  have hs3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 3*ell k := mul_nonneg (Real.sqrt_nonneg _) hk
  nlinarith [sq_nonneg (‖physicalObservedConfiguration ell k z i-z.1 i‖-Real.sqrt 3*ell k)]

lemma physicalObservationLaw_ae_displacement {N K : ℕ} (μ : Measure (Configuration N))
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ k i,
      ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := μ)
    (ν := Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).tendsto_ae.eventually
      compactNoiseLaw_pi_ae_support
  exact h.mono (fun z hz k i => physicalObservedConfiguration_displacement ell k (hell k) z hz i)

end CoulombAtom

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_L1_laplacian_pair_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) (volume.prod volume) := by
  have hΔ := tfLaplacian_continuous hφ
  have hΔc := tfLaplacian_compact hφ hc
  have hj : Measurable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) :=
    ((hm.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm).mul (hΔ.measurable.comp measurable_fst)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => (bounded_L1_potential_integrable hm hi hM hn hb x).mul_const (Δ φ x)),?_⟩
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have htest := CoulombBarrier.locallyIntegrable_mul_test hp.locallyIntegrable hΔ.norm hΔc.norm
  have he (x : TFSpace) : (∫ y, ‖ρ y/‖x-y‖*Δ φ x‖) = tfPotential ρ x*‖Δ φ x‖ := by
    simp_rw [norm_mul,Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _))]
    exact integral_mul_const _ _
  simpa only [he] using htest

theorem bounded_L1_weak_poisson {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  calc
    _ = ∫ x, ∫ y, ρ y/‖x-y‖*Δ φ x := by simp only [integral_mul_const,tfPotential]
    _ = ∫ y, ∫ x, ρ y/‖x-y‖*Δ φ x :=
      integral_integral_swap (bounded_L1_laplacian_pair_integrable hm hi hM hn hb hφ hc)
    _ = ∫ y, ρ y*tfPotential (Δ φ) y := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x, ρ y/‖x-y‖*Δ φ x) = ρ y*(∫ x, Δ φ x/‖y-x‖)
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only; rw [norm_sub_rev]; ring
    _ = _ := by
      simp_rw [tfPotential_laplacian hφ hc]
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

end CoulombAnalysis

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakPoissonOscillationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

open CoulombAtom

lemma exists_global_weak_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → Continuous u → Measurable ρ →
      (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
      Function.support ρ ⊆ ball 0 R →
      (∀ z ∈ closedBall (0 : Space) R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x‖ ≤ R/6 →
        |u x-u 0| ≤ C/R*‖x‖*(B+M*R^2+max (-u 0) 0) := by
  obtain ⟨Ch,hCh,harm⟩ := exists_weak_harmonic_oscillation_constant
  let A : ℝ := 1+8*Real.pi
  let C : ℝ := 3*Ch*A+8*Real.pi
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u ρ R B M hR hB hM hu hm hn hb hs hcap hw x hx
  let P := tfPotential ρ
  have hp := bounded_support_memLp hm hn hb hs (5/3)
  have hP : Continuous P := tfPotential_continuous (bounded_support_integrable hm hn hb hs) hp
  have hPn (z : Space) : 0 ≤ P z := tfPotential_nonneg (Eventually.of_forall hn) z
  have hpb (z : Space) (hz : ‖z‖ ≤ R) : P z ≤ 8*Real.pi*M*R^2 :=
    bounded_density_potential_le hm hM hR hn hb hs z hz
  have hpd : |P x-P 0| ≤ 8*Real.pi*M*R*‖x‖ := by
    simpa only [sub_zero] using bounded_density_potential_difference hm hM hR hn hb hs x 0
      (hx.trans (by linarith)) (by simp; exact hR.le)
  let H : Space → ℝ := fun z => u z+P z
  have hH : Continuous H := hu.add hP
  have hHw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R → (∫ z, H z*Δ g z) = 0 := by
    intro g hg hcg hsg
    have hiu : Integrable (fun z => u z*Δ g z) :=
      (hu.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hip : Integrable (fun z => P z*Δ g z) :=
      (hP.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hpot := tfPotential_weak_laplacian_ball hp hs hg hcg hsg
    dsimp only [H]
    simp_rw [add_mul]
    rw [integral_add hiu hip,hw g hg hcg hsg,hpot]
    ring
  let K : ℝ := B+8*Real.pi*M*R^2
  let v : Space → ℝ := fun z => K-H z
  have hvc : Continuous v := continuous_const.sub hH
  have hvn : ∀ z ∈ closedBall (0 : Space) (3*(R/3)), 0 ≤ v z := by
    intro z hz
    have hz' : z ∈ closedBall (0 : Space) R := by convert hz using 1; congr 1; ring
    have ht := hcap z hz'
    have hpz := hpb z (by simpa only [mem_closedBall,dist_zero_right] using hz')
    dsimp [v,K,H]
    linarith
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*(R/3)) → (∫ z, v z*Δ g z) = 0 := by
    intro g hg hcg hsg
    apply weak_harmonic_upper_distance hH K hHw hg hcg
    convert hsg using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hv := harm v (R/3) (by linarith) hvc.continuousOn hvn hvw x (by linarith)
  let Q : ℝ := B+M*R^2+max (-u 0) 0
  have hn0 : 0 ≤ max (-u 0) 0 := le_max_right _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hv0 : v 0 ≤ A*Q := by
    have ht := hPn 0
    have hc := le_max_left (-u 0) 0
    have hmr : 0 ≤ M*R^2 := mul_nonneg hM (sq_nonneg R)
    dsimp [v,K,H,A,Q]
    nlinarith [mul_nonneg (show 0 ≤ 8*Real.pi by positivity) (add_nonneg hB hn0)]
  have hv' : |H x-H 0| ≤ (3*Ch*A)/R*‖x‖*Q := by
    have he : v x-v 0 = -(H x-H 0) := by dsimp [v]; ring
    rw [he,abs_neg] at hv
    apply hv.trans
    calc
      _ ≤ Ch/(R/3)*‖x‖*(A*Q) := mul_le_mul_of_nonneg_left hv0 (by positivity)
      _ = _ := by ring
  have hp' : |P x-P 0| ≤ (8*Real.pi)/R*‖x‖*Q := by
    apply hpd.trans
    calc
      _ = (8*Real.pi)/R*‖x‖*(M*R^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  calc
    |u x-u 0| = |(H x-H 0)-(P x-P 0)| := by dsimp [H]; congr 1; ring
    _ ≤ |H x-H 0|+|P x-P 0| := abs_sub _ _
    _ ≤ (3*Ch*A)/R*‖x‖*Q+(8*Real.pi)/R*‖x‖*Q := add_le_add hv' hp'
    _ = C/R*‖x‖*Q := by dsimp [C]; ring

theorem exists_weak_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → ContinuousOn u (closedBall 0 R) → Measurable ρ →
      (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
      Function.support ρ ⊆ ball 0 R →
      (∀ z ∈ closedBall (0 : Space) R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x‖ ≤ R/6 →
        |u x-u 0| ≤ C/R*‖x‖*(B+M*R^2+max (-u 0) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_global_weak_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro u ρ R B M hR hB hM hu hm hn hb hs hcap hw x hx
  let f : C(closedBall (0 : Space) R,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) R) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) R,ℝ) => h ⟨z,hz⟩) hv
  have hh := hbound v ρ R B M hR hB hM v.continuous hm hn hb hs
    (fun z hz => by rw [he z hz]; exact hcap z hz) (fun g hg hcg hsg => ?_) x hx
  · simpa only [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/6 ≤ R)),
      he 0 (mem_closedBall_self hR.le)] using hh
  · rw [←hw g hg hcg hsg]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hsg (tfLaplacian_support hg hz)))]

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

open CoulombAtom

theorem exists_local_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (y : Space) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → ContinuousOn u (closedBall y R) → Measurable ρ →
      (∀ z ∈ ball y R, 0 ≤ ρ z) → (∀ z ∈ ball y R, ρ z ≤ M) →
      (∀ z ∈ closedBall y R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball y R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x-y‖ ≤ R/6 →
        |u x-u y| ≤ C/R*‖x-y‖*(B+M*R^2+max (-u y) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_weak_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro u ρ y R B M hR hB hM hu hm hn hb hcap hw x hx
  let v : Space → ℝ := fun z => u (y+z)
  let q : Space → ℝ := (ball 0 R).indicator (fun z => ρ (y+z))
  have hball (z : Space) (hz : z ∈ ball (0 : Space) R) : y+z ∈ ball y R := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hclosed (z : Space) (hz : z ∈ closedBall (0 : Space) R) : y+z ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hv : ContinuousOn v (closedBall 0 R) :=
    hu.comp (continuous_const.add continuous_id).continuousOn hclosed
  have hqm : Measurable q :=
    (hm.comp (measurable_const.add measurable_id)).indicator measurableSet_ball
  have hqn : ∀ z, 0 ≤ q z := indicator_nonneg (fun z hz => hn _ (hball z hz))
  have hqb : ∀ z, q z ≤ M := by
    intro z
    by_cases hz : z ∈ ball (0 : Space) R
    · dsimp only [q]
      rw [indicator_of_mem hz]
      exact hb _ (hball z hz)
    · dsimp only [q]
      rw [indicator_of_notMem hz]
      exact hM
  have hqs : Function.support q ⊆ ball 0 R := support_indicator_subset
  have hvc : ∀ z ∈ closedBall (0 : Space) R, v z ≤ B := fun z hz => hcap _ (hclosed z hz)
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R → (∫ z, v z*Δ g z) = 4*Real.pi*(∫ z, q z*g z) := by
    intro g hg hcg hsg
    let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y R := by
      intro z hz
      have ht := hsg (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using ht
    have ht := hw G hG hcG hsG
    rw [tfLaplacian_translate g (-y)] at ht
    have hi := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    have he : (∫ z, v z*Δ g z) = ∫ z, u z*Δ g (-y+z) := by
      simpa only [v,neg_add_cancel_left] using hi
    rw [he,ht]
    congr 1
    have hj := integral_add_left_eq_self (μ := volume) (fun z => ρ z*G z) y
    calc
      _ = ∫ z, ρ (y+z)*g z := by simpa only [G,neg_add_cancel_left] using hj.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun z => by
        by_cases hz : g z = 0
        · simp only [hz,mul_zero]
        · dsimp only [q]
          rw [indicator_of_mem (hsg (subset_tsupport g hz))])
  have hh := hbound v q R B M hR hB hM hv hqm hqn hqb hqs hvc hvw (x-y) hx
  simpa only [v,add_sub_cancel,add_zero] using hh

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

lemma dyadicUniformEventBudget_mono {r p₀ p δ : ℝ}
    (hr : 0 < r) (h₀ : 0 < p₀) (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5+δ ≤
      dyadicUniformEventBudget r p₀ δ := by
  have hp' : 0 < p := h₀.trans_le hp
  have hlog : 0 ≤ Real.log (Real.exp 1/p) := by
    rw [eventLog_eq hp']
    linarith [Real.log_nonpos hp'.le hp1]
  have hh : Real.log (Real.exp 1/p) ≤ Real.log (Real.exp 1/p₀) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (Real.exp_pos 1).le h₀ hp
  unfold dyadicUniformEventBudget
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hh 5)
    (mul_nonneg observationFisherConstant_pos.le (Real.rpow_nonneg hr.le _))) le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FreshObservedSandwichBarrier
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
open scoped BigOperators ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma event_rawLaw_ae {N K : ℕ} (F G : fermionGraph N) (_ell : Fin K → ℝ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    {P : Configuration N → Prop} (hP : MeasurableSet {x | P x})
    (hA : MeasurableSet A)
    (h : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A → P z.1) :
    ∀ᵐ x ∂graphRawLaw G, P x := by
  rw [hlaw]
  apply Measure.ae_smul_measure _ c
  exact (ae_map_iff measurable_fst.aemeasurable hP).mpr ((ae_restrict_iff' hA).mpr h)

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

lemma localTFResponse_strict_mono {h H : ℝ} (hh : 0 ≤ h) (hH : h < H) :
    localTFResponse h < localTFResponse H := by
  have hT : 0 < (5/3:ℝ)*tfKinetic := mul_pos (by norm_num) tfKinetic_pos
  unfold localTFResponse
  rw [max_eq_left hh,max_eq_left (hh.trans hH.le)]
  exact Real.rpow_lt_rpow (div_nonneg hh hT.le) ((div_lt_div_iff_of_pos_right hT).mpr hH) (by norm_num)

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

end CoulombAtom

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OriginalFieldOscillationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_continuousOn_punctured {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) {0}ᶜ := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact norm_ne_zero_iff.mpr hx

lemma originalQueryField_punctured_poisson {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    PuncturedPoisson (originalQueryField F Z lam r j c₁ r₀ s z)
      (fun y => 4*Real.pi*originalQueryDensity F r j c₁ r₀ s z y) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  intro g hg hcg hsg
  have hg0 : g 0 = 0 := by
    by_contra hn0
    exact hsg (subset_tsupport g hn0) rfl
  have hiN := locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hiL : Integrable (fun x : Space => lam*Δ g x) :=
    (continuous_const.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
      (tfLaplacian_compact hg hcg).mul_left
  have hiP := locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
      (hρ z).2.2.1 (hρ z).2.2.2).continuous.locallyIntegrable
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hL := compact_laplacian_green (f := fun _ : Space => lam) contDiff_const hg hcg
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at hL
  change Integrable (fun x : Space => Z/‖x‖*Δ g x) at hiN
  have hiNL : Integrable (fun x : Space => Z/‖x‖*Δ g x-lam*Δ g x) := by
    exact (hiN.sub hiL).congr (ae_of_all _ (fun _ => rfl))
  simp only [originalQueryField,sub_mul]
  rw [integral_sub hiNL hiP,integral_sub hiN hiL,hL,
    show (∫ x, Z/‖x‖*Δ g x) = -(4*Real.pi*Z)*g 0 from
      nuclearField_weak_laplacian Z hg hcg,hg0,mul_zero,sub_zero,zero_sub,
    bounded_L1_weak_poisson (hρ z).1 (hρ z).2.1 hM (hρ z).2.2.1 (hρ z).2.2.2 hg hcg]
  simp only [mul_assoc,integral_const_mul]
  ring

theorem exists_original_field_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (y : Space) (R B M : ℝ), 0 < R → R < ‖y‖ → 0 ≤ B → 0 ≤ M →
      (∀ x ∈ ball y R, originalQueryDensity F r j c₁ r₀ s z x ≤ M) →
      (∀ x ∈ closedBall y R, originalQueryField F Z lam r j c₁ r₀ s z x ≤ B) →
      ∀ x : Space, ‖x-y‖ ≤ R/6 →
        |originalQueryField F Z lam r j c₁ r₀ s z x-
          originalQueryField F Z lam r j c₁ r₀ s z y| ≤
          C/R*‖x-y‖*(B+M*R^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_local_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z y R B M hR hRy hB hM hden hcap x hx
  obtain ⟨M₀,hM₀,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hsub : closedBall y R ⊆ ({0}ᶜ : Set Space) := by
    intro t ht ht0
    have he : t = 0 := ht0
    subst t
    have hh : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_left] using ht
    exact (not_le_of_gt hRy) hh
  apply hbound _ _ y R B M hR hB hM
    ((originalQueryField_continuousOn_punctured F Z lam r j hc hr₀ hs hrs z).mono hsub)
    (hρ z).1 (fun t _ => (hρ z).2.2.1 t) hden hcap
    (fun g hg hcg hsg => ?_) x hx
  have hh := originalQueryField_punctured_poisson F Z lam r j hc hr₀ hs hrs z g hg hcg
    (hsg.trans (ball_subset_closedBall.trans hsub))
  simpa only [mul_assoc,integral_const_mul] using hh

end CoulombAtom

end Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom

lemma norm_fourth_difference_le {r : ℝ} (_hr : 0 < r) {x y : Space}
    (hx : ‖x‖ ≤ 2*r) (hy : ‖y‖ ≤ 2*r) :
    |‖x‖^4-‖y‖^4| ≤ 32*r^3*‖x-y‖ := by
  have hp := abs_pow_sub_pow_le (a := ‖x‖) (b := ‖y‖) (n := 4)
  simp only [abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)] at hp
  calc
    _ ≤ |‖x‖-‖y‖| *4*(max ‖x‖ ‖y‖)^3 := by simpa only [Nat.cast_ofNat] using hp
    _ ≤ ‖x-y‖*4*(2*r)^3 := by
      gcongr
      · exact abs_norm_sub_norm_le x y
      · exact max_le hx hy
    _ = _ := by ring

lemma normalized_field_difference {φ : Space → ℝ} {x y : Space} {r A B M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hx : ‖x‖ ≤ 2*r) (hyl : r ≤ ‖y‖) (hy : ‖y‖ ≤ 2*r)
    (hcap : φ y ≤ B)
    (hosc : |φ x-φ y| ≤ A/r*‖x-y‖*(B+M*r^2+max (-φ y) 0)) :
    |‖x‖^4*φ x-‖y‖^4*φ y| ≤
      (16*A+32)/r*‖x-y‖*(r^4*B+r^6*M+max (-(‖y‖^4*φ y)) 0) := by
  let t : ℝ := max (-φ y) 0
  let V : ℝ := max (-(‖y‖^4*φ y)) 0
  let Q : ℝ := r^4*B+r^6*M+V
  have ht : 0 ≤ t := le_max_right _ _
  have hV : 0 ≤ V := le_max_right _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hneg : r^4*t ≤ V := by
    calc
      _ ≤ ‖y‖^4*t := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hyl 4) ht
      _ = V := by dsimp [t,V]; rw [mul_max_of_nonneg _ _ (pow_nonneg (norm_nonneg y) 4),mul_zero]; congr 1; ring
  have habs : |φ y| ≤ B+t := by
    apply abs_le.mpr
    have hh : -φ y ≤ t := le_max_left _ _
    constructor <;> linarith
  have hxp : ‖x‖^4 ≤ 16*r^4 := by
    calc
      _ ≤ (2*r)^4 := pow_le_pow_left₀ (norm_nonneg x) hx 4
      _ = _ := by ring
  have hfirst : ‖x‖^4*|φ x-φ y| ≤ (16*A)/r*‖x-y‖*Q := by
    calc
      _ ≤ (16*r^4)*(A/r*‖x-y‖*(B+M*r^2+t)) :=
        mul_le_mul hxp hosc (abs_nonneg _) (by positivity)
      _ = (16*A)/r*‖x-y‖*(r^4*B+r^6*M+r^4*t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  have hsecond : |‖x‖^4-‖y‖^4| *|φ y| ≤ 32/r*‖x-y‖*Q := by
    calc
      _ ≤ (32*r^3*‖x-y‖)*(B+t) :=
        mul_le_mul (norm_fourth_difference_le hr hx hy) habs (abs_nonneg _) (by positivity)
      _ = 32/r*‖x-y‖*(r^4*B+r^4*t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; nlinarith [mul_nonneg (pow_nonneg hr.le 6) hM]) (by positivity)
  calc
    _ = |‖x‖^4*(φ x-φ y)+(‖x‖^4-‖y‖^4)*φ y| := by congr 1; ring
    _ ≤ |‖x‖^4*(φ x-φ y)|+|(‖x‖^4-‖y‖^4)*φ y| := abs_add_le _ _
    _ = ‖x‖^4*|φ x-φ y|+|‖x‖^4-‖y‖^4| *|φ y| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg x) 4),abs_mul]
    _ ≤ (16*A)/r*‖x-y‖*Q+32/r*‖x-y‖*Q := add_le_add hfirst hsecond
    _ = _ := by dsimp [Q,V]; ring

end CoulombAnalysis

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
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier
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
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma OwnProbabilityTailTiltState.to_tailTiltState {N K : ℕ} {F : fermionGraph N}
    {Z lam r δ : ℝ} {p₀ p₁ : Fin (K+1) → ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    (hr : 0 < r) (h₁ : ∀ j, 0 < p₁ j) (h01 : ∀ j, p₀ j ≤ p₁ j) :
    TailTiltState Z lam r K p₁ δ F := by
  refine ⟨hF.1,hF.2.1,?_⟩
  intro j A hA hp
  obtain ⟨G,hGn,hGlaw,hGE⟩ := hF.2.2 j A hA ((h01 j).trans hp)
  refine ⟨G,hGn,hGlaw,hGE.trans ?_⟩
  let := graphRawLaw_probability F hF.1
  let := physicalObservationLaw_probability (K := K) (graphRawLaw F)
  exact dyadicUniformEventBudget_mono (by positivity) (h₁ j) hp (measureReal_le_one (s := A))

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
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSpatialNetBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSpatialNet_barrier_scope

open Set Metric
open scoped BigOperators

open CoulombAtom

lemma spatialGridIndex_close {h : ℝ} (hh : 0 < h) {x y : Space}
    (he : spatialGridIndex h x = spatialGridIndex h y) : ‖x-y‖ ≤ 3*h := by
  have hc (i : Fin 3) : |x i-y i| ≤ h := by
    have hi := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun he i)
    change |x i/h-y i/h| < 1 at hi
    rw [←sub_div,abs_div,abs_of_pos hh] at hi
    exact ((div_lt_one hh).mp hi).le
  have hs : ‖x-y‖^2 ≤ 3*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, h^2 := Finset.sum_le_sum (fun i _ => by
        change (x i-y i)^2 ≤ h^2
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i-y i)) hh.le).mpr (hc i))
      _ = _ := by simp
  nlinarith [norm_nonneg (x-y)]

lemma spatialGridIndex_bound {R h : ℝ} (hh : 0 < h)
    {x : Space} (hx : ‖x‖ ≤ R) (i : Fin 3) :
    spatialGridIndex h x i ∈ Finset.Icc (-(⌈R/h⌉₊+1 : ℕ):ℤ) (⌈R/h⌉₊+1 : ℕ) := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hi : |x i| ≤ R := hcoord.trans hx
  have hM : R/h < (⌈R/h⌉₊+1 : ℕ) := by
    have hh := Nat.le_ceil (R/h)
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  norm_num only [Nat.cast_add,Nat.cast_one] at hM
  simp only [Finset.mem_Icc,spatialGridIndex]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    have hxi := (abs_le.mp hi).1
    have hd : -R/h ≤ x i/h := div_le_div_of_nonneg_right hxi hh.le
    rw [neg_div] at hd
    linarith
  · apply Int.floor_le_iff.mpr
    push_cast
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (abs_le.mp hi).2 hh.le) (by linarith)

theorem exists_spatial_grid_net {A : Set Space} {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ Q : Finset Space, (∀ x ∈ Q, x ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ Q, ‖y-x‖ ≤ 3*h) ∧
      (Q.card:ℝ) ≤ (2*(R/h)+5)^3 := by
  classical
  let M : ℕ := ⌈R/h⌉₊+1
  let D : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(M:ℤ)) (M:ℤ))
  let E := D.filter (fun k => ∃ x ∈ A, spatialGridIndex h x = k)
  let f : (Fin 3 → ℤ) → Space := fun k => if hk : ∃ x ∈ A, spatialGridIndex h x = k then hk.choose else 0
  have hf {k : Fin 3 → ℤ} (hk : k ∈ E) : f k ∈ A ∧ spatialGridIndex h (f k) = k := by
    have he := (Finset.mem_filter.mp hk).2
    simpa only [f,dite_eq_left he] using he.choose_spec
  have hd {x : Space} (hx : x ∈ A) : spatialGridIndex h x ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,x,hx,rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact spatialGridIndex_bound hh (hA x hx) i
  refine ⟨E.image f,?_,?_,?_⟩
  · intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (hf hk).1
  · intro y hy
    refine ⟨f (spatialGridIndex h y),Finset.mem_image.mpr ⟨_,hd hy,rfl⟩,?_⟩
    apply spatialGridIndex_close hh
    exact (hf (hd hy)).2.symm
  · have hcard : (Finset.Icc (-(M:ℤ)) (M:ℤ)).card = 2*M+1 := by
      rw [Int.card_Icc]
      omega
    have hD : D.card = (2*M+1)^3 := by
      simp only [D,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have hM : (M:ℝ) ≤ R/h+2 := by
      have hm := Nat.ceil_lt_add_one (div_nonneg hR hh.le)
      dsimp [M]
      push_cast
      linarith
    calc
      _ ≤ (D.card:ℝ) := by exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le D _))
      _ = ((2*M+1:ℕ):ℝ)^3 := by rw [hD]; push_cast; rfl
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

end Work_BarrierSpatialNet_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialEventuallyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialEventually_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma tailPolynomialThreshold_pos {r : ℝ} (hr : 0 < r) {K : ℕ} (j : Fin (K+1)) :
    0 < tailPolynomialThreshold r j := by
  unfold tailPolynomialThreshold
  positivity

end Work_TailInitialEventually_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_inverse_cube_radius {c₁ r₀ s r : ℝ} (hc : 0 < c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    (masterWidth c₁ r₀ s y)⁻¹^3 ≤ c₁⁻¹^3*r^(-3-3*masterExponent) := by
  have hl := masterWidth_radius_lower (r₀ := r₀) hc.le hr hrs hy
  have hp : 0 < c₁*r^(1+masterExponent) := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hinv := inv_anti₀ hp hl
  have he : (c₁*r^(1+masterExponent))⁻¹^3 = c₁⁻¹^3*r^(-3-3*masterExponent) := by
    rw [mul_inv_rev,mul_pow,←Real.rpow_neg hr.le,←Real.rpow_mul_natCast hr.le]
    have hex : -(1+masterExponent)*(3:ℝ) = -3-3*masterExponent := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hex]
    ring
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (hp.le.trans hl)) hinv 3).trans_eq he

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualBandInverseBarrier
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
open scoped Topology BigOperators

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

lemma original_inverse_net_union_bound {N K : ℕ} {F : fermionGraph N}
    {Z lam r₀ s c₁ h xi : ℝ} {j : Fin K} (Q : Finset Space)
    (hQ : ∀ y ∈ Q, OriginalPointInverseBounds F Z lam r₀ s c₁ h xi j y) :
    (physicalObservationLaw (graphRawLaw F) K).real
      (⋃ y ∈ Q, originalLowFailure F Z lam r₀ s c₁ h xi j y ∪
        originalHighFailure F Z lam r₀ s c₁ h xi j y) ≤
      4*(Q.card:ℝ)*((2:ℝ)^j.val*r₀)^40 := by
  apply (measureReal_biUnion_finset_le Q _).trans
  calc
    _ ≤ ∑ _y ∈ Q, 4*((2:ℝ)^j.val*r₀)^40 := by
      apply Finset.sum_le_sum
      intro y hy
      apply (measureReal_union_le _ _).trans
      have hh := hQ y hy
      linarith only [hh.1,hh.2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

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
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TinyProbabilityFloorBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombBarrier

lemma tinyProbabilityFloor_le_polynomial {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 ≤ u) :
    tinyProbabilityFloor Z u ≤ min 1 (u^40) := by
  have hn : 0 ≤ min (1:ℝ) (u^80) := le_min (by norm_num) (pow_nonneg hu _)
  have hd : 1 ≤ 1+Z := by linarith
  apply (div_le_self hn hd).trans
  by_cases h : u ≤ 1
  · apply min_le_min_left 1
    have h40 := pow_le_one₀ hu h (n := 40)
    have hpow : u^80 = (u^40)^2 := by ring
    rw [hpow]
    nlinarith [pow_nonneg hu 40]
  · have h40 : 1 ≤ u^40 := one_le_pow₀ (by linarith)
    rw [min_eq_left h40]
    exact min_le_left _ _

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_InverseNetEventsBarrier
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
open scoped Topology BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

lemma originalQueryDensity_info_measurable {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryDensity F r j c₁ r₀ s z y) := by
  exact (jointMasterPosterior_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs
    canonicalRealPacket_smooth.continuous).comp (measurable_id.prodMk measurable_const)

lemma original_inverse_failure_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ h xi : ℝ) (j : Fin K) (y : Space)
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) :
    MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j]
      (originalLowFailure F Z lam r₀ s c₁ h xi j y ∪
        originalHighFailure F Z lam r₀ s c₁ h xi j y) := by
  have hf := originalQueryField_info_measurable (K := K) F Z lam r₀ j hc hr₀ hs y
  have hd := originalQueryDensity_info_measurable (K := K) F r₀ j hc hr₀ hs y
  exact ((measurableSet_le measurable_const hf).inter (measurableSet_le hd measurable_const)).union
    ((measurableSet_le hf measurable_const).inter (measurableSet_le measurable_const hd))

lemma original_inverse_height_net_union_bound {N K : ℕ} {F : fermionGraph N}
    {Z lam r₀ s c₁ xi : ℝ} {j : Fin K} (Q : Finset Space) (H : Finset ℝ)
    (hQ : ∀ h ∈ H, ∀ y ∈ Q, OriginalPointInverseBounds F Z lam r₀ s c₁ h xi j y) :
    (physicalObservationLaw (graphRawLaw F) K).real
      (⋃ h ∈ H, ⋃ y ∈ Q, originalLowFailure F Z lam r₀ s c₁ h xi j y ∪
        originalHighFailure F Z lam r₀ s c₁ h xi j y) ≤
      4*(H.card:ℝ)*(Q.card:ℝ)*((2:ℝ)^j.val*r₀)^40 := by
  apply (measureReal_biUnion_finset_le H _).trans
  calc
    _ ≤ ∑ _h ∈ H, 4*(Q.card:ℝ)*((2:ℝ)^j.val*r₀)^40 := by
      exact Finset.sum_le_sum (fun h hh => original_inverse_net_union_bound Q (hQ h hh))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma exists_inverse_band_spatial_net {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ Q : Finset Space,
      (∀ x ∈ Q, 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8) ∧
      (∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 →
        ∃ x ∈ Q, ‖x-y‖ ≤ u^2) ∧
      (Q.card:ℝ) ≤ 4913/u^3 := by
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_spatial_grid_net
    (A := {x : Space | 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8})
    (R := 2*u) (h := u^2/3) (by positivity) (by positivity)
    (fun _ hx => by linarith [hx.2])
  refine ⟨Q,hQ,?_,hcard.trans ?_⟩
  · intro y hyl hyh
    obtain ⟨x,hx,hxy⟩ := hcover y ⟨hyl,hyh⟩
    refine ⟨x,hx,?_⟩
    rw [norm_sub_rev] at hxy
    nlinarith
  · have hlin : 2*(2*u/(u^2/3))+5 ≤ 17/u := by
      apply (le_div_iff₀ hu).mpr
      field_simp
      nlinarith
    calc _ ≤ (17/u)^3 := pow_le_pow_left₀ (by positivity) hlin 3
         _ = _ := by ring

lemma divided_net_field_variation {a b alpha beta t : ℝ}
    (ht : 1 ≤ t) (ha : 0 ≤ alpha) (hv : |b-a| ≤ alpha+beta*max (-a) 0) :
    |b/t-a/t| ≤ alpha+beta*max (-(a/t)) 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hm : max (-(a/t)) 0 = max (-a) 0/t := by
    simpa only [neg_div,zero_div] using max_div_div_right ht0.le (-a) 0
  rw [←sub_div,abs_div,abs_of_pos ht0,hm]
  calc
    _ ≤ (alpha+beta*max (-a) 0)/t := div_le_div_of_nonneg_right hv ht0.le
    _ = alpha/t+beta*(max (-a) 0/t) := by ring
    _ ≤ _ := add_le_add (div_le_self ha ht) le_rfl

lemma localCellRadius_normalized {y : Space} (p : ℕ) (a : ℝ) :
    (localCellRadius y)^p*a = (‖y‖^p*a)/(100000:ℝ)^p := by
  simp only [localCellRadius,div_pow]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedAnnularCountBarrier
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
section Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma observedAnnularCount_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (a b : ℝ) :
    Measurable[observationInformation ell j] (observedAnnularCount (N := N) ell k a b) := by
  unfold observedAnnularCount rawAnnularCount
  exact observedStatistic_information_measurable ell k hk
    (g := fun x : Space => if a ≤ ‖x‖ ∧ ‖x‖ ≤ b then 1 else 0) (measurable_const.ite (measurableSet_le measurable_const measurable_norm |>.inter
    (measurableSet_le measurable_norm measurable_const)) measurable_const)

lemma observed_annular_count_le_raw {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (a b : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    observedAnnularCount ell k a b z ≤
      rawAnnularCount (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z.1 := by
  unfold observedAnnularCount rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_sub_norm_le (physicalObservedConfiguration ell k z i) (z.1 i)
    have ht' := norm_sub_norm_le (z.1 i) (physicalObservedConfiguration ell k z i)
    rw [norm_sub_rev] at ht'
    exact False.elim (hj ⟨by linarith [hd i,hi.1],by linarith [hd i,hi.2]⟩)
  · norm_num
  · exact le_rfl

lemma event_raw_annular_count_lower {N K : ℕ} (F G : fermionGraph N)
    (hGn : ‖fermionGraphValue N G‖^2 = 1) (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    (k : Fin K) (a b : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet A) (hcount : ∀ z ∈ A, T ≤ observedAnnularCount ell k a b z)
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A)) :
    T^2 ≤ rawAnnularMoment (graphFormVector G) (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) := by
  have he := event_rawLaw_ae F G ell hlaw
    (measurableSet_le measurable_const (rawAnnularCount_measurable _ _)) hA
    (by
      filter_upwards [physicalObservationLaw_ae_displacement (graphRawLaw F) ell hell] with z hz
      intro hzA
      exact (hcount z hzA).trans (observed_annular_count_le_raw ell k a b z (hz k)))
  let := graphRawLaw_probability G hGn
  rw [rawAnnularMoment_eq_integral (graphFormVector_sobolev G).sobolevVector,formRawLaw_graph]
  calc
    T^2 = ∫ _x : Configuration N, T^2 ∂graphRawLaw G := by simp
    _ ≤ ∫ x, rawAnnularCount (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) x^2 ∂graphRawLaw G :=
      integral_mono_ae (integrable_const _) (rawAnnularCount_sq_integrable _ _ _)
        (he.mono (fun x hx => pow_le_pow_left₀ hT hx 2))

end Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombBarrier CoulombObservation
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

section Work_AnnularMomentMonotone_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombBarrier

lemma rawAnnularCount_mono {N : ℕ} {a b A B : ℝ} (ha : A ≤ a) (hb : b ≤ B)
    (x : Configuration N) : rawAnnularCount a b x ≤ rawAnnularCount A B x := by
  unfold rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · exact False.elim (hj ⟨ha.trans hi.1,hi.2.trans hb⟩)
  · norm_num
  · exact le_rfl

lemma rawAnnularMoment_mono {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {a b A B : ℝ} (ha : A ≤ a) (hb : b ≤ B) :
    rawAnnularMoment ψ a b ≤ rawAnnularMoment ψ A B := by
  let := formRawLaw_finite hψ
  rw [rawAnnularMoment_eq_integral hψ,rawAnnularMoment_eq_integral hψ]
  exact integral_mono (rawAnnularCount_sq_integrable _ _ _) (rawAnnularCount_sq_integrable _ _ _)
    (fun x => pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ x) (rawAnnularCount_mono ha hb x) 2)

end Work_AnnularMomentMonotone_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem exists_tail_state_annular_count_constant {alpha beta : ℝ} (ha : 0 < alpha) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z lam r : ℝ}, 0 ≤ Z → 0 < lam → 0 < r →
      ∀ {N K : ℕ} {F : fermionGraph N} {p₀ : Fin (K+1) → ℝ} {δ : ℝ},
      TailTiltState Z lam r K p₀ δ F →
      ∀ (j : Fin (K+1)) (k : Fin K), j.val ≤ k.val →
      ∀ (u T : ℝ), 0 < u → 0 ≤ T →
      Real.sqrt 3*dyadicObservationWidth r k ≤ alpha*u/2 →
      Real.sqrt 3*dyadicObservationWidth r k ≤ beta*u →
      C*(annularOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) u)^2 < T^2 →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | T < observedAnnularCount (fun k : Fin K => dyadicObservationWidth r k) k
          (alpha*u) (beta*u) z}).toReal < p₀ j := by
  obtain ⟨C,hC,hbound⟩ := exists_priced_annular_count_constant (beta := 2*beta) (by linarith : 0 < alpha/2)
  refine ⟨C,hC,?_⟩
  intro Z lam r hZ hlam hr N K F p₀ δ hstate j k hk u T hu hT hnoiseA hnoiseB hlarge
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) := {z | T < observedAnnularCount ell k (alpha*u) (beta*u) z}
  have hA : MeasurableSet[observationInformation ell j] A := measurableSet_lt measurable_const
    (observedAnnularCount_information_measurable ell k hk _ _)
  by_contra! hn
  obtain ⟨G,hGn,hlaw,hD⟩ := hstate.2.2 j A hA hn
  have hlower := event_raw_annular_count_lower F G hGn ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k (alpha*u) (beta*u) hT ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hlaw
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have hmoment := rawAnnularMoment_mono hψ.sobolevFermion.sobolevVector
    (by dsimp only [ell]; linarith : alpha/2*u ≤ alpha*u-Real.sqrt 3*ell k)
    (by dsimp only [ell]; linarith : beta*u+Real.sqrt 3*ell k ≤ (2*beta)*u)
  have hD0 := le_trans (le_max_right (corePriceExcess Z lam (graphFormVector G)) 0) hD
  have hupper := hbound Z lam N (graphFormVector G) hψ.sobolevFermion hm hZ hlam
    (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) u hD0 hu hD
  exact (not_le_of_gt hlarge) (hlower.trans (hmoment.trans hupper))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularEventNumericsBarrier
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
section Work_AnnularEventNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma annularOffsetMass_rescale {D u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u^3*annularOffsetMass D u = 1+Real.sqrt (D*u^7) := by
  have hh : u^3 ≤ 1 := pow_le_one₀ hu.le hu1
  have hmax : max (1/u^3) 1 = 1/u^3 :=
    max_eq_left ((le_div_iff₀ (pow_pos hu 3)).mpr (by simpa using hh))
  unfold annularOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ hu.ne'),
    ←Real.sqrt_sq (by positivity : 0 ≤ u^3),←Real.sqrt_mul (sq_nonneg (u^3))]
  congr 2
  ring

lemma annularOffsetMass_tendsto {ι : Type*} {l : Filter ι} {u D : ι → ℝ}
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hD : Tendsto (fun i => D i*(u i)^7) l (𝓝 0)) :
    Tendsto (fun i => (u i)^3*annularOffsetMass (D i) (u i)) l (𝓝 1) := by
  have hh : Tendsto (fun i => 1+Real.sqrt (D i*(u i)^7)) l (𝓝 1) := by
    simpa using hD.sqrt.const_add 1
  apply hh.congr'
  filter_upwards [hu,hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
  exact (annularOffsetMass_rescale hi hi1.le).symm

lemma annular_count_margin_eventually {ι : Type*} {l : Filter ι} {u D : ι → ℝ}
    {C T : ℝ} (hCT : C < T^2)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hD : Tendsto (fun i => D i*(u i)^7) l (𝓝 0)) :
    ∀ᶠ i in l, C*(annularOffsetMass (D i) (u i))^2 < (T/(u i)^3)^2 := by
  have hm := annularOffsetMass_tendsto hu hu0 hD
  have hh := ((hm.pow 2).const_mul C).eventually_lt
    (tendsto_const_nhds (x := T^2)) (by simpa using hCT)
  filter_upwards [hu,hh] with i hui hi
  have hscale : (u i)^6*(T/(u i)^3)^2 = T^2 := by field_simp
  apply (mul_lt_mul_iff_right₀ (pow_pos hui 6)).mp
  rw [hscale]
  nlinarith only [hi]

lemma polynomial_annular_count_margin_eventually {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {C T δ : ℝ} (n : ℕ) (hCT : C < T^2)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0)) :
    ∀ᶠ i in l, C*(annularOffsetMass
      (dyadicUniformEventBudget (u i) ((u i)^n) δ) (u i))^2 < (T/(u i)^3)^2 := by
  apply annular_count_margin_eventually hCT hu hu0
  have hh := (polynomial_probability_budget_tendsto n (v := 7) (by norm_num) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu0,hu⟩)
  simpa only [Function.comp_def,Real.rpow_ofNat] using hh

lemma observation_annular_noise_eventually {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0)) :
    ∀ᶠ i in l, Real.sqrt 3*(u i)^(101/100:ℝ) ≤ a*(u i) := by
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ 1*(u i)^(101/100:ℝ) := by
    filter_upwards [hu] with i hi
    exact ⟨Real.rpow_nonneg hi.le _,by simp⟩
  have hh : Tendsto (fun i => Real.sqrt 3*((u i)^(101/100:ℝ)/(u i))) l (𝓝 0) := by
    simpa only [mul_zero] using
      (observation_relative_tendsto (E := 1) zero_le_one hu hu0 hell).const_mul (Real.sqrt 3)
  filter_upwards [hu,hh.eventually (gt_mem_nhds ha)] with i hui hi
  rw [←mul_div_assoc] at hi
  exact (div_le_iff₀ hui).mp hi.le

end Work_AnnularEventNumerics_barrier_scope

section Work_ActualAnnularGood_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem exists_actual_annular_good_constant {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ T : ℝ, 0 < T ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)}
      {j : ∀ i, Fin (K i)} {δ : ℝ},
      Tendsto s l (𝓝 0) →
      (∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        TailTiltState (Z i) (lam i) (r₀ i) (K i)
          (tailPolynomialThreshold (r₀ i)) δ (F i)) →
      ∀ᶠ i in l,
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/((2:ℝ)^(j i).val*r₀ i)^3 <
            observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
              (j i) (alpha*((2:ℝ)^(j i).val*r₀ i)) (beta*((2:ℝ)^(j i).val*r₀ i)) z} <
          ((2:ℝ)^(j i).val*r₀ i)^40 := by
  obtain ⟨C,hC,hcount⟩ := exists_tail_state_annular_count_constant (beta := beta) ha
  let T : ℝ := 2*C+1
  have hT : 0 < T := by dsimp [T]; linarith
  have hCT : C < T^2 := by dsimp [T]; nlinarith [sq_nonneg C]
  refine ⟨T,hT,?_⟩
  intro ι l r₀ s Z lam N K F j δ hs0 hband hstate
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hu : ∀ᶠ i in l, 0 < u i := by
    filter_upwards [hband] with i hi
    exact mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _) hi.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le)
    (hband.mono fun _ hi => hi.2) hs0
  have hlarge := polynomial_annular_count_margin_eventually (δ := δ) 40 hCT hu hu0
  have hnoiseA := observation_annular_noise_eventually (by linarith : 0 < alpha/2) hu hu0
  have hnoiseB := observation_annular_noise_eventually hb hu hu0
  filter_upwards [hband,hstate,hlarge,hnoiseA,hnoiseB,
    hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hi hFi hli hAi hBi hui1
  have hui : 0 < u i := mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _) hi.1
  have hp : tailPolynomialThreshold (r₀ i) (j i).castSucc = (u i)^40 := by
    unfold tailPolynomialThreshold
    exact min_eq_right (pow_le_one₀ hui.le hui1.le)
  have hell : dyadicObservationWidth (r₀ i) (j i) = (u i)^(101/100:ℝ) := by
    unfold dyadicObservationWidth u
    norm_num
  have hh := hcount hFi.1 hFi.2.1 hi.1 hFi.2.2
    (j i).castSucc (j i) (by rfl) (u i) (T/(u i)^3) hui (by positivity)
    (by rw [hell]; linarith only [hAi]) (by rw [hell]; exact hBi)
    (by simpa only [Fin.val_castSucc,hp] using hli)
  simpa only [Fin.val_castSucc,hp,Measure.real] using hh

end Work_ActualAnnularGood_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem exists_actual_uniform_annular_good_constant {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ T : ℝ, 0 < T ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/((2:ℝ)^j.val*r₀ i)^3 <
            observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
              j (alpha*((2:ℝ)^j.val*r₀ i)) (beta*((2:ℝ)^j.val*r₀ i)) z} <
          ((2:ℝ)^j.val*r₀ i)^40 := by
  obtain ⟨T,hT,hcount⟩ := exists_actual_annular_good_constant ha hb
  refine ⟨T,hT,?_⟩
  intro ι l r₀ s Z lam N K F δ hs0 hr₀ hstate
  have hpoly : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i)
        (tailPolynomialThreshold (r₀ i)) δ (F i) := by
    filter_upwards [hr₀,hstate] with i hri hi
    exact ⟨hi.1,hi.2.1,hi.2.2.to_tailTiltState hri (tailPolynomialThreshold_pos hri)
      (fun _ => tinyProbabilityFloor_le_polynomial hi.1 (by positivity))⟩
  let A : ι → Type := fun i => {j : Fin (K i) // (2:ℝ)^j.val*r₀ i ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb' : ∀ᶠ q in L, 0 < r₀ (π q) ∧ (2:ℝ)^q.2.1.val*r₀ (π q) ≤ s (π q) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := hcount (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1)
    (hs0.comp ht) hb' (ht.eventually hpoly)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j hj
  exact hi ⟨i,⟨j,hj⟩⟩ rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UniformObservationNoiseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UniformObservationNoise_barrier_scope

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombObservation

lemma uniform_observation_noise_eventually {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} {a : ℝ} (ha : 0 < a) (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ u : ℝ, 0 < u → u ≤ s i →
      Real.sqrt 3*u^(101/100:ℝ) ≤ a*u := by
  let A : ι → Type := fun i => {u : ℝ // 0 < u ∧ u ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  let u : (Σ i, A i) → ℝ := fun q => q.2.1
  have ht : Tendsto π L l := tendsto_comap
  have hu : ∀ᶠ q in L, 0 < u q := Eventually.of_forall (fun q => q.2.2.1)
  have hu0 : Tendsto u L (𝓝 0) := squeeze_zero
    (fun q => q.2.2.1.le) (fun q => q.2.2.2) (hs0.comp ht)
  have hh := observation_annular_noise_eventually ha hu hu0
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro v hv hvs
  exact hi ⟨i,⟨v,hv,hvs⟩⟩ rfl

end CoulombAtom

end Work_UniformObservationNoise_barrier_scope

section Work_ObservedPosteriorCount_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombBarrier CoulombObservation ProbabilityTheory

lemma raw_annular_count_le_observed {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (a b : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    rawAnnularCount a b z.1 ≤
      observedAnnularCount ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z := by
  unfold observedAnnularCount rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_sub_norm_le (physicalObservedConfiguration ell k z i) (z.1 i)
    have ht' := norm_sub_norm_le (z.1 i) (physicalObservedConfiguration ell k z i)
    rw [norm_sub_rev] at ht'
    exact False.elim (hj ⟨by linarith [hd i,hi.1],by linarith [hd i,hi.2]⟩)
  · norm_num
  · exact le_rfl

lemma observedAnnularCount_integrable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (k : Fin K) (a b : ℝ) :
    Integrable (observedAnnularCount ell k a b) (physicalObservationLaw μ K) := by
  have hm := (observedAnnularCount_information_measurable (N := N) ell k (j := 0) (Nat.zero_le _) a b).mono
    (observationInformation_le ell 0) le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable (N:ℝ)
  exact ae_of_all _ (fun z => by
    change ‖rawAnnularCount a b (physicalObservedConfiguration ell k z)‖ ≤ (N:ℝ)
    rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ _)]
    exact rawAnnularCount_le _ _ _)

lemma original_posterior_annular_count_le_observed {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) (j : ℕ) (k : Fin K)
    (hk : j ≤ k.val) (a b : ℝ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      (∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j (originalDatum ell j z)) ≤
        observedAnnularCount ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z := by
  let P := physicalObservationLaw μ K
  let f := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => rawAnnularCount a b z.1
  let g := observedAnnularCount (N := N) ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k)
  have hfi : Integrable f P := by
    apply Integrable.of_bound ((rawAnnularCount_measurable a b).comp measurable_fst).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun z => by
      change ‖rawAnnularCount a b z.1‖ ≤ (N:ℝ)
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b z.1)]
      exact rawAnnularCount_le a b z.1)
  have hgi : Integrable g P := observedAnnularCount_integrable μ ell k _ _
  have hfg : f ≤ᵐ[P] g := by
    filter_upwards [physicalObservationLaw_ae_displacement μ ell hell] with z hz
    exact raw_annular_count_le_observed ell k a b z (hz k)
  have hmono := condExp_mono (m := observationInformation ell j) hfi hgi hfg
  have hgmeas := observedAnnularCount_information_measurable (N := N) ell k hk
    (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k)
  rw [condExp_of_stronglyMeasurable (observationInformation_le ell j) hgmeas.stronglyMeasurable hgi] at hmono
  have he := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable (rawAnnularCount_measurable a b).stronglyMeasurable hfi
  simp only [originalDatum_comap] at he
  filter_upwards [hmono,he] with z hz hez
  exact hez ▸ hz

end CoulombAtom

end Work_ObservedPosteriorCount_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedPosteriorDensityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservedPosteriorDensity_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation

lemma master_density_count_scale {r : ℝ} (hr : 0 < r) (D T : ℝ) :
    D*r^(-3-3*masterExponent)*(T/r^3) = D*T*r^(-6-3*masterExponent) := by
  have he : T/r^3 = T*r^(-3:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]; rfl
  rw [he]
  calc
    _ = D*T*(r^(-3-3*masterExponent)*r^(-3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

end CoulombBarrier

end Work_ObservedPosteriorDensity_barrier_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom

lemma widthKernel_query_difference {t : Space → ℝ} (hp : ∀ x, 0 < t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) (x y z : Space) :
    ‖widthKernel t h x y-widthKernel t h x z‖ ≤
      (H:ℝ)*(t x)⁻¹^4*‖y-z‖ := by
  have hd := hh.dist_le_mul ((t x)⁻¹ • (y-x)) ((t x)⁻¹ • (z-x))
  have he : (y-x)-(z-x) = y-z := by abel
  simp only [dist_eq_norm,←smul_sub,he,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (hp x).le)] at hd
  unfold widthKernel
  rw [←mul_sub,norm_mul,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (hp x).le) _)]
  exact (mul_le_mul_of_nonneg_left hd (pow_nonneg (inv_nonneg.mpr (hp x).le) _)).trans_eq (by ring)

lemma widthKernel_ne_zero_width_lower {t : Space → ℝ}
    (ht : LipschitzWith (1/2) t) (hp : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : widthKernel t h x y ≠ 0) : t y/2 ≤ t x := by
  have ha := widthKernel_ne_zero_distance hp hs hx
  have hd := ht.dist_le_mul y x
  have hb : t y-t x ≤ (1/2:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,norm_sub_rev y x,NNReal.coe_div,
      NNReal.coe_one,NNReal.coe_ofNat] using (le_abs_self (t y-t x)).trans hd
  linarith [hp x]

end CoulombAtom

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombBarrier
open CoulombAtom
attribute [local irreducible] masterWidth masterKernel

lemma inverse_fourth_radius_scale {c r : ℝ} (_hc : 0 < c) (hr : 0 < r) :
    (c*r^(1+masterExponent)/2)⁻¹^4 =
      16*c⁻¹^4*r^(-4-4*masterExponent) := by
  rw [inv_div,div_eq_mul_inv,mul_inv_rev,mul_pow,mul_pow,←Real.rpow_neg hr.le,
    ←Real.rpow_mul_natCast hr.le]
  have he : -(1+masterExponent)*(4:ℝ) = -4-4*masterExponent := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  ring

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorAnnularQueryBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PosteriorAnnularQuery_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff

open CoulombAtom CoulombObservation
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma posterior_query_difference_le_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {a b C : ℝ} (y z : Space)
    (hbound : ∀ x, ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
      C*(if a ≤ ‖x‖ ∧ ‖x‖ ≤ b then 1 else 0))
    (d : OriginalDatum N K ell j) :
    ‖jointMasterPosterior μ ell j c₁ r₀ s g d y-
      jointMasterPosterior μ ell j c₁ r₀ s g d z‖ ≤
      C*∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j d := by
  let ν := originalRawKernel μ ell j d
  let f := fun (q : Space) (x : Configuration N) => ∑ i, masterKernel c₁ r₀ s g (x i) q
  have hfi (q) : Integrable (f q) ν := by
    have hm : Measurable (f q) := Finset.measurable_sum _ (fun i _ =>
      ((masterKernel_joint_continuous hc hr₀ hs hg).measurable.comp
        (f := fun x : Configuration N => (x i,q))
        ((measurable_pi_apply i).prodMk measurable_const)))
    obtain ⟨M,_hM,hM⟩ := masterConfigurationDensity_bound (N := N) hc hr₀ hs hrs hg hcg
    exact Integrable.of_bound hm.aestronglyMeasurable M (ae_of_all _ (fun x => hM x q))
  have hci : Integrable (rawAnnularCount a b) ν := by
    apply Integrable.of_bound (rawAnnularCount_measurable _ _).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ x)]
      exact rawAnnularCount_le _ _ x)
  have hb (x : Configuration N) : ‖f y x-f z x‖ ≤ C*rawAnnularCount a b x := by
    dsimp only [f]
    rw [←Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hbound (x i))).trans_eq
      (by rw [rawAnnularCount,Finset.mul_sum]))
  unfold jointMasterPosterior
  change ‖(∫ x, f y x ∂ν)-(∫ x, f z x ∂ν)‖ ≤ C*∫ x, rawAnnularCount a b x ∂ν
  rw [←integral_sub (hfi y) (hfi z),←integral_const_mul]
  exact norm_integral_le_of_norm_le (hci.const_mul C) (ae_of_all _ hb)

end Work_PosteriorAnnularQuery_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff

open CoulombAtom CoulombObservation

lemma master_query_count_scale {r : ℝ} (hr : 0 < r) (D T t : ℝ) :
    D*r^(-4-4*masterExponent)*t*(T/r^3) = D*T*r^(-7-4*masterExponent)*t := by
  have he : T/r^3 = T*r^(-3:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]; rfl
  rw [he]
  calc
    _ = D*T*(r^(-4-4*masterExponent)*r^(-3:ℝ))*t := by ring
    _ = _ := by
      rw [←Real.rpow_add hr,show (-4-4*masterExponent)+(-3:ℝ) = -7-4*masterExponent by ring]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_MasterExpandedAnnularQuery
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Set Metric
open scoped NNReal ContDiff
open CoulombAtom
attribute [local irreducible] masterWidth masterKernel

lemma masterWidth_relative_upper_half {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) {y : Space}
    (hy : r₀ ≤ 2*‖y‖) : masterWidth c₁ r₀ s y ≤ 2*c₁*‖y‖ := by
  have hd : masterBaseDistance r₀ y ≤ 2*‖y‖ :=
    max_le (by linarith [norm_nonneg y]) hy
  have hp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  calc
    _ ≤ c₁*masterBaseDistance r₀ y*s^masterExponent := masterWidth_upper hc hr₀ hs y
    _ ≤ c₁*masterBaseDistance r₀ y*1 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hc (le_max_of_le_left (norm_nonneg y)))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd hc]

lemma masterKernel_ne_zero_expanded_annular {g : Space → ℝ}
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ r₀ s r : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hs1 : s ≤ 1) (hrr : r₀ ≤ 2*r) {x y : Space} (hy : r ≤ ‖y‖)
    (hyB : ‖y‖ ≤ B*r) (hxy : masterKernel c₁ r₀ s g x y ≠ 0) :
    r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r := by
  have hr : 0 < r := by linarith
  rw [masterKernel_eq_widthKernel hc hr₀ hs g] at hxy
  have hm := widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
    (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y hxy
  simp only [mem_closedBall,dist_eq_norm] at hm
  have ht := masterWidth_relative_upper_half hc.le hr₀ hs hs1 (by linarith : r₀ ≤ 2*‖y‖)
  have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
  have hd : ‖x-y‖ ≤ ‖y‖/2 := by nlinarith [norm_nonneg y]
  have hl := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hl
  have hu := norm_sub_norm_le x y
  constructor
  · nlinarith only [hl,hd,hy]
  · calc
      ‖x‖ ≤ (3/2:ℝ)*‖y‖ := by linarith only [hu,hd]
      _ ≤ (3/2:ℝ)*(B*r) := mul_le_mul_of_nonneg_left hyB (by norm_num)
      _ ≤ 2*(B*r) := mul_le_mul_of_nonneg_right (by norm_num)
        (mul_nonneg (zero_le_one.trans hB) hr.le)
      _ = 2*B*r := by ring

 theorem exists_master_expanded_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ s r : ℝ}, 0 < r₀ → 0 < s → s ≤ 1 →
      r₀ ≤ 2*r → r ≤ s → ∀ x y z : Space,
      r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r then 1 else 0) := by
  have hcomp : HasCompactSupport (fun q => (g q)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      (masterProfile_support hgs)
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  refine ⟨(H:ℝ)*16*c₁⁻¹^4,by positivity,?_⟩
  intro r₀ s r hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2
  have hr : 0 < r := by linarith
  have hzero : ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ = 0 →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        ((H:ℝ)*16*c₁⁻¹^4)*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r then 1 else 0) := by
    intro he
    rw [he]
    split_ifs <;> positivity
  by_cases ha : masterKernel c₁ r₀ s g x y = 0 ∧ masterKernel c₁ r₀ s g x z = 0
  · exact hzero (by rw [ha.1,ha.2,sub_self,norm_zero])
  have hex : masterKernel c₁ r₀ s g x y ≠ 0 ∨ masterKernel c₁ r₀ s g x z ≠ 0 := by tauto
  have hax : r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r := hex.elim
    (fun h => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hy hy2 h)
    (fun h => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hz hz2 h)
  rw [ite_eq_left hax,mul_one]
  have hlow : c₁*r^(1+masterExponent)/2 ≤ masterWidth c₁ r₀ s x := by
    have haux (q : Space) (hq : r ≤ ‖q‖) (hxq : masterKernel c₁ r₀ s g x q ≠ 0) :
        c₁*r^(1+masterExponent)/2 ≤ masterWidth c₁ r₀ s x := by
      rw [masterKernel_eq_widthKernel hc hr₀ hs g] at hxq
      exact (div_le_div_of_nonneg_right (masterWidth_radius_lower hc.le hr hrs hq) (by norm_num)).trans
        (widthKernel_ne_zero_width_lower (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
          (masterWidth_pos hc hr₀ hs) (masterProfile_support hgs) hxq)
    exact hex.elim (haux y hy) (haux z hz)
  have hinv := pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr₀ hs x).le)
    (inv_anti₀ (by positivity : 0 < c₁*r^(1+masterExponent)/2) hlow) 4
  rw [inverse_fourth_radius_scale hc hr] at hinv
  rw [masterKernel_eq_widthKernel hc hr₀ hs g]
  exact (widthKernel_query_difference (masterWidth_pos hc hr₀ hs) hH x y z).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv H.coe_nonneg)
      (norm_nonneg _)).trans_eq (by ring))

end
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff
open CoulombAtom CoulombObservation
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma posterior_density_le_raw_annular_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ}
    (hg : Continuous g) (y : Space) {a b A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, masterKernel c₁ r₀ s g x y ≤ A)
    (hsupport : ∀ x, masterKernel c₁ r₀ s g x y ≠ 0 → a ≤ ‖x‖ ∧ ‖x‖ ≤ b)
    (d : OriginalDatum N K ell j) :
    jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
      A * ∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j d := by
  let f : Configuration N → ℝ := fun x => ∑ i, masterKernel c₁ r₀ s g (x i) y
  have hm : Measurable f := Finset.measurable_sum _ (fun i _ =>
    ((masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun x : Configuration N => (x i,y))
      ((measurable_pi_apply i).prodMk measurable_const)))
  have hn (x) : 0 ≤ f x := Finset.sum_nonneg fun i _ => masterKernel_nonneg _ _ _ _ _ _
  have hb (x) : f x ≤ A*rawAnnularCount a b x := by
    rw [rawAnnularCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simpa only [mul_one] using hbound (x i)
    · have hz : masterKernel c₁ r₀ s g (x i) y = 0 := by
        by_contra hh
        exact h (hsupport (x i) hh)
      simp only [hz,mul_zero,le_refl]
  have hfb (x) : ‖f x‖ ≤ A*N := by
    rw [Real.norm_of_nonneg (hn x)]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (rawAnnularCount_le a b x) hA)
  have hci : Integrable (rawAnnularCount a b) (originalRawKernel μ ell j d) := by
    apply Integrable.of_bound (rawAnnularCount_measurable a b).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b x)]; exact rawAnnularCount_le a b x)
  unfold jointMasterPosterior
  calc
    _ ≤ ∫ x, A*rawAnnularCount a b x ∂originalRawKernel μ ell j d :=
      integral_mono (Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hfb))
        (hci.const_mul _) hb
    _ = _ := integral_const_mul _ _

theorem exists_posterior_expanded_annular_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ 2*r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y : Space), r ≤ ‖y‖ → ‖y‖ ≤ B*r →
      jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
        D*r^(-3-3*masterExponent) *
          ∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨A,hAn,hA⟩ := masterKernel_amplitude hg hgs
  refine ⟨A*c₁⁻¹^3,by positivity,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hrr hrs d y hy hyB
  have hr : 0 < r := by linarith
  let D := A*c₁⁻¹^3*r^(-3-3*masterExponent)
  have hDn : 0 ≤ D := by dsimp only [D]; positivity
  have hb (x) : masterKernel c₁ r₀ s g x y ≤ D :=
    (hA hc hcL hr₀ hs hs1 x y).trans (by
      simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_left
        (masterWidth_inverse_cube_radius (r₀ := r₀) hc hr hrs hy) hAn)
  exact posterior_density_le_raw_annular_count μ ell j hc hr₀ hs hg y hDn hb
    (fun x hx => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hy hyB hx) d

 theorem exists_posterior_expanded_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y z : Space),
      r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
      ‖jointMasterPosterior μ ell j c₁ r₀ s g d y-
        jointMasterPosterior μ ell j c₁ r₀ s g d z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          ∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨C,hC,hbound⟩ := exists_master_expanded_annular_query_constant hg hgs hB hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hr₀s hrr hrs d y z hy hy2 hz hz2
  have hcg : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      ((subset_tsupport g).trans (hgs.trans ball_subset_closedBall))
  exact posterior_query_difference_le_count μ ell j hc hr₀ hs hr₀s hg.continuous hcg
    y z (fun x => hbound hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2) d

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedExpandedAnnular
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff
open CoulombAtom CoulombObservation

lemma original_posterior_expanded_count_band_bound {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) (j : ℕ) (k : Fin K)
    (hk : j ≤ k.val) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hnoise : Real.sqrt 3*ell k ≤ r/4) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      (∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j (originalDatum ell j z)) ≤
        observedAnnularCount ell k (r/4) (3*B*r) z := by
  filter_upwards [original_posterior_annular_count_le_observed μ ell hell j k hk (r/2) (2*B*r)] with z hz
  apply hz.trans
  exact rawAnnularCount_mono (by linarith) (by nlinarith) _

 theorem exists_observed_posterior_expanded_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ z ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (3*B*r) z ≤ T/r^3 →
        ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ B*r →
          jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y ≤
            D*T*r^(-6-3*masterExponent) := by
  obtain ⟨D,hD,hbound⟩ := exists_posterior_expanded_annular_density_constant hg hgs hB hc hcL
  refine ⟨D,hD,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hr₀s hrr hrs hnoise
  have hr : 0 < r := by linarith
  filter_upwards [original_posterior_expanded_count_band_bound μ ell hell j k hk hB hr hnoise] with z hz
  intro hcount y hy hy2
  exact (hbound μ ell j hr₀ hs hs1 hrr hrs _ y hy hy2).trans
    ((mul_le_mul_of_nonneg_left (hz.trans hcount) (by positivity)).trans_eq
      (master_density_count_scale hr D T))

 theorem exists_observed_posterior_expanded_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ q ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (3*B*r) q ≤ T/r^3 →
        ∀ y z : Space, r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
          ‖jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) y-
            jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) z‖ ≤
            C*T*r^(-7-4*masterExponent)*‖y-z‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_posterior_expanded_annular_query_constant hg hgs hB hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hr₀s hrr hrs hnoise
  have hr : 0 < r := by linarith
  filter_upwards [original_posterior_expanded_count_band_bound μ ell hell j k hk hB hr hnoise] with q hq
  intro hcount y z hy hy2 hz hz2
  exact (hbound μ ell j hr₀ hs hs1 hr₀s hrr hrs _ y z hy hy2 hz hz2).trans
    ((mul_le_mul_of_nonneg_left (hq.trans hcount) (by positivity)).trans_eq
      (master_query_count_scale hr C T ‖y-z‖))

end CoulombBarrier

open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma rpow_half_scale {u : ℝ} (hu : 0 ≤ u) (e : ℝ) :
    (u/2)^e = (1/2:ℝ)^e*u^e := by
  rw [show u/2 = (1/2:ℝ)*u by ring, Real.mul_rpow (by norm_num) hu]

 theorem exists_actual_expanded_conditional_regularity_constants {B c₁ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ T D L : ℝ, 0 < T ∧ 0 ≤ D ∧ 0 ≤ L ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let count := observedAnnularCount
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (3*B*u)
        Measurable[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] count ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/u^3 < count z} < u^40 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i),
          count q ≤ T/u^3 →
            (∀ y : Space, u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u →
              originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                D*u^(-6-3*masterExponent)) ∧
            (∀ y z : Space, u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u → u/2 ≤ ‖z‖ → ‖z‖ ≤ B*u →
              ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤
                L*u^(-7-4*masterExponent)*‖y-z‖) := by
  obtain ⟨T,hT,hcount⟩ := exists_actual_uniform_annular_good_constant
    (by norm_num : (0:ℝ) < 1/8) (by linarith : (0:ℝ) < 3*B)
  obtain ⟨D,hD,hdensity⟩ := exists_observed_posterior_expanded_density_constant
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support (by linarith : 1 ≤ 2*B) hc hcL
  obtain ⟨L,hL,hquery⟩ := exists_observed_posterior_expanded_query_constant
    canonicalRealPacket_smooth canonicalRealPacket_support (by linarith : 1 ≤ 2*B) hc hcL
  refine ⟨T,D*T*(1/2:ℝ)^(-6-3*masterExponent),L*T*(1/2:ℝ)^(-7-4*masterExponent),
    hT,by positivity,by positivity,?_⟩
  intro ι l r₀ s Z lam N K F δ hs0 hr₀ hstate
  have hn := uniform_observation_noise_eventually (by norm_num : (0:ℝ) < 1/8) hs0
  filter_upwards [hcount hs0 hr₀ hstate,hr₀,hn,
    hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hci hri hni hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hs : 0 < s i := hu.trans_le hjs
  have hnoise : Real.sqrt 3*dyadicObservationWidth (r₀ i) j ≤ (u/2)/4 := by
    have hh := hni u hu hjs
    simpa only [dyadicObservationWidth,u,show (1.01:ℝ) = 101/100 by norm_num,
      one_div_mul_eq_div,div_div,show (2:ℝ)*4 = 8 by norm_num] using hh
  have hr₀s := hru.trans hjs
  have hrr : r₀ i ≤ 2*(u/2) := by linarith
  have hrs : u/2 ≤ s i := by linarith
  have henn : 0 ≤ u/2 := by positivity
  have hshape : (u/2)/4 = u/8 := by ring
  have hshape' : 3*(2*B)*(u/2) = 3*B*u := by ring
  have hshape'' : (2*B)*(u/2) = B*u := by ring
  refine ⟨observedAnnularCount_information_measurable _ j le_rfl _ _,?_,?_⟩
  · simpa only [one_div_mul_eq_div] using hci j hjs
  · filter_upwards [hdensity (graphRawLaw (F i)) _ (fun k => (dyadicObservationWidth_pos hri k).le)
      j j le_rfl hri hs hsi.le hr₀s hrr hrs hnoise,
      hquery (graphRawLaw (F i)) _ (fun k => (dyadicObservationWidth_pos hri k).le)
      j j le_rfl hri hs hsi.le hr₀s hrr hrs hnoise] with q hd hq
    intro hcut
    have hcut' : observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
        j ((u/2)/4) (3*(2*B)*(u/2)) q ≤ T/(u/2)^3 := by
      rw [hshape,hshape']
      exact hcut.trans (div_le_div_of_nonneg_left hT.le (by positivity)
        (pow_le_pow_left₀ henn (by linarith : u/2 ≤ u) 3))
    have hd' := hd hcut'
    have hq' := hq hcut'
    rw [hshape''] at hd' hq'
    constructor
    · intro y hyl hyh
      simpa only [rpow_half_scale hu.le,mul_assoc,u,originalQueryDensity] using hd' y hyl hyh
    · intro y z hyl hyh hzl hzh
      simpa only [rpow_half_scale hu.le,mul_assoc,u,originalQueryDensity] using hq' y z hyl hyh hzl hzh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CapInformationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CapInformation_barrier_scope

open MeasureTheory Set

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_capBandStatistic_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    (u C : ℝ) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z)) := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  have hm := jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  have hf : Measurable (fun p : OriginalDatum N K ell j × Space =>
      Z/‖p.2‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket p.1) p.2) :=
    ((measurable_const.div measurable_snd.norm).sub measurable_const).sub
      (potential_joint_measurable hm)
  exact (((hf.const_mul _).sub measurable_const).max measurable_const).stronglyMeasurable.integral_prod_right'.measurable.const_mul _

end CoulombAtom

end Work_CapInformation_barrier_scope

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom CoulombBarrier

lemma norm_sixth_difference_le {r : ℝ} (_hr : 0 < r) {x y : Space}
    (hx : ‖x‖ ≤ 2*r) (hy : ‖y‖ ≤ 2*r) :
    |‖x‖^6-‖y‖^6| ≤ 192*r^5*‖x-y‖ := by
  have hp := abs_pow_sub_pow_le (a := ‖x‖) (b := ‖y‖) (n := 6)
  simp only [abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)] at hp
  calc
    _ ≤ |‖x‖-‖y‖| *6*(max ‖x‖ ‖y‖)^5 := by simpa only [Nat.cast_ofNat] using hp
    _ ≤ ‖x-y‖*6*(2*r)^5 := by
      gcongr
      · exact abs_norm_sub_norm_le x y
      · exact max_le hx hy
    _ = _ := by ring

lemma normalized_density_net_variation {ρ : Space → ℝ} {x y : Space} {u D L w : ℝ}
    (hu : 0 < u) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hx : ‖x‖ ≤ 2*u) (hy : ‖y‖ ≤ 2*u) (hxy : ‖x-y‖ ≤ u^2)
    (hn : 0 ≤ ρ y) (hden : ρ y ≤ D*u^(-6-3*w))
    (hq : ‖ρ x-ρ y‖ ≤ L*u^(-7-4*w)*‖x-y‖) :
    |‖x‖^6*ρ x-‖y‖^6*ρ y| ≤ 64*L*u^(1-4*w)+192*D*u^(1-3*w) := by
  have hxp : ‖x‖^6 ≤ 64*u^6 := by
    calc _ ≤ (2*u)^6 := pow_le_pow_left₀ (norm_nonneg x) hx 6
         _ = _ := by ring
  have heq (n : ℕ) (v : ℝ) : u^n*u^v = u^((n:ℝ)+v) := by
    rw [←Real.rpow_natCast,Real.rpow_add hu]
  have hp₁ : u^6*u^(-7-4*w)*u^2 = u^(1-4*w) := by
    rw [mul_right_comm,←pow_add,heq]
    congr 1
    norm_num
    ring
  have hp₂ : u^5*u^2*u^(-6-3*w) = u^(1-3*w) := by
    rw [←pow_add,heq]
    congr 1
    norm_num
    ring
  have hfirst : ‖x‖^6*|ρ x-ρ y| ≤ 64*L*u^(1-4*w) := by
    calc
      _ ≤ (64*u^6)*(L*u^(-7-4*w)*‖x-y‖) :=
        mul_le_mul hxp (by simpa only [Real.norm_eq_abs] using hq) (abs_nonneg _) (by positivity)
      _ ≤ (64*u^6)*(L*u^(-7-4*w)*u^2) := by gcongr
      _ = 64*L*(u^6*u^(-7-4*w)*u^2) := by ring
      _ = _ := by rw [hp₁]
  have hsecond : |‖x‖^6-‖y‖^6| *|ρ y| ≤ 192*D*u^(1-3*w) := by
    rw [abs_of_nonneg hn]
    calc
      _ ≤ (192*u^5*‖x-y‖)*(D*u^(-6-3*w)) :=
        mul_le_mul (norm_sixth_difference_le hu hx hy) hden hn (by positivity)
      _ ≤ (192*u^5*u^2)*(D*u^(-6-3*w)) := by gcongr
      _ = 192*D*(u^5*u^2*u^(-6-3*w)) := by ring
      _ = _ := by rw [hp₂]
  calc
    _ = |‖x‖^6*(ρ x-ρ y)+(‖x‖^6-‖y‖^6)*ρ y| := by congr 1; ring
    _ ≤ |‖x‖^6*(ρ x-ρ y)|+|(‖x‖^6-‖y‖^6)*ρ y| := abs_add_le _ _
    _ = ‖x‖^6*|ρ x-ρ y|+|‖x‖^6-‖y‖^6| *|ρ y| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg x) 6),abs_mul]
    _ ≤ _ := add_le_add hfirst hsecond

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OriginalAnnularOscillationBarrier
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

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma inner_cap_ball_subset {u : ℝ} (hu : 0 < u) {y : Space}
    (hyl : 11*u/8 ≤ ‖y‖) (hyh : ‖y‖ ≤ 13*u/8) :
    closedBall y (u/16) ⊆ closedAnnularShell (5*u/4) (7*u/4) := by
  intro t ht
  have hd : ‖t-y‖ ≤ u/16 := by simpa only [mem_closedBall,dist_eq_norm] using ht
  have hupper := norm_sub_le t y
  have hlow : ‖y‖ ≤ ‖t-y‖+‖t‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_sub_add y t
  have hhigh : ‖t‖ ≤ ‖t-y‖+‖y‖ := norm_le_norm_sub_add t y
  constructor <;> linarith

theorem exists_original_annular_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u B M : ℝ), 0 < u → 0 ≤ B → 0 ≤ M →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ M) →
      (∀ t : Space, 5*u/4 ≤ ‖t‖ → ‖t‖ ≤ 7*u/4 →
        originalQueryField F Z lam r j c₁ r₀ s z t ≤ B) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u/96 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        C/u*‖x-y‖*(u^4*B+u^6*M+
          max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_original_field_oscillation_constant
  refine ⟨256*C+32,by positivity,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u B M hu hB hM hden hcap y x hyl hyh hx
  have hball := inner_cap_ball_subset hu hyl hyh
  have hyl' : u ≤ ‖y‖ := by linarith
  have hyh' : ‖y‖ ≤ 2*u := by linarith
  have hxh : ‖x‖ ≤ 2*u := by
    have ht := norm_le_norm_sub_add x y
    linarith
  have hf := hbound F Z lam r j hc hr₀ hs hrs z y (u/16) B M (by positivity)
    (by linarith) hB hM (fun t ht => ?_) (fun t ht => ?_) x (by linarith)
  · have hφ : originalQueryField F Z lam r j c₁ r₀ s z y ≤ B := hcap y (by linarith) (by linarith)
    have hosc : |originalQueryField F Z lam r j c₁ r₀ s z x-
        originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        (16*C)/u*‖x-y‖*(B+M*u^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by
      apply hf.trans
      have hsq : M*(u/16)^2 ≤ M*u^2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg u]) hM
      calc
        _ = (16*C)/u*‖x-y‖*(B+M*(u/16)^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hh := normalized_field_difference hu (by positivity : 0 ≤ 16*C) hB hM hxh hyl' hyh' hφ hosc
    convert hh using 1 <;> first | rfl | ring
  · have ht' := hball (ball_subset_closedBall ht)
    exact hden t (by linarith [ht'.1]) (by linarith [ht'.2])
  · have ht' := hball ht
    exact hcap t ht'.1 ht'.2

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_capStatistic_unscaled {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    (hstat : capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      originalQueryField F Z lam r j c₁ r₀ s z y ≤ 16*(C+1)/(u/100000)^4 := by
  intro y hyl hyh
  have hh := original_capBandStatistic_controls_field F Z lam r j hc hr₀ hs hrs z
    hu hC hstat y hyl hyh
  by_cases hf : originalQueryField F Z lam r j c₁ r₀ s z y ≤ 0
  · exact hf.trans (by positivity)
  · have hr : u/100000 ≤ localCellRadius y := by dsimp only [localCellRadius]; linarith
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 4) (le_of_not_ge hf)
    apply (le_div_iff₀ (by positivity : 0 < (u/100000)^4)).mpr
    simpa only [mul_comm] using hp.trans hh

lemma normalized_density_power {u D w : ℝ} (hu : 0 < u) :
    u^6*(D*u^(-6-3*w)) = D*u^(-3*w) := by
  rw [mul_left_comm]
  congr 1
  rw [← Real.rpow_natCast u 6, ← Real.rpow_add hu]
  congr 1
  ring

theorem exists_original_scaled_oscillation_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u C D : ℝ), 0 < u → 0 ≤ C → 0 ≤ D →
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1 →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ D*u^(-6-3*masterExponent)) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u/96 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        A/u*‖x-y‖*(16*(C+1)*100000^4+D*u^(-3*masterExponent)+
          max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0) := by
  obtain ⟨A,hA,hbound⟩ := exists_original_annular_oscillation_constant
  refine ⟨A,hA,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u C D hu hC hD hstat hden y x hyl hyh hxy
  have hh := hbound F Z lam r j hc hr₀ hs hrs z u (16*(C+1)/(u/100000)^4)
    (D*u^(-6-3*masterExponent)) hu (by positivity) (by positivity) hden
    (original_capStatistic_unscaled F Z lam r j hc hr₀ hs hrs z hu hC hstat) y x hyl hyh hxy
  have hp : u^4*(16*(C+1)/(u/100000)^4) = 16*(C+1)*100000^4 := by
    field_simp
  simpa only [hp,normalized_density_power hu] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_NetFieldVariationBarrier
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
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma net_oscillation_scale {u d A E D V w : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hw : 0 ≤ w) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hV : 0 ≤ V) (hd : d ≤ u^2) :
    A/u*d*(E+D*u^(-3*w)+V) ≤ A*(E+D)*u^(1-3*w)+A*u*V := by
  have hp : 1 ≤ u^(-3*w) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have hEp : E ≤ E*u^(-3*w) := by simpa using mul_le_mul_of_nonneg_left hp hE
  have heq : u*u^(-3*w) = u^(1-3*w) := by
    rw [sub_eq_add_neg,Real.rpow_add hu,Real.rpow_one]
    simp only [neg_mul]
  calc
    _ ≤ A/u*u^2*(E+D*u^(-3*w)+V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
    _ = A*u*(E+D*u^(-3*w)+V) := by field_simp
    _ ≤ A*u*((E+D)*u^(-3*w)+V) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hEp]) (by positivity)
    _ = A*(E+D)*(u*u^(-3*w))+A*u*V := by ring
    _ = _ := by rw [heq]

theorem exists_original_net_field_variation_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u C D : ℝ), 0 < u → u ≤ 1/96 → 0 ≤ C → 0 ≤ D →
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1 →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ D*u^(-6-3*masterExponent)) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u^2 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        A*(16*(C+1)*100000^4+D)*u^(1-3*masterExponent)+
          A*u*max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0 := by
  obtain ⟨A,hA,hbound⟩ := exists_original_scaled_oscillation_constant
  refine ⟨A,hA,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u C D hu hu96 hC hD hstat hden y x hyl hyh hxy
  have hdist : ‖x-y‖ ≤ u/96 := hxy.trans (by nlinarith)
  exact (hbound F Z lam r j hc hr₀ hs hrs z u C D hu hC hD hstat hden y x hyl hyh hdist).trans
    (net_oscillation_scale hu (by linarith) (by norm_num [masterExponent]) hA.le
      (by positivity) hD (le_max_right _ _) hxy)

lemma net_field_high_transfer {a b h xi α β : ℝ}
    (_hxi : 0 ≤ xi) (hh : xi ≤ h) (hα : α ≤ xi/4) (hβ : β ≤ 1)
    (hov : |b-a| ≤ α+β*max (-a) 0) (ha : a ≤ h-xi) :
    b ≤ h-3*xi/4 := by
  have hb := (abs_le.mp hov).2
  by_cases hn : 0 ≤ a
  · rw [max_eq_right (by linarith : -a ≤ 0),mul_zero,add_zero] at hb
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -a)] at hb
    have hp : β*(-a) ≤ -a := by simpa using mul_le_mul_of_nonneg_right hβ (by linarith : 0 ≤ -a)
    linarith

lemma net_field_low_transfer {a b h xi α β : ℝ}
    (hxi : 0 ≤ xi) (hh : 0 ≤ h) (hα : α ≤ xi/4)
    (hov : |b-a| ≤ α+β*max (-a) 0) (ha : h+xi ≤ a) :
    h+3*xi/4 ≤ b := by
  rw [max_eq_right (by linarith : -a ≤ 0),mul_zero,add_zero] at hov
  have hb := (abs_le.mp hov).1
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseNetPropagationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    localTFResponse a ≤ localTFResponse b := by
  rcases hab.eq_or_lt with h | h
  · exact congrArg localTFResponse h |>.le
  · exact (localTFResponse_strict_mono ha h).le

theorem exists_inverse_height_net {lo hi xi : ℝ}
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ H : Finset ℝ, (∀ k ∈ H, lo/2 ≤ k ∧ k ≤ 2*hi) ∧
      ∀ h ∈ Icc lo hi,
        (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
        (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4) := by
  classical
  obtain ⟨S,hS,hfin,hcover⟩ := isCompact_Icc.finite_cover_balls
    (s := Icc (lo/2) (2*hi)) (show 0 < xi/16 by positivity)
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro k hk
    exact hS (hfin.mem_toFinset.mp hk)
  · intro h hh
    have hlo' : h-3*xi/16 ∈ Icc (lo/2) (2*hi) := by
      constructor <;> linarith [hh.1,hh.2]
    have hhi' : h+3*xi/16 ∈ Icc (lo/2) (2*hi) := by
      constructor <;> linarith [hh.1,hh.2]
    have extract (t : ℝ) (ht : t ∈ Icc (lo/2) (2*hi)) :
        ∃ k ∈ hfin.toFinset, |t-k| < xi/16 := by
      obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover ht)
      obtain ⟨hk,hball⟩ := mem_iUnion.mp hk
      refine ⟨k,hfin.mem_toFinset.mpr hk,?_⟩
      simpa only [Metric.mem_ball,Real.dist_eq] using hball
    obtain ⟨kl,hkl,hl⟩ := extract _ hlo'
    obtain ⟨kh,hkh,hh'⟩ := extract _ hhi'
    have hl' := abs_lt.mp hl
    have hh'' := abs_lt.mp hh'
    exact ⟨⟨kl,hkl,by linarith,by linarith⟩,⟨kh,hkh,by linarith,by linarith⟩⟩

theorem exists_uniform_inverse_density_margin {lo hi xi : ℝ}
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ h ∈ Icc lo hi,
      localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8) := by
  let g : ℝ → ℝ := fun h => min
    (localTFResponse h-localTFResponse (h-xi/8))
    (localTFResponse (h+xi/8)-localTFResponse h)
  have hg : Continuous g :=
    (localTFResponse_continuous.sub
      (localTFResponse_continuous.comp (continuous_id.sub continuous_const))).min
      ((localTFResponse_continuous.comp (continuous_id.add continuous_const)).sub
        localTFResponse_continuous)
  obtain ⟨h,hh,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlh) hg.continuousOn
  have hgpos : 0 < g h := by
    apply lt_min
    · exact sub_pos.mpr (localTFResponse_strict_mono (by linarith [hh.1]) (by linarith))
    · exact sub_pos.mpr (localTFResponse_strict_mono (by linarith [hh.1]) (by linarith))
  refine ⟨g h,hgpos,?_⟩
  intro t ht
  have hm : g h ≤ g t := hmin ht
  have h1 := hm.trans (min_le_left _ _)
  have h2 := hm.trans (min_le_right _ _)
  exact ⟨by linarith,by linarith⟩

theorem inverse_net_propagation {X : Type*} {B : Set X} {Q : Finset X}
    {H : Finset ℝ} {v rho : X → ℝ} {lo hi xi eta alpha beta : ℝ}
    (hxi : 0 < xi) (hlo : 16*xi < lo)
    (halpha : alpha ≤ xi/4) (hbeta : beta ≤ 1)
    (hmargin : ∀ h ∈ Icc lo hi,
      localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8))
    (hheight : ∀ h ∈ Icc lo hi,
      (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
      (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4))
    (hnet : ∀ y ∈ B, ∃ x ∈ Q,
      |v x-v y| ≤ alpha+beta*max (-v y) 0 ∧ |rho x-rho y| ≤ eta)
    (hgood : ∀ x ∈ Q, ∀ k ∈ H,
      ¬(v x ≤ k-xi/4 ∧ localTFResponse k ≤ rho x) ∧
      ¬(k+xi/4 ≤ v x ∧ rho x ≤ localTFResponse k)) :
    ∀ y ∈ B, ∀ h ∈ Icc lo hi,
      (localTFResponse h < rho y → h-xi ≤ v y) ∧
      (rho y < localTFResponse h → v y ≤ h+xi) := by
  intro y hy h hh
  obtain ⟨x,hx,hv,hr⟩ := hnet y hy
  have hr' := abs_le.mp hr
  constructor
  · intro hhigh
    by_contra hn
    have hvy : v y ≤ h-xi := (lt_of_not_ge hn).le
    have hvx : v x ≤ h-3*xi/4 :=
      net_field_high_transfer hxi.le (by linarith [hh.1]) halpha hbeta hv hvy
    obtain ⟨k,hk,hkl,hkh⟩ := (hheight h hh).1
    have hk0 : 0 ≤ k := by linarith [hh.1]
    have hkresp := localTFResponse_mono_nonneg hk0 hkh
    have hgap := (hmargin h hh).1
    apply (hgood x hx k hk).1
    exact ⟨by linarith,by linarith⟩
  · intro hlow
    by_contra hn
    have hvy : h+xi ≤ v y := (lt_of_not_ge hn).le
    have hvx : h+3*xi/4 ≤ v x :=
      net_field_low_transfer hxi.le (by linarith [hh.1]) halpha hv hvy
    obtain ⟨k,hk,hkl,hkh⟩ := (hheight h hh).2
    have hh0 : 0 ≤ h+xi/8 := by linarith [hh.1]
    have hkresp := localTFResponse_mono_nonneg hh0 hkl
    have hgap := (hmargin h hh).2
    apply (hgood x hx k hk).2
    exact ⟨by linarith,by linarith⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_UniformNetErrorsBarrier
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
section Work_UniformNetErrors_barrier_scope

open Filter
open scoped Topology

lemma uniform_power_error_eventually {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} {a C eps : ℝ} (ha : 0 < a) (heps : 0 < eps)
    (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ u : ℝ, 0 < u → u ≤ s i → C*u^a ≤ eps := by
  let A : ι → Type := fun i => {u : ℝ // 0 < u ∧ u ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  let u : (Σ i, A i) → ℝ := fun q => q.2.1
  have ht : Tendsto π L l := tendsto_comap
  have hu0 : Tendsto u L (𝓝 0) := squeeze_zero
    (fun q => q.2.2.1.le) (fun q => q.2.2.2) (hs0.comp ht)
  have hp : Tendsto (fun q => C*u q^a) L (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne',mul_zero] using (tendsto_const_nhds (x := C)).mul (hu0.rpow_const (Or.inr ha.le))
  have he := Filter.eventually_comap.mp (hp.eventually (gt_mem_nhds heps))
  filter_upwards [he] with i hi
  intro v hv hvs
  exact (hi ⟨i,⟨v,hv,hvs⟩⟩ rfl).le

end Work_UniformNetErrors_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem original_spatial_inverse_propagation {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ : ℝ) (j : Fin K) (q : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u lo hi xi eta D L A : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hxi : 0 < xi) (hlo : 16*xi < lo) (hD : 0 ≤ D) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (H : Finset ℝ) (Q : Finset Space)
    (hQ : ∀ x ∈ Q, 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8)
    (hcover : ∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ∃ x ∈ Q, ‖x-y‖ ≤ u^2)
    (hmargin : ∀ h ∈ Icc lo hi, localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8))
    (hheight : ∀ h ∈ Icc lo hi, (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
      (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4))
    (hsmallA : A*(16*(tfPatchCapConstant+3)*100000^4+D)*u^(1-3*masterExponent) ≤ xi/4)
    (hsmallB : A*u ≤ 1)
    (hsmallD : (64*L+192*D)*u^(1-4*masterExponent) ≤ eta)
    (hden : ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ 2*u →
      originalQueryDensity F r₀ j c₁ r₀ s q y ≤ D*u^(-6-3*masterExponent))
    (hquery : ∀ y z : Space, u ≤ ‖y‖ → ‖y‖ ≤ 2*u → u ≤ ‖z‖ → ‖z‖ ≤ 2*u →
      ‖originalQueryDensity F r₀ j c₁ r₀ s q y-originalQueryDensity F r₀ j c₁ r₀ s q z‖ ≤
        L*u^(-7-4*masterExponent)*‖y-z‖)
    (hfield : ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u^2 →
      |‖x‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q x-
        ‖y‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y| ≤
        A*(16*(tfPatchCapConstant+3)*100000^4+D)*u^(1-3*masterExponent)+
          A*u*max (-(‖y‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y)) 0)
    (hgood : q ∉ ⋃ k ∈ H, ⋃ x ∈ Q,
      originalLowFailure F Z lam r₀ s c₁ k (xi/4) j x ∪
        originalHighFailure F Z lam r₀ s c₁ k (xi/4) j x) :
    ∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ∀ h ∈ Icc lo hi,
      (localTFResponse h < (localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y →
        h-xi ≤ (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y) ∧
      ((localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y < localTFResponse h →
        (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y ≤ h+xi) := by
  have hcap : 0 < tfPatchCapConstant+3 := by linarith [tfPatchCapConstant_pos]
  have hnorm := inverse_net_propagation (B := {y : Space | 11*u/8 ≤ ‖y‖ ∧ ‖y‖ ≤ 13*u/8})
    (Q := Q) (H := H)
    (v := fun y => (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y)
    (rho := fun y => (localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y)
    hxi hlo hsmallA hsmallB hmargin hheight
  apply fun y hyl hyh => hnorm ?_ ?_ y ⟨hyl,hyh⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy.1 hy.2
    refine ⟨x,hx,?_,?_⟩
    · simp only [localCellRadius_normalized]
      apply divided_net_field_variation (by norm_num : (1:ℝ) ≤ 100000^4)
        (by positivity) (hfield y x hy.1 hy.2 hxy)
    · have hyl : u ≤ ‖y‖ := by linarith [hy.1]
      have hyh : ‖y‖ ≤ 2*u := by linarith [hy.2]
      have hxl : u ≤ ‖x‖ := by linarith [(hQ x hx).1]
      have hxh : ‖x‖ ≤ 2*u := by linarith [(hQ x hx).2]
      have hn : 0 ≤ originalQueryDensity F r₀ j c₁ r₀ s q y :=
        jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _
      have hd := normalized_density_net_variation hu hD hL hxh hyh hxy hn (hden y hyl hyh)
        (hquery x y hxl hxh hyl hyh)
      have hp : u^(1-3*masterExponent) ≤ u^(1-4*masterExponent) :=
        Real.rpow_le_rpow_of_exponent_ge hu hu1 (by norm_num [masterExponent])
      have hd' : |‖x‖^6*originalQueryDensity F r₀ j c₁ r₀ s q x-
          ‖y‖^6*originalQueryDensity F r₀ j c₁ r₀ s q y| ≤ eta := by
        apply le_trans hd
        calc _ ≤ 64*L*u^(1-4*masterExponent)+192*D*u^(1-4*masterExponent) := by gcongr
             _ = (64*L+192*D)*u^(1-4*masterExponent) := by ring
             _ ≤ eta := hsmallD
      simp only [localCellRadius_normalized]
      rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 100000^6)]
      exact (div_le_self (abs_nonneg _) (by norm_num)).trans hd'
  · intro x hx k hk
    have hfail : q ∉ originalLowFailure F Z lam r₀ s c₁ k (xi/4) j x ∪
        originalHighFailure F Z lam r₀ s c₁ k (xi/4) j x := by
      intro hq
      apply hgood
      exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,hq⟩⟩⟩⟩
    have hr : 0 < localCellRadius x := by
      dsimp [localCellRadius]
      have hn : 0 < ‖x‖ := by linarith [(hQ x hx).1]
      positivity
    have h4 := pow_pos hr 4
    have h6 := pow_pos hr 6
    constructor
    · intro hh
      apply hfail
      right
      exact ⟨(le_div_iff₀ h4).mpr (by nlinarith [hh.1]),
        (div_le_iff₀ h6).mpr (by nlinarith [hh.2])⟩
    · intro hh
      apply hfail
      left
      exact ⟨(div_le_iff₀ h4).mpr (by nlinarith [hh.1]),
        (le_div_iff₀ h6).mpr (by nlinarith [hh.2])⟩

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

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma scaled_rpow_normalization {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (D e : ℝ) :
    D*u^e = (D/a^e)*(a*u)^e := by
  rw [Real.mul_rpow ha.le hu]
  field_simp [Real.rpow_ne_zero ha.le ha.ne']

theorem exists_actual_scaled_original_regularity_constants {a c₁ : ℝ}
    (ha : 1/2 ≤ a) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ T D L A : ℝ, 0 < T ∧ 0 ≤ D ∧ 0 ≤ L ∧ 0 < A ∧
    ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let v := a*u
        let count := observedAnnularCount
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u)
        let cap := fun z => capBandStatistic v (tfPatchCapConstant+2)
          (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
        MeasurableSet[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j]
          {z | T/u^3 < count z ∨ 1 < cap z} ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/u^3 < count z ∨ 1 < cap z} ≤
            u^40+4096*(tfPatchCapConstant+2)*u^60 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i),
          count q ≤ T/u^3 → cap q ≤ 1 →
            (∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
              originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                D*v^(-6-3*masterExponent)) ∧
            (∀ y z : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v → v ≤ ‖z‖ → ‖z‖ ≤ 2*v →
              ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤
                L*v^(-7-4*masterExponent)*‖y-z‖) ∧
            (∀ y x : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 → ‖x-y‖ ≤ v^2 →
              |‖x‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q x-
                ‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y| ≤
              A*(16*(tfPatchCapConstant+3)*100000^4+D)*v^(1-3*masterExponent)+
                A*v*max (-(‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)) 0) ∧
            (∀ y : Space, 5*v/4 ≤ ‖y‖ → ‖y‖ ≤ 7*v/4 →
              (localCellRadius y)^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                16*(tfPatchCapConstant+3)) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨T,D,L,hT,hD,hL,hreg⟩ := exists_actual_expanded_conditional_regularity_constants
    (by linarith : 1 ≤ 2*a) hc hcL
  obtain ⟨A,hA,hfield⟩ := exists_original_net_field_variation_constant
  let D' := D/a^(-6-3*masterExponent)
  let L' := L/a^(-7-4*masterExponent)
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hL' : 0 ≤ L' := by dsimp [L']; positivity
  refine ⟨T,D',L',A,hT,hD',hL',hA,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have has0 : Tendsto (fun i => a*s i) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := a)).mul hs0
  filter_upwards [hreg hs0 hr₀ hstate,
    actual_scaled_original_cap_eventually ha hc hcL hδ hs0 hr₀ hstate,hr₀,
    has0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/96))]
      with i hi hcap hri hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  let v := a*u
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hv : 0 < v := mul_pos ha0 hu
  have hs : 0 < s i := hu.trans_le hjs
  have hvs : v ≤ a*s i := mul_le_mul_of_nonneg_left hjs ha0.le
  have hh := hi j hjs
  have hshape : (3:ℝ)*(2*a) = 6*a := by ring
  simp only [hshape] at hh
  have hp := (hcap j.castSucc hjs).2.1
  have hm := original_capBandStatistic_info_measurable (K := K i) (F i) (Z i) (lam i) (r₀ i) j hc hri hs
    v (tfPatchCapConstant+2)
  refine ⟨(measurableSet_lt measurable_const hh.1).union (measurableSet_lt measurable_const hm),?_,?_⟩
  · exact (measureReal_union_le _ _).trans (add_le_add hh.2.1.le hp)
  · filter_upwards [hh.2.2] with q hq
    intro hcount hcc
    obtain ⟨hden,hquery⟩ := hq hcount
    have hden' : ∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
        originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ D'*v^(-6-3*masterExponent) := by
      intro y hyl hyh
      have ht := hden y (by nlinarith) (by nlinarith)
      exact ht.trans_eq (scaled_rpow_normalization ha0 hu.le D _)
    have hquery' : ∀ y z : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v → v ≤ ‖z‖ → ‖z‖ ≤ 2*v →
        ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
          originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤ L'*v^(-7-4*masterExponent)*‖y-z‖ := by
      intro y z hyl hyh hzl hzh
      have ht := hquery y z (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
      exact ht.trans_eq (congrArg (fun t => t*‖y-z‖) (scaled_rpow_normalization ha0 hu.le L _))
    refine ⟨hden',hquery',?_,?_⟩
    · have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
      have ht := hfield (F i) (Z i) (lam i) (r₀ i) j hc hri hs (hru.trans hjs)
        q v (tfPatchCapConstant+2) D' hv (hvs.trans hsi.le) hC hD' hcc hden'
      simpa only [add_assoc,show (2:ℝ)+1 = 3 by norm_num] using ht
    · exact (hcap j.castSucc hjs).2.2 q hcc

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ScaledSpatialInverse
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
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem exists_actual_scaled_spatial_inverse_constant {a c₁ lo hi xi : ℝ}
    (ha : 1/2 ≤ a) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let v := a*u
        ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
          ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
            (∀ y : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 → ∀ h ∈ Icc lo hi,
              (localTFResponse h < (localCellRadius y)^6*
                  originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
                h-xi ≤ (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
              ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                  localTFResponse h →
                (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
            (∀ y : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                  16*(tfPatchCapConstant+3)) := by
  classical
  have ha0 : 0 < a := by linarith
  obtain ⟨T,D,L,A,hT,hD,hL,hA,hreg⟩ := exists_actual_scaled_original_regularity_constants ha hc hcL
  obtain ⟨H,hH,hheight⟩ := exists_inverse_height_net hlh hxi hlo
  obtain ⟨eta,heta,hmargin⟩ := exists_uniform_inverse_density_margin hlh hxi hlo
  let B : ℝ := 4096*(tfPatchCapConstant+2)
  let C : ℝ := 1+B+4*(H.card:ℝ)*4913/a^3
  have hB : 0 ≤ B := by dsimp [B]; linarith [tfPatchCapConstant_pos]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have has0 : Tendsto (fun i => a*s i) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := a)).mul hs0
  have hpoly : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i)
        (tailPolynomialThreshold (r₀ i)) δ (F i) := by
    filter_upwards [hr₀,hstate] with i hri hi'
    exact ⟨hi'.1,hi'.2.1,hi'.2.2.to_tailTiltState hri (tailPolynomialThreshold_pos hri)
      (fun _ => tinyProbabilityFloor_le_polynomial hi'.1 (by positivity))⟩
  have hinv : ∀ᶠ i in l, ∀ k ∈ H, ∀ (j : Fin (K i)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i → ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ →
      ‖y‖ ≤ (2*a)*((2:ℝ)^j.val*r₀ i) →
      OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j y := by
    apply (Filter.eventually_all_finset H).mpr
    intro k hk
    exact actual_expandedAnnulus_inverse_uniform_eventually (by linarith : 1 ≤ 2*a) hc hcL (by positivity)
      (by linarith [(hH k hk).1]) hδ hs0 hr₀ hpoly
  have heA := uniform_power_error_eventually (C := A*(16*(tfPatchCapConstant+3)*100000^4+D))
    (show 0 < 1-3*masterExponent by norm_num [masterExponent]) (show 0 < xi/4 by positivity) has0
  have heB := uniform_power_error_eventually (C := A) (a := (1:ℝ)) zero_lt_one zero_lt_one has0
  have heD := uniform_power_error_eventually (C := 64*L+192*D)
    (show 0 < 1-4*masterExponent by norm_num [masterExponent]) heta has0
  filter_upwards [hreg hδ hs0 hr₀ hstate,hinv,heA,heB,heD,hr₀,has0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hri' hi' hAi hBi hDi hri hasi hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  let v := a*u
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := hjs.trans hsi.le
  have hs : 0 < s i := hu.trans_le hjs
  have hv : 0 < v := mul_pos ha0 hu
  have hvs : v ≤ a*s i := mul_le_mul_of_nonneg_left hjs ha0.le
  have hv1 : v ≤ 1 := hvs.trans hasi.le
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_inverse_band_spatial_net hv hv1
  let E₀ := {z | T/u^3 < observedAnnularCount
    (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u) z ∨
    1 < capBandStatistic v (tfPatchCapConstant+2)
      (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)}
  let E₁ := ⋃ k ∈ H, ⋃ x ∈ Q,
    originalLowFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j x ∪
      originalHighFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j x
  have hregi := hri' j hjs
  have hE₀ : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E₀ := hregi.1
  have hE₁ : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E₁ := by
    apply MeasurableSet.biUnion H.countable_toSet
    intro k hk
    apply MeasurableSet.biUnion Q.countable_toSet
    intro x hx
    exact original_inverse_failure_info_measurable (F i) (Z i) (lam i) (r₀ i) (s i) c₁
      k (xi/4) j x hc hri hs
  refine ⟨E₀ ∪ E₁,hE₀.union hE₁,?_,?_⟩
  · have hp₁ : (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E₁ ≤
        4*(H.card:ℝ)*(Q.card:ℝ)*u^40 := by
      apply original_inverse_height_net_union_bound Q H
      intro k hk x hx
      exact hi' k hk j x hjs (by have := (hQ x hx).1; dsimp [v] at this; nlinarith)
        (by have := (hQ x hx).2; dsimp [v] at this; nlinarith)
    have hp₁' : (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E₁ ≤
        (4*(H.card:ℝ)*4913/a^3)*u^37 := by
      apply hp₁.trans
      calc _ ≤ 4*(H.card:ℝ)*(4913/v^3)*u^40 := by gcongr
           _ = _ := by dsimp [v]; field_simp
    have hp40 : u^40 ≤ u^37 := pow_le_pow_of_le_one hu.le hu1 (by omega)
    have hp60 : u^60 ≤ u^37 := pow_le_pow_of_le_one hu.le hu1 (by omega)
    apply (measureReal_union_le _ _).trans
    calc _ ≤ (u^40+B*u^60)+(4*(H.card:ℝ)*4913/a^3)*u^37 := add_le_add hregi.2.1 hp₁'
         _ ≤ (u^37+B*u^37)+(4*(H.card:ℝ)*4913/a^3)*u^37 := by gcongr
         _ = C*u^37 := by dsimp [C]; ring
  · filter_upwards [hregi.2.2] with q hq
    intro hqE
    have hq0 : q ∉ E₀ := fun h => hqE (Or.inl h)
    have hq1 : q ∉ E₁ := fun h => hqE (Or.inr h)
    have hcount : observedAnnularCount
        (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u) q ≤ T/u^3 :=
      le_of_not_gt (fun h => hq0 (Or.inl h))
    have hcap : capBandStatistic v (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q) ≤ 1 :=
      le_of_not_gt (fun h => hq0 (Or.inr h))
    obtain ⟨hden,hquery,hfield,hcapq⟩ := hq hcount hcap
    refine ⟨?_,fun y hyl hyh => hcapq y (by linarith) (by linarith)⟩
    exact original_spatial_inverse_propagation (F i) (Z i) (lam i) (r₀ i) (s i) c₁ j q
      hv hv1 hxi hlo hD hL hA.le H Q hQ hcover hmargin hheight
      (hAi v hv hvs) (by simpa using hBi v hv hvs) (hDi v hv hvs)
      hden hquery hfield hq1
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusBandCover
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Set Metric

theorem exists_fullAnnulus_band_cover {B : ℝ} (hB : 1 ≤ B) :
    ∃ A : Finset ℝ, (∀ a ∈ A, 1/2 ≤ a) ∧
      ∀ t ∈ Icc 1 B, ∃ a ∈ A, 11*a/8 ≤ t ∧ t ≤ 13*a/8 := by
  classical
  let J := {q : ℝ // q ∈ Icc 1 B}
  have hc : Icc 1 B ⊆ ⋃ q : J, ball (q : ℝ) (1/32) := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,mem_ball_self (by norm_num)⟩
  obtain ⟨S,hS⟩ := isCompact_Icc.elim_finite_subcover
    (fun q : J => ball (q : ℝ) (1/32)) (fun _ => isOpen_ball) hc
  refine ⟨insert (2*B/3) (S.image (fun q : J => 2*(q:ℝ)/3)),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · linarith
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      linarith [q.property.1]
  · intro t ht
    obtain ⟨q,hq,hclose⟩ := mem_iUnion₂.mp (hS ht)
    have hd : |t-(q:ℝ)| < 1/32 := by simpa only [mem_ball,Real.dist_eq] using hclose
    refine ⟨2*(q:ℝ)/3,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q,hq,rfl⟩),?_,?_⟩
    · linarith [(abs_lt.mp hd).1,q.property.1]
    · linarith [(abs_lt.mp hd).2,q.property.1]

end
open MeasureTheory Filter Set
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem exists_actual_fullAnnulus_inverse_constant_oai {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
          ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u → ∀ h ∈ Icc lo hi,
              (localTFResponse h < (localCellRadius y)^6*
                  originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
                h-xi ≤ (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
              ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                  localTFResponse h →
                (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                  16*(tfPatchCapConstant+3)) := by
  classical
  obtain ⟨A,hA,hcover⟩ := exists_fullAnnulus_band_cover hB
  let J := {a // a ∈ A}
  let : Fintype J := Fintype.ofFinite J
  choose C hC hresult using fun a : J =>
    exists_actual_scaled_spatial_inverse_constant (hA a a.property) hc hcL hlh hxi hlo
  let C₀ : ℝ := 1+∑ a : J, C a
  have hpos : 0 < C₀ := by
    dsimp [C₀]
    have := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset J)) => (hC a).le)
    linarith
  refine ⟨C₀,hpos,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have he : ∀ᶠ i in l, ∀ a : J, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
      ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
        MeasurableSet[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C a*((2:ℝ)^j.val*r₀ i)^37 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
          (∀ y : Space, 11*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 ≤ ‖y‖ →
            ‖y‖ ≤ 13*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 → ∀ h ∈ Icc lo hi,
            (localTFResponse h < (localCellRadius y)^6*
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
              h-xi ≤ (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
            ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                localTFResponse h →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
          (∀ y : Space, 11*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 ≤ ‖y‖ →
            ‖y‖ ≤ 13*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 →
            (localCellRadius y)^4*
              originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                16*(tfPatchCapConstant+3)) := by
    exact Filter.eventually_all.mpr (fun a => hresult a hδ hs0 hr₀ hstate)
  filter_upwards [he,hr₀] with i hi hri
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hu : 0 < u := by dsimp [u]; positivity
  choose E hE hp hg using fun a : J => hi a j hjs
  refine ⟨⋃ a : J, E a,MeasurableSet.iUnion hE,?_,?_⟩
  · calc
      _ ≤ ∑ a : J, (physicalObservationLaw (graphRawLaw (F i)) (K i)).real (E a) :=
        measureReal_iUnion_fintype_le E
      _ ≤ ∑ a : J, C a*u^37 := Finset.sum_le_sum (fun a _ => hp a)
      _ ≤ C₀*u^37 := by rw [←Finset.sum_mul]; dsimp [C₀]; nlinarith [pow_nonneg hu.le 37]
  · have hall := Filter.eventually_all.mpr hg
    filter_upwards [hall] with q hq
    intro hqE
    have heq (a : J) : q ∉ E a := fun h => hqE (mem_iUnion.mpr ⟨a,h⟩)
    have hband (y : Space) (hyl : u ≤ ‖y‖) (hyh : ‖y‖ ≤ B*u) :
        ∃ a : J, 11*((a:ℝ)*u)/8 ≤ ‖y‖ ∧ ‖y‖ ≤ 13*((a:ℝ)*u)/8 := by
      have ht : ‖y‖/u ∈ Icc 1 B := ⟨(le_div_iff₀ hu).mpr (by simpa using hyl),
        (div_le_iff₀ hu).mpr hyh⟩
      obtain ⟨a,ha,hal,hah⟩ := hcover (‖y‖/u) ht
      refine ⟨⟨a,ha⟩,?_,?_⟩
      · have := (le_div_iff₀ hu).mp hal
        dsimp
        nlinarith
      · have := (div_le_iff₀ hu).mp hah
        dsimp
        nlinarith
    constructor
    · intro y hyl hyh h hh
      obtain ⟨a,hal,hah⟩ := hband y hyl hyh
      exact (hq a (heq a)).1 y hal hah h hh
    · intro y hyl hyh
      obtain ⟨a,hal,hah⟩ := hband y hyl hyh
      exact (hq a (heq a)).2 y hal hah

end CoulombAtom

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant_oai.{u_1} := @OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant_oai.{u_1}
