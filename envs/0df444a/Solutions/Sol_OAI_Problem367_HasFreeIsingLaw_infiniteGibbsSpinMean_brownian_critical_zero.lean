-- Prove2me | solution 1 for OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:03.138777+00:00
-- url     : https://prove2.me/submissions/6ff8740c-198a-4fa6-9034-2e988f56828b

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussian_root_information_le_component
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selected_child_parent_abs_le
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selected_child_parent_secondMoment
import Theorems.Thm_OAI_Problem367_condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem sqrt_bound_of_quadratic_information_loss {M c K t : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K)
    (h : M ≤ M - c * M ^ 2 + K * t) :
    M ≤ Real.sqrt (K / c) * Real.sqrt t := by
  have hquad : M ^ 2 ≤ K * t / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  calc
    M ≤ Real.sqrt (K * t / c) := Real.le_sqrt_of_sq_le hquad
    _ = Real.sqrt (K / c) * Real.sqrt t := by
      rw [show K * t / c = (K / c) * t by ring,
        Real.sqrt_mul (div_nonneg hK hc.le)]

theorem critical_information_upper_of_fusion {b theta M t : ℝ}
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hcritical : b * theta ^ 2 = 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : M ≤ b * theta ^ 2 * M -
      2 * (1 - theta ^ 2) * theta ^ 4 * M ^ 2 + (t + t ^ 2)) :
    M ≤ Real.sqrt (1 / ((1 - theta ^ 2) * theta ^ 4)) * Real.sqrt t := by
  have hθsq : theta ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one theta).mpr (abs_lt.mpr ⟨by linarith, hθ1⟩)
  have hc : 0 < (1 - theta ^ 2) * theta ^ 4 :=
    mul_pos (sub_pos.mpr hθsq) (pow_pos hθ0 4)
  have htsq : t ^ 2 ≤ t := by nlinarith
  rw [hcritical, one_mul] at h
  have hrec : M ≤ M - (2 * ((1 - theta ^ 2) * theta ^ 4)) * M ^ 2 + 2 * t := by
    nlinarith
  have hbound := sqrt_bound_of_quadratic_information_loss
    (mul_pos (by norm_num : (0 : ℝ) < 2) hc) (by norm_num : (0 : ℝ) ≤ 2) hrec
  have hratio : (2 : ℝ) / (2 * ((1 - theta ^ 2) * theta ^ 4)) =
      1 / ((1 - theta ^ 2) * theta ^ 4) := by field_simp
  simpa only [hratio] using hbound

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ObservationMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem367

variable {Ω ι : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integral_mul_centered_noise {S B : Ω → ℝ}
    (hS : MemLp S 2 μ) (hB : MemLp B 2 μ)
    (hSB : IndepFun S B μ) (hmean : ∫ ω, B ω ∂μ = 0) :
    (∫ ω, S ω * B ω ∂μ) = 0 := by
  rw [hSB.integral_fun_mul_eq_mul_integral hS.aestronglyMeasurable
    hB.aestronglyMeasurable, hmean, mul_zero]

theorem integral_observation_mul_observation
    {S T B C : Ω → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hSC : IndepFun S C μ) (hTB : IndepFun T B μ)
    (hBzero : ∫ ω, B ω ∂μ = 0) (hCzero : ∫ ω, C ω ∂μ = 0) (t : ℝ) :
    (∫ ω, (t * S ω + B ω) * (t * T ω + C ω) ∂μ) =
      t ^ 2 * (∫ ω, S ω * T ω ∂μ) + ∫ ω, B ω * C ω ∂μ := by
  have h1 : Integrable (fun ω => t ^ 2 * (S ω * T ω)) μ :=
    (hS.integrable_mul hT).const_mul (t ^ 2)
  have h2 : Integrable (fun ω => t * (S ω * C ω)) μ :=
    (hS.integrable_mul hC).const_mul t
  have h3 : Integrable (fun ω => t * (T ω * B ω)) μ :=
    (hT.integrable_mul hB).const_mul t
  have h4 : Integrable (fun ω => B ω * C ω) μ := hB.integrable_mul hC
  calc
    _ = ∫ ω, ((t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) +
          t * (T ω * B ω)) + B ω * C ω ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := by
      have h12 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) μ :=
        h1.add h2
      have h123 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω) +
          t * (T ω * B ω)) μ := h12.add h3
      rw [integral_add h123 h4,
        integral_add h12 h3, integral_add h1 h2]
      simp_rw [integral_const_mul]
      rw [integral_mul_centered_noise hS hC hSC hCzero,
        integral_mul_centered_noise hT hB hTB hBzero]
      ring

theorem centered_gaussian_moments {B : Ω → ℝ} {t : ℝ≥0}
    (hB : HasLaw B (gaussianReal 0 t) μ) :
    MemLp B 2 μ ∧ (∫ ω, B ω ∂μ) = 0 ∧ (∫ ω, B ω ^ 2 ∂μ) = t := by
  refine ⟨hB.hasGaussianLaw.memLp_two, ?_, ?_⟩
  · rw [hB.integral_eq, integral_id_gaussianReal]
  · have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := t)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable, integral_id_gaussianReal] at hv
    simp only [sub_zero] at hv
    simpa only [Function.comp_apply] using
      (hB.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans hv

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    HasFreeIsingLaw theta (mu.map flipConfig) := by
  intro D hD eta
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    simp only [Set.ofPred_forall]
    apply D.measurableSet_biInter
    intro v hv
    exact (show MeasurableSet ({eta v} : Set IsingSpin) from trivial).preimage
      (measurable_pi_apply v)
  rw [Measure.map_apply measurable_flipConfig hmeas]
  have hpre : flipConfig ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = flipConfig eta v} := by
    ext x
    simp [flipConfig]
  rw [hpre, hmu D hD (flipConfig eta), freeCylinderWeight_flipConfig]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    mu.map flipConfig = mu :=
  hmu.map_flipConfig.unique hmu

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

theorem spinSign_memLp (mu : Measure (κ → IsingSpin)) [IsFiniteMeasure mu]
    (r : κ) : MemLp (fun σ => spinSign (σ r)) 2 mu := by
  apply MemLp.of_bound (measurable_spinSign.comp (measurable_pi_apply r)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun σ => by cases h : σ r <;> norm_num [spinSign, h])

theorem noise_hasLaw (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i : κ) :
    HasLaw (fun p : (κ → IsingSpin) × (κ → ℝ) => p.2 i) (gaussianReal 0 t)
      (mu.prod (gaussianNoiseLaw κ t)) :=
  ((measurePreserving_eval_infinitePi (fun _ : κ => gaussianReal 0 t) i).comp
    measurePreserving_snd).hasLaw

theorem spin_noise_indep (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i j : κ) :
    IndepFun (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 i))
      (fun p => p.2 j) (mu.prod (gaussianNoiseLaw κ t)) :=
  indepFun_prod (μ := mu) (ν := gaussianNoiseLaw κ t)
    (X := fun σ => spinSign (σ i)) (Y := fun B => B j)
    (measurable_spinSign.comp (measurable_pi_apply i)) (measurable_pi_apply j)

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

lemma abs_tanh_le_abs_response (z : ℝ) : |Real.tanh z| ≤ |z| := by
  have h := lipschitzWith_tanh_response.dist_le_mul z 0
  simpa [Real.dist_eq] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedPosterior rho F v r) :=
  stronglyMeasurable_condExp.measurable.mono (selectedObservationField_le hF v) le_rfl

theorem selectedObservationField_comap_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (g : TreeAut d) :
    (selectedObservationField F v).comap (Prod.map (relabel g) (relabel g)) =
      selectedObservationField F (fun i => g.toEquiv.symm (v i)) := by
  unfold selectedObservationField
  rw [MeasurableSpace.comap_comp]
  rfl

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

theorem selectedPosterior_relabel_ae {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
        Prod.map (relabel g) (relabel g) =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
      selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) := by
  let := hmu.isProbabilityMeasure
  let rho := mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) rho := by
    apply Integrable.of_bound
      ((hsign.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hCE := condExp_comp_measurePreserving rho rho
    (Prod.map (relabel g) (relabel g))
    (PlantedStationarity.measurePreserving_planted_relabel hmu nu g)
    (selectedObservationField F v) (selectedObservationField_le hF v) hi
  rw [selectedObservationField_comap_relabel] at hCE
  exact hCE.symm

theorem selectedPosterior_identDistrib_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have hm := measurable_selectedPosterior
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) hF v r
  refine ⟨hm.aemeasurable, (measurable_selectedPosterior _ hF _ _).aemeasurable, ?_⟩
  have hCE := selectedPosterior_relabel_ae hmu nu hF v r g
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hmu nu g
  calc
    _ = Measure.map
        (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
          Prod.map (relabel g) (relabel g))
        (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
      rw [← Measure.map_map hm hmp.measurable, hmp.map_eq]
    _ = _ := Measure.map_congr hCE

theorem selectedPosterior_identDistrib_of_range_relabel {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (w : κ → TreeVertex d) (r s : TreeVertex d) (g : TreeAut d)
    (hregion : Set.range (fun i => g.toEquiv.symm (v i)) = Set.range w)
    (hroot : g.toEquiv.symm r = s) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F w s)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have h := selectedPosterior_identDistrib_relabel hmu nu hF v r g
  simpa only [selectedPosterior, selectedObservationField_eq_of_range_eq F hregion, hroot] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem selectedPosterior_abs_le_one {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∀ᵐ p ∂ρ, |selectedPosterior ρ F v r p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 r <;> norm_num [spinSign, hs]

theorem integrable_selectedPosterior_abs_pow {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsFiniteMeasure ρ] {F : IsingSpin → A → B}
    (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (n : ℕ) :
    Integrable (fun p => |selectedPosterior ρ F v r p| ^ n) ρ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_selectedPosterior ρ hF v r).abs.pow_const n).aestronglyMeasurable)
  filter_upwards [selectedPosterior_abs_le_one ρ F v r] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_one₀ (abs_nonneg _) hp

theorem measurePreserving_plantedMarkFlip {d : ℕ} {A : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν) :
    MeasurePreserving (plantedMarkFlipEquiv d A)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  have hm : (Measure.infinitePi (fun _ : TreeVertex d => ν)).map Neg.neg =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    change (Measure.infinitePi (fun _ : TreeVertex d => ν)).map
      (fun z i => -z i) = _
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
    simp only [hν]
  exact (show MeasurePreserving flipConfig μ μ from
    ⟨measurable_flipConfig, hμ.flip_invariant⟩).prod
    (show MeasurePreserving Neg.neg
      (Measure.infinitePi (fun _ : TreeVertex d => ν))
      (Measure.infinitePi (fun _ : TreeVertex d => ν)) from ⟨measurable_neg, hm⟩)

theorem measurable_plantedMarkFlip_selectedObservationField
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B]
    (F : IsingSpin → A → B)
    (hodd : ∀ s z, F s.flip (-z) = -F s z) (v : ι → TreeVertex d) :
    Measurable[selectedObservationField F v, selectedObservationField F v]
      (plantedMarkFlipEquiv d A) := by
  apply measurable_comap_iff.mpr
  have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) ∘ plantedMarkFlipEquiv d A =
      fun p i => -F (p.1 (v i)) (p.2 (v i)) := by
    funext p i
    exact hodd (p.1 (v i)) (p.2 (v i))
  rw [heq]
  exact (comap_measurable (fun p : (TreeVertex d → IsingSpin) ×
    (TreeVertex d → A) => fun i => F (p.1 (v i)) (p.2 (v i)))).neg

theorem selectedPosterior_flip_ae {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r ∘
      plantedMarkFlipEquiv d A =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      -selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ρ := by
    have hs : Measurable spinSign := by intro s hs; trivial
    apply Integrable.of_bound
      ((hs.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hm := measurable_plantedMarkFlip_selectedObservationField F hodd v
  have hn := condExp_comp_measurePreserving_equiv
    (selectedObservationField_le hF v) (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν) hm hm hi
  have ho : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ∘ plantedMarkFlipEquiv d A =
      -(fun p => spinSign (p.1 r)) := by
    funext p
    cases hs : p.1 r <;>
      simp [plantedMarkFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [ho] at hn
  exact hn.trans (condExp_neg _ _)

theorem selectedPosteriorLaw_neg_invariant {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
      (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r)).map
        Neg.neg =
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
        (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_plantedMarkFlip hμ ν hν) measurable_neg
    (measurable_selectedPosterior _ hF v r)
    (selectedPosterior_flip_ae hμ ν hν hF hodd v r)

theorem HasFreeIsingLaw.selected_gaussian_posteriorLaw_neg_invariant
    {d : ℕ} {ι : Type*} {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (t : ℝ) (variance : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
      (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun s z => t * spinSign s + z) v r)).map Neg.neg =
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
        (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
          (fun s z => t * spinSign s + z) v r) := by
  apply selectedPosteriorLaw_neg_invariant hμ (gaussianReal 0 variance)
  · simp only [gaussianReal_map_neg, neg_zero]
  · have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul t).add measurable_snd
  · intro s z
    cases s <;> simp [IsingSpin.flip, spinSign] <;> ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ComponentInformationUpper
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance componentInformationUpperNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem singletonGibbsSpinMean_eq_tanh {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (v : TreeVertex d) (y : ({v} : Finset (TreeVertex d)) → ℝ) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta {v})
      (fun (eta : ({v} : Finset (TreeVertex d)) → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta ⟨v, by simp⟩)) y = Real.tanh (y ⟨v, by simp⟩) := by
  classical
  let r : ({v} : Finset (TreeVertex d)) := ⟨v, by simp⟩
  have hm := FinitePosterior.fieldMean_spin_mem_Ioo (finiteIsingEnergy beta {v})
    (fun (eta : ({v} : Finset (TreeVertex d)) → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta r)) y
    (fun eta => by cases eta r <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hfield := finite_tree_gibbs_field_bound {v} hb y r
  change |Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta {v})
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta r)) y) - y r| ≤ _ at hfield
  simp only [inducedEdges_singleton, Finset.filter_empty, Finset.card_empty,
    Nat.cast_zero, zero_mul] at hfield
  have heq := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hfield (abs_nonneg _)))
  rw [← Real.tanh_artanh hm, heq]

theorem HasFreeIsingLaw.selected_singleton_gaussian_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z) (fun _ : Unit => v) v =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => Real.tanh (observation t p v) := by
  classical
  have hfield : MeasurableSpace.comap (finiteObservation {v} t) inferInstance =
      selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
        (fun _ : Unit => v) := by
    change selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
      (fun w : ({v} : Finset (TreeVertex d)) => w.1) = _
    apply selectedObservationField_eq_of_range_eq
    ext w
    simp
  have hce := hμ.finiteObservation_condExp {v} (connectedFinset_singleton v) t
    (fun eta => spinSign (eta ⟨v, by simp⟩))
  rw [hfield] at hce
  filter_upwards [hce] with p hp
  change selectedPosterior _ _ _ _ p = _ at hp
  rw [hp, singletonGibbsSpinMean_eq_tanh hb]
  rfl

theorem gaussian_observation_second_moment {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, (observation t p v) ^ 2 ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) =
      (t : ℝ) + (t : ℝ) ^ 2 := by
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  have hS : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 v)) 2 ρ :=
    (PlantedInformation.spinSign_memLp μ v).comp_measurePreserving measurePreserving_fst
  have hB := centered_gaussian_moments (PlantedInformation.noise_hasLaw μ t v)
  have hind := PlantedInformation.spin_noise_indep μ t v v
  have h := integral_observation_mul_observation hS hS hB.1 hB.1 hind hind
    hB.2.1 hB.2.1 (t : ℝ)
  have hspin : (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ),
      spinSign (p.1 v) * spinSign (p.1 v) ∂ρ) = 1 := by
    have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        spinSign (p.1 v) * spinSign (p.1 v)) = fun _ => (1 : ℝ) := by
      funext p
      cases p.1 v <;> norm_num [spinSign]
    rw [heq]
    simp [ρ]
  rw [hspin] at h
  simp only [← pow_two] at h
  rw [hB.2.2] at h
  simpa only [observation, pow_two, mul_one, add_comm] using h

theorem HasFreeIsingLaw.selected_singleton_information_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z) (fun _ : Unit => v) v p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ (t : ℝ) + (t : ℝ) ^ 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  have hF : Measurable (Function.uncurry
      (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hpost := integrable_selectedPosterior_abs_pow ρ hF (fun _ : Unit => v) v 2
  simp only [sq_abs] at hpost
  have hS := (PlantedInformation.spinSign_memLp μ v).comp_measurePreserving
    (measurePreserving_fst (ν := gaussianNoiseLaw (TreeVertex d) t))
  have hB := (centered_gaussian_moments (PlantedInformation.noise_hasLaw μ t v)).1
  have hobs : Integrable (fun p => (observation t p v) ^ 2) ρ :=
    ((hS.const_mul (t : ℝ)).add hB).integrable_sq
  rw [← gaussian_observation_second_moment μ t v]
  apply integral_mono_ae hpost hobs
  filter_upwards [hμ.selected_singleton_gaussian_posterior hb t v] with p hp
  rw [hp]
  have hbound := abs_tanh_le_abs_response (observation t p v)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hbound 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Descent
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ) : CondIndepFun m hm f g ν := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := (condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)).mp hfg U V hU hV
  have hmeas : MeasurableSet {ω' | (ν⟦f ⁻¹' U ∩ g ⁻¹' V | m⟧) ω' =
      (ν⟦f ⁻¹' U | m⟧) ω' * (ν⟦g ⁻¹' V | m⟧) ω'} :=
    measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm).measurable
      ((stronglyMeasurable_condExp.mono hm).measurable.mul
        (stronglyMeasurable_condExp.mono hm).measurable)
  have hdesc := ae_map_iff (μ := μ) he.measurable.aemeasurable hmeas
  rw [he.map_eq] at hdesc
  apply hdesc.mpr
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.symm.trans (hωmul.trans (congrArg₂ (· * ·) hωE hωH))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FamilyConditionalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

alias ⟨_, iCondIndepFun_of_comp_measurePreserving⟩ :=
  iCondIndepFun_iff_comp_measurePreserving

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

variable {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem infinitePi_map_pair_arrays
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      (fun p : (s → A) × (s → B) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_pairs
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteBlockIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory

section Unconditional

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} {f : ∀ i, Ω → X i}

theorem iIndepFun_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun j ω (i : S j) => f i ω) μ := by
  have := hf.isProbabilityMeasure
  have : ∀ index, IsProbabilityMeasure (μ.map (f index)) :=
    fun i => Measure.isProbabilityMeasure_map (hm i).aemeasurable
  have hinj : Function.Injective (fun p : (j : κ) × S j => (p.2 : ι)) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    change (u : ι) = (v : ι) at huv
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hS hne) u.property (huv.symm ▸ v.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext huv)
  have hgroup := hf.precomp hinj
  have hmap := hgroup.map_fun_eq_infinitePi_map (fun p => hm p.2)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  calc
    μ.map (fun ω j (i : S j) => f i ω) =
        (μ.map (fun ω (p : (j : κ) × S j) => f p.2 ω)).map
          (MeasurableEquiv.piCurry (fun j (i : S j) => X i)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j =>
        Measure.infinitePi (fun i : S j => μ.map (f i))) := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun (j : κ) (i : S j) => μ.map (f i))
    _ = Measure.infinitePi (fun j => μ.map (fun ω (i : S j) => f i ω)) := by
      congr 1
      funext j
      exact (hf.precomp (g := fun i : S j => (i : ι)) Subtype.val_injective
        |>.map_fun_eq_infinitePi_map (fun i : S j => hm (i : ι))).symm

theorem infinitePi_map_disjoint_family {κ : Type*}
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S : κ → Set ι) (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    (Measure.infinitePi ν).map (fun labels index => (S index).domRestrict labels) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i : S j => ν i)) := by
  have h := iIndepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S hS (μ := Measure.infinitePi ν)
  change iIndepFun (fun index labels => (S index).domRestrict labels)
    (Measure.infinitePi ν) at h
  calc
    _ = Measure.infinitePi (fun index => (Measure.infinitePi ν).map (S index).domRestrict) :=
      h.map_fun_eq_infinitePi_map (by fun_prop)
    _ = _ := by
      congr 1
      funext j
      exact Measure.infinitePi_map_restrict' ν

end Unconditional

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentProductIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem setIntegral_prod_preimage_fst
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {f : S × A → ℝ} (hf : Integrable f (ρ.prod μ)) (D : Set S) :
    (∫ z in Prod.fst ⁻¹' D, f z ∂ρ.prod μ) =
      ∫ s in D, ∫ a, f (s, a) ∂μ ∂ρ := by
  have hset : (Prod.fst ⁻¹' D : Set (S × A)) = D ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  apply integral_prod
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.restrict

theorem condExp_prod_fst
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    {f : S × A → ℝ} (hfm : StronglyMeasurable f) (hf : Integrable f (ρ.prod μ)) :
    (ρ.prod μ)[f | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
      fun z => ∫ a, f (z.1, a) ∂μ := by
  have hg : Integrable (fun z : S × A => ∫ a, f (z.1, a) ∂μ) (ρ.prod μ) :=
    hf.integral_prod_left.comp_fst μ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn)
  · intro D hD _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hD
    rw [setIntegral_prod_preimage_fst ρ μ hg,
      setIntegral_prod_preimage_fst ρ μ hf]
    simp
  · have hfm' : StronglyMeasurable (Function.uncurry (fun s a => f (s, a))) := by
      simpa only [Function.uncurry_def] using hfm
    exact (hfm'.integral_prod_right.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_latent_product
    {S A B C D : Type*} [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace S] [StandardBorelSpace A] [StandardBorelSpace B]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap (Prod.fst : S × (A × B) → S)) measurable_fst.comap_le
      (fun z : S × (A × B) => F (z.1, z.2.1))
      (fun z : S × (A × B) => G (z.1, z.2.2)) (ρ.prod (μ.prod ν)) := by
  classical
  have hFm : Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) := by fun_prop
  have hGm : Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) := by fun_prop
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hFm hGm]
  intro U V hU hV
  let E : Set (S × (A × B)) := (fun z => F (z.1, z.2.1)) ⁻¹' U
  let H : Set (S × (A × B)) := (fun z => G (z.1, z.2.2)) ⁻¹' V
  have hE : MeasurableSet E := hU.preimage hFm
  have hH : MeasurableSet H := hV.preimage hGm
  have hcE := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hE).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hE)
  have hcH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hH).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hH)
  have hcEH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator (hE.inter hH)).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  filter_upwards [hcE, hcH, hcEH] with z hzE hzH hzEH
  change ((ρ.prod (μ.prod ν))[(E ∩ H).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzEH, hzE, hzH]
  have hprod : (fun ab : A × B => (E ∩ H).indicator (fun _ => (1 : ℝ)) (z.1, ab)) =
      fun ab => (if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0) *
        (if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0) := by
    funext ab
    by_cases hfa : F (z.1, ab.1) ∈ U <;> by_cases hgb : G (z.1, ab.2) ∈ V <;>
      simp [E, H, hfa, hgb]
  rw [hprod, integral_prod_mul
    (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)
    (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
  have hleft : (∫ ab : A × B, E.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ a, if F (z.1, a) ∈ U then (1 : ℝ) else 0 ∂μ := by
    change (∫ ab : A × B, if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_fst (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)]
    simp
  have hright : (∫ ab : A × B, H.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ b, if G (z.1, b) ∈ V then (1 : ℝ) else 0 ∂ν := by
    change (∫ ab : A × B, if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_snd (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
    simp
  rw [hleft, hright]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentFamilyIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_latent_of_fiber_indep
    {ι S A : Type*} {B : ι → Type*}
    [mS : MeasurableSpace S] [MeasurableSpace A]
    [mB : ∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [StandardBorelSpace A]
    (ρ : Measure S) (μ : Measure A)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    (F : ∀ i, S × A → B i) (hF : ∀ i, Measurable (F i))
    (hind : ∀ s, iIndepFun (fun i a => F i (s, a)) μ) :
    iCondIndepFun (mS.comap (Prod.fst : S × A → S)) measurable_fst.comap_le
      F (ρ.prod μ) := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB F hF]
  intro I sets hsets
  let E : ι → Set (S × A) := fun i => F i ⁻¹' sets i
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi => (hsets i hi).preimage (hF i)
  have hEI : MeasurableSet (⋂ i ∈ I, E i) := by
    exact I.measurableSet_biInter hE
  have hcI := condExp_prod_fst ρ μ
    (measurable_const.indicator hEI).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hEI)
  have hc : ∀ i ∈ I,
      (ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
        fun z => ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ := by
    intro i hi
    exact condExp_prod_fst ρ μ
      (measurable_const.indicator (hE i hi)).stronglyMeasurable
      ((integrable_const (1 : ℝ)).indicator (hE i hi))
  have hcall := (Filter.eventually_all_finset I).2 hc
  filter_upwards [hcI, hcall] with z hzI hz
  change ((ρ.prod μ)[(⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzI]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ I,
      ((ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst]) z) =
      ∏ i ∈ I, ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ :=
    Finset.prod_congr rfl hz
  rw [hprod]
  let T : ι → Set A := fun i => (fun a => F i (z.1, a)) ⁻¹' sets i
  have hT : ∀ i ∈ I, MeasurableSet (T i) := by
    intro i hi
    exact (hsets i hi).preimage ((hF i).comp (measurable_const.prodMk measurable_id))
  have hTI : MeasurableSet (⋂ i ∈ I, T i) := I.measurableSet_biInter hT
  have hleft : (fun a => (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) (z.1, a)) =
      (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator, Set.mem_iInter, E, T, Set.mem_preimage]
  rw [hleft]
  have hmass : (∫ a, (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) a ∂μ) =
      μ.real (⋂ i ∈ I, T i) := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hTI)
  rw [hmass]
  have hright : ∀ i ∈ I,
      (∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ) = μ.real (T i) := by
    intro i hi
    change (∫ a, (T i).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) (hT i hi))
  rw [Finset.prod_congr rfl hright]
  unfold Measure.real
  rw [(hind z.1).measure_inter_preimage_eq_mul I hsets, ENNReal.toReal_prod]

theorem iCondIndepFun_latent_infinitePi
    {ι S : Type*} [Countable ι] {A B : ι → Type*}
    [mS : MeasurableSpace S] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [∀ i, StandardBorelSpace (A i)]
    (ρ : Measure S) (ν : ∀ i, Measure (A i))
    [IsFiniteMeasure ρ] [∀ i, IsProbabilityMeasure (ν i)]
    (F : ∀ i, S × A i → B i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun (mS.comap (Prod.fst : S × (∀ i, A i) → S))
      measurable_fst.comap_le
      (fun i z => F i (z.1, z.2 i)) (ρ.prod (Measure.infinitePi ν)) := by
  apply iCondIndepFun_latent_of_fiber_indep ρ (Measure.infinitePi ν)
    (fun i z => F i (z.1, z.2 i))
  · intro i
    exact (hF i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · intro s
    exact iIndepFun_infinitePi (fun i =>
      (hF i).comp (measurable_const.prodMk measurable_id))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

lemma prefix_in_branch_or_root {d : ℕ} (c : Fin d)
    {u v : TreeVertex d} (hv : [c] <+: v.val) (huv : u.val <+: v.val) :
    u.val = [] ∨ [c] <+: u.val := by
  by_cases hu : u.val = []
  · exact Or.inl hu
  · right
    apply List.prefix_of_prefix_length_le hv huv
    have : 0 < u.val.length := List.length_pos_iff.mpr hu
    simpa only [List.length_singleton] using Nat.succ_le_of_lt this

lemma measurable_branchNoise {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (fun p : IsingSpin × (BranchVertex c → ℝ) => branchNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.val = []
  · simpa only [branchNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst : IsingSpin × (BranchVertex c → ℝ) → IsingSpin))
  · by_cases hv : [c] <+: v.val
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : BranchVertex c => ℝ) ⟨v,hv⟩).comp measurable_snd)
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ : IsingSpin × (BranchVertex c → ℝ) => IsingSpin.pos))

lemma measurable_branchFactor {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (branchFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.val).comp (measurable_branchNoise theta c)

lemma factor_branch_representation {d : ℕ} (theta : ℝ) (c : Fin d)
    (U : TreeVertex d → ℝ) :
    (fun v : BranchVertex c => factor theta U v.val) =
      branchFactor theta c (fairSpin (U (root d)), fun v : BranchVertex c => U v.val) := by
  funext v
  apply ofNoise_congr_prefix
  intro w hw
  rcases prefix_in_branch_or_root c v.property hw with hnil | hbranch
  · have heq : w = root d := (eq_root_iff w).mpr hnil
    subst w
    simp [inputNoise, branchNoise]
  · have hnil : w.val ≠ [] := by
      intro heq
      rw [heq] at hbranch
      have hl := hbranch.length_le
      simp at hl
    simp [inputNoise, branchNoise, hnil, hbranch]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

namespace RootedBroadcast

lemma branch_disjoint {d : ℕ} {c e : Fin d} (hce : c ≠ e) :
    Disjoint {v : TreeVertex d | [c] <+: v.val} {v | [e] <+: v.val} := by
  apply Set.disjoint_left.mpr
  intro v hc he
  have hprefix : [c] <+: [e] := List.prefix_of_prefix_length_le hc he (by simp)
  have heq : [c] = [e] := hprefix.eq_of_length (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hce (by simpa only [List.singleton_inj] using heq)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_rd7e72b_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

theorem map_root_branch_family_of_sampler {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [MeasurableSpace S]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f) :
    (Measure.infinitePi ν).map (fun U => (f (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun v : BranchVertex c => ν v.val))) := by
  let F : (NonrootVertex d → A) → (∀ c : Fin d, BranchVertex c → A) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_coordinate_rest ν (root d)).comp hf hF
  have hB : Measurable (fun U : TreeVertex d → A => f (U (root d))) :=
    hf.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hroot : (Measure.infinitePi ν).map (fun U => f (U (root d))) =
      (ν (root d)).map f := by
    change (Measure.infinitePi ν).map (f ∘ (fun U => U (root d))) = _
    rw [← Measure.map_map hf (measurable_pi_apply (root d)), Measure.infinitePi_map_eval]
  change IndepFun (fun U : TreeVertex d → A => f (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val)
    (Measure.infinitePi ν) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable, hroot]
  congr 1
  exact infinitePi_map_disjoint_family ν
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem iCondIndepFun_root_branch_observables {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [mS : MeasurableSpace S]
    [StandardBorelSpace A] [StandardBorelSpace S]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f)
    (F : ∀ c, S × (BranchVertex c → A) → B c) (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      (mS.comap (fun U : TreeVertex d → A => f (U (root d))))
      (hf.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => F c (f (U (root d)), fun v => U v.val))
      (Measure.infinitePi ν) := by
  let e : (TreeVertex d → A) → S × (∀ c : Fin d, BranchVertex c → A) :=
    fun U => (f (U (root d)), fun c v => U v.val)
  let ρ := ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
    Measure.infinitePi (fun v : BranchVertex c => ν v.val)))
  have he : MeasurePreserving e (Measure.infinitePi ν) ρ :=
    ⟨(hf.comp (measurable_pi_apply (root d))).prodMk (by fun_prop),
      map_root_branch_family_of_sampler ν f hf⟩
  have hbase := iCondIndepFun_latent_infinitePi ((ν (root d)).map f)
    (fun c : Fin d => Measure.infinitePi (fun v : BranchVertex c => ν v.val)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (Measure.infinitePi ν) ρ e he
    (mS.comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun z : S × (∀ c : Fin d, BranchVertex c → A) =>
      F c (z.1, z.2 c)) from by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

theorem map_noisyBroadcast {d : ℕ} {A : Type*} [MeasurableSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (factor theta (fun v => (U v).1), fun v => (U v).2)) =
      (freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fun v => (U v).1), fun v => (U v).2))).map
        (Prod.map (factor theta) id) := by
      rw [Measure.map_map ((measurable_factor d theta).prodMap measurable_id) (by fun_prop)]
      rfl
    _ = _ := by
      rw [infinitePi_map_split_pairs, ← Measure.map_prod_map _ _
        (measurable_factor d theta) measurable_id, Measure.map_id]
      rfl

local instance instMeasurableSingletonClassIsingSpin_2_rd7e72b_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem iCondIndepFun_noisy_factor_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let F : ∀ c : Fin d, IsingSpin × (BranchVertex c → ℝ × A) →
      (BranchVertex c → IsingSpin) × (BranchVertex c → A) :=
    fun c p => (branchFactor theta c (p.1, fun v => (p.2 v).1),
      fun v => (p.2 v).2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := iCondIndepFun_root_branch_observables
    (fun v => uniform01.prod (ν v)) (fun p : ℝ × A => fairSpin p.1)
    (measurable_fairSpin.comp measurable_fst) F hF
  have heq : (fun (c : Fin d) (U : TreeVertex d → ℝ × A) => F c (fairSpin (U (root d)).1, fun v => U v.val)) =
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2)) := by
    funext c U
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  rw [heq] at h
  exact h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_1_rd7e72b_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_iCondIndepFun_noisy_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply iCondIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ × A =>
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d)).1) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.iCondIndepFun_noisy_factor_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_branches {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_branches theta ν

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_NoisyBranchConditionalLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin_rd7e72b_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.planted_spin_event_mass
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (v : TreeVertex d) (s : IsingSpin) :
    (μ.prod (Measure.infinitePi ν))
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hset :
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} =
        {x : TreeVertex d → IsingSpin | x v = s} ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one, hμ.marginal]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

theorem exists_treeAut_map {d : ℕ} (u v : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = v := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root u
  obtain ⟨h, hh⟩ := exists_treeAut_to_root v
  refine ⟨g.trans h.symm, ?_⟩
  change h.toEquiv.symm (g.toEquiv u) = v
  rw [hg, ← hh]
  exact h.toEquiv.symm_apply_apply v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem childComponentIndexVertex_val {d : ℕ} {c a : Fin d} (hca : c ≠ a)
    (u : ComponentIndex a) : (childComponentIndexVertex c a u).1 = c :: a :: u.2.1 := by
  simp [childComponentIndexVertex, prefixFlip, prefixFlipWord, componentIndexVertex, componentVertex, hca]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentObservationDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem componentObservationField_eq_own_sup_children
    {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (c : Fin d) :
    selectedObservationField F (componentIndexVertex (c := c)) =
      selectedObservationField F (fun _ : Unit =>
        (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d)) ⊔
      ⨆ a : {a : Fin d // c ≠ a}, selectedObservationField F (childComponentIndexVertex c a.1) := by
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi, iSup_const]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, w, hlen, hchain⟩
    cases w with
    | nil => exact le_sup_left
    | cons a w =>
        have hca : c ≠ a := (List.isChain_cons_cons.mp hchain).1
        let u : ComponentIndex a := ⟨w.length, ⟨w, rfl, hchain.tail⟩⟩
        have hv : componentIndexVertex (c := c) ⟨n, ⟨a :: w, hlen, hchain⟩⟩ =
            childComponentIndexVertex c a u := by
          apply Subtype.ext
          simp [childComponentIndexVertex_val hca, componentIndexVertex, componentVertex, u]
        rw [hv]
        exact le_sup_of_le_right (le_iSup_of_le (⟨a, hca⟩ : {a : Fin d // c ≠ a})
          (le_iSup_of_le u le_rfl))
  · apply sup_le
    · exact le_iSup_of_le (⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩ : ComponentIndex c) le_rfl
    · apply iSup_le
      intro a
      apply iSup_le
      intro u
      let w : ComponentIndex c := ⟨u.1 + 1, ⟨a.1 :: u.2.1,
        by simp [u.2.2.1], List.isChain_cons_cons.mpr ⟨a.2, u.2.2.2⟩⟩⟩
      have hv : childComponentIndexVertex c a.1 u = componentIndexVertex w := by
        apply Subtype.ext
        simp [childComponentIndexVertex_val a.2, componentIndexVertex, componentVertex, w]
      rw [hv]
      exact le_iSup_of_le w le_rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LatentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyRootIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_3_rd7e72b_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem map_root_ownNoise_branch_family {d : ℕ} {A : Type*}
    [MeasurableSpace A] (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (fairSpin (U (root d)).1, (U (root d)).2,
          fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      (uniform01.map fairSpin).prod ((ν (root d)).prod
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))) := by
  have hbase := map_root_branch_family_of_sampler
    (fun v => uniform01.prod (ν v))
    (fun p : ℝ × A => (fairSpin p.1, p.2))
    ((measurable_fairSpin.comp measurable_fst).prodMk measurable_snd)
  have hroot : (uniform01.prod (ν (root d))).map
      (fun p : ℝ × A => (fairSpin p.1, p.2)) =
      (uniform01.map fairSpin).prod (ν (root d)) := by
    change (uniform01.prod (ν (root d))).map (Prod.map fairSpin id) = _
    rw [← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]
  rw [hroot] at hbase
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val))).map
          MeasurableEquiv.prodAssoc := by
      have hmf : Measurable (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1) :=
        (measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d))
      have hm : Measurable (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val)) :=
        (hmf.prodMk (by fun_prop)).prodMk (by fun_prop)
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    _ = _ := by
      rw [hbase]
      exact (measurePreserving_prodAssoc (uniform01.map fairSpin) (ν (root d))
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))).map_eq

theorem condIndepFun_noisy_factor_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun U => (fairSpin (U (root d)).1, (U (root d)).2))
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let G : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ × A) →
      (∀ c : Fin d, (BranchVertex c → IsingSpin) × (BranchVertex c → A)) :=
    fun p c => (branchFactor theta c (p.1, fun v => (p.2 c v).1),
      fun v => (p.2 c v).2)
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := condIndepFun_of_product_jointLaw
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    (uniform01.map fairSpin) (ν (root d))
    (Measure.infinitePi (fun c : Fin d =>
      Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))
    ((measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d)))
    (measurable_snd.comp (measurable_pi_apply (root d)))
    (show Measurable (fun U : TreeVertex d → ℝ × A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) from by fun_prop)
    (map_root_ownNoise_branch_family ν) id G measurable_id hG
  have hfun : (fun U : TreeVertex d → ℝ × A =>
      G (fairSpin (U (root d)).1, fun c v => U v.val)) =
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2)) := by
    funext U c
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  simpa only [Function.comp_def, id_eq, hfun] using h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_2_rd7e72b_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_condIndepFun_noisy_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply condIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot (U : TreeVertex d → ℝ × A) :
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d) =
      fairSpin (U (RootedBroadcast.root d)).1 := by
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.condIndepFun_noisy_factor_root_branches theta ν

theorem HasFreeIsingLaw.condIndepFun_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val)))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact (freeIsingMeasure_condIndepFun_noisy_root_branches theta ν).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin_3_rd7e72b_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measurePreserving_planted_relabel
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
    (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply (hμ.measurePreserving_relabel g).prod
  exact ⟨measurable_relabel g,
    Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩

theorem HasFreeIsingLaw.iCondIndepFun_relabel_noisy_branches
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun c z =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := iCondIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
    (hμ.iCondIndepFun_noisy_branches h0 h1 (fun _ => ν))
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

theorem HasFreeIsingLaw.condIndepFun_relabel_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d)
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun z => F (z.1 (g.toEquiv.symm (RootedBroadcast.root d)),
        z.2 (g.toEquiv.symm (RootedBroadcast.root d))))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val))))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from
      hF.comp (by fun_prop))
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      G (fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))) from hG.comp (by fun_prop))
    (hμ.condIndepFun_root_branch_observables h0 h1 (fun _ => ν) F G hF hG)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.iCondIndepFun_child_component_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : Fin d => fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a => F (p.1 (childComponentIndexVertex c a u))
          (p.2 (childComponentIndexVertex c a u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G (a : Fin d) : (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A) → (ComponentIndex a → B) :=
    fun p u => F (p.1 (v a u)) (p.2 (v a u))
  have hG (a : Fin d) : Measurable (G a) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A) => (p.1 (v a u), p.2 (v a u))) by fun_prop)
  have h := (hμ.iCondIndepFun_relabel_noisy_branches h0 h1 ν (prefixTreeAut c)).comp G hG
  exact h

theorem HasFreeIsingLaw.iCondIndepFun_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : {a : Fin d // c ≠ a} =>
        fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a.1 => F (p.1 (childComponentIndexVertex c a.1 u))
          (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  exact Kernel.iIndepFun.precomp Subtype.val_injective
    (hμ.iCondIndepFun_child_component_observations h0 h1 ν hF c)

theorem HasFreeIsingLaw.condIndepFun_own_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        F (p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))) (p.2 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun a : {a : Fin d // c ≠ a} => fun u : ComponentIndex a.1 =>
          F (p.1 (childComponentIndexVertex c a.1 u))
            (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A)) →
      (∀ a : {a : Fin d // c ≠ a}, ComponentIndex a.1 → B) :=
    fun p a u => F ((p a.1).1 (v a.1 u)) ((p a.1).2 (v a.1 u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A)) =>
          ((p a.1).1 (v a.1 u), (p a.1).2 (v a.1 u))) by fun_prop)
  have h := hμ.condIndepFun_relabel_root_branch_observables h0 h1 ν (prefixTreeAut c)
    (Function.uncurry F) G hF hG
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentFusionRecurrence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

theorem HasFreeIsingLaw.gaussian_component_information_fusion
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    gaussianComponentInformation μ t c ≤
      ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c -
        2 * (1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4 *
          (gaussianComponentInformation μ t c) ^ 2 + ((t : ℝ) + (t : ℝ) ^ 2) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  let r := RootedBroadcast.branchRoot c
  let I := {a : Fin d // c ≠ a}
  let X (a : I) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun u : ComponentIndex a.1 => F (z.1 (childComponentIndexVertex c a.1 u))
      (z.2 (childComponentIndexVertex c a.1 u))
  let Y (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun _ : Unit => F (z.1 r) (z.2 r)
  let S (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := z.1 r
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hS : Measurable S := (measurable_pi_apply r).comp measurable_fst
  have hX (a : I) : Measurable (X a) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      (z.1 (childComponentIndexVertex c a.1 u), z.2 (childComponentIndexVertex c a.1 u))) by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => (z.1 r, z.2 r)) by fun_prop)
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθ1 := Real.tanh_lt_one beta
  have hθlo : -1 ≤ Real.tanh beta := by linarith
  have hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X ρ :=
    hμ.iCondIndepFun_forward_child_observations hθlo hθ1.le (gaussianReal 0 t) hF c
  have hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun z a => X a z) ρ :=
    (hμ.condIndepFun_own_forward_child_observations hθlo hθ1.le
      (gaussianReal 0 t) hF c).comp
        (show Measurable (fun x : ℝ => fun _ : Unit => x) by fun_prop) measurable_id
  have hfair (s : IsingSpin) : ρ {z | S z = s} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r s
  have hbound (a : I) : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance] z| ≤
        Real.tanh beta :=
    hμ.selected_child_parent_abs_le hθ0 hθ1.le (gaussianReal 0 t) hF c a.1
  have hstrict (a : I) : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance] z| < 1 :=
    (hbound a).mono (fun _ hz => hz.trans_lt hθ1)
  have hsym (a : I) : (ρ.map (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap (X a) inferInstance])).map (fun x : ℝ => -x) =
      ρ.map (ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance]) :=
    hμ.selected_gaussian_posteriorLaw_neg_invariant t t (childComponentIndexVertex c a.1) r
  have hOwnStrict : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap Y inferInstance] z| < 1 := by
    filter_upwards [hμ.selected_singleton_gaussian_posterior hb t r] with z hz
    change |selectedPosterior ρ F (fun _ : Unit => r) r z| < 1
    rw [hz]
    exact Real.abs_tanh_lt_one _
  have hOwnSym : (ρ.map (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap Y inferInstance])).map (fun x : ℝ => -x) =
      ρ.map (ρ[fun z => spinSign (S z) | MeasurableSpace.comap Y inferInstance]) :=
    hμ.selected_gaussian_posteriorLaw_neg_invariant t t (fun _ : Unit => r) r
  have hcard : Fintype.card I = d - 1 := by
    dsimp [I]
    simp [Fintype.card_subtype_compl]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card I by rw [hcard]; omega)
  have hfamily := condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
    hS hX hCI hfair hstrict hsym hY hOwn hOwnStrict hOwnSym hab (hbound a) (hbound b) hθ1
  have hfield : MeasurableSpace.comap (fun z => (Y z, fun a => X a z)) inferInstance =
      selectedObservationField F (componentIndexVertex (c := c)) := by
    simpa only [Y, X, r, RootedBroadcast.branchRoot, selectedObservationField,
      Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
      MeasurableSpace.comap_process_pi, iSup_const] using
      (componentObservationField_eq_own_sup_children F c).symm
  rw [hfield] at hfamily
  have hchild (a : I) : (∫ z, (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap (X a) inferInstance] z) ^ 2 ∂ρ) =
      (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c :=
    hμ.selected_child_parent_secondMoment hθlo hθ1.le (gaussianReal 0 t) hF c a.1
  simp_rw [hchild] at hfamily
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hfamily
  have hown := hμ.selected_singleton_information_le hb t r
  change (∫ z, (ρ[fun z => spinSign (S z) |
    MeasurableSpace.comap Y inferInstance] z) ^ 2 ∂ρ) ≤ (t : ℝ) + (t : ℝ) ^ 2 at hown
  change gaussianComponentInformation μ t c ≤ _ at hfamily
  nlinarith [hfamily, hown]

theorem HasFreeIsingLaw.gaussian_component_critical_information_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d) :
    gaussianComponentInformation μ t c ≤
      Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4)) *
        Real.sqrt (t : ℝ) := by
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθpos : 0 < Real.tanh beta := by
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (le_of_not_gt h) hθ0
    simp [hz] at hcritical
  exact critical_information_upper_of_fusion hθpos (Real.tanh_lt_one beta)
    hcritical t.coe_nonneg ht (hμ.gaussian_component_information_fusion hd hb t c)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SiteInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem HasFreeIsingLaw.gaussian_site_information_le_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) (v : TreeVertex d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c := by
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  obtain ⟨g, hg⟩ := exists_treeAut_map (RootedBroadcast.root d) v
  have hroot : g.toEquiv.symm v = RootedBroadcast.root d := by rw [← hg]; simp
  have hregion : Set.range (fun i : TreeVertex d => g.toEquiv.symm (id i)) = Set.range id := by
    rw [Set.range_id]
    exact Set.range_eq_univ.mpr g.toEquiv.symm.surjective
  have h := selectedPosterior_identDistrib_of_range_relabel hμ (gaussianReal 0 t)
    hF id id v (RootedBroadcast.root d) g hregion hroot
  have heq := (h.comp (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)).integral_eq
  change (∫ z, (PlantedSymmetry.posteriorMagnetization
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
    ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) = _ at heq
  rw [heq]
  exact hμ.gaussian_root_information_le_component hb t c

theorem HasFreeIsingLaw.gaussian_site_critical_information_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      ((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt (t : ℝ) := by
  let c : Fin d := ⟨0, by omega⟩
  have h := (hμ.gaussian_site_information_le_component hb t c v).trans
    (mul_le_mul_of_nonneg_left
      (hμ.gaussian_component_critical_information_upper hd hb hcritical t ht c)
      (by positivity : 0 ≤ 1 + (Real.tanh beta) ^ 2))
  simpa only [mul_assoc] using h

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_critical_secondMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ z, (infiniteGibbsSpinMean beta v (PlantedSymmetry.observation t z)) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      ((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt (t : ℝ) := by
  have hEq := integral_congr_ae
    ((hμ.infiniteGibbsSpinMean_eq_posterior t v).fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hEq
  rw [hEq]
  exact hμ.gaussian_site_critical_information_upper hd hb hcritical t ht v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceUniformEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

open PlantedSymmetry GaussianTreeCovariance

theorem integral_brownian_ising_observation_eq_gaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0)
    (f : (TreeVertex d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      f (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))
      ∂μ.prod (Measure.infinitePi ν)) =
      ∫ p, f (observation t p) ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hL : HasLaw T (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (μ.prod (Measure.infinitePi ν)) := ⟨hT.measurable.aemeasurable, hT.map_eq⟩
  exact hL.integral_comp ((hf.comp (measurable_observation t)).aestronglyMeasurable)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceCriticalEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_secondMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ((1 + Real.tanh beta ^ 2) *
        Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))) *
          Real.sqrt (t : ℝ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rw [integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
    (fun y => infiniteGibbsSpinMean beta v y ^ 2)
    ((measurable_infiniteGibbsSpinMean beta v).pow_const 2)]
  exact hμ.infiniteGibbsSpinMean_critical_secondMoment hd hb hcritical t ht v

lemma HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (0, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) = 0 := by
  have h := hμ.infiniteGibbsSpinMean_brownian_critical_secondMoment
    hd hb hcritical ν hB hmB 0 (by norm_num) v
  simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] at h
  unfold brownianIsingObservationR
  dsimp only
  rw [Real.toNNReal_zero]
  exact le_antisymm h (integral_nonneg (fun p => sq_nonneg _))

end Problem367

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero_oai.{u_1} := @OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero_oai.{u_1}
