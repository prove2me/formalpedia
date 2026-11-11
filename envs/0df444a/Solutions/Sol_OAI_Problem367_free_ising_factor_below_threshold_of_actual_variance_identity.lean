-- Prove2me | solution 1 for OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:57.718197+00:00
-- url     : https://prove2.me/submissions/39e8172b-3fc9-4ef5-b0a0-b7738fb8857e

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_critical_root_variance_zero_of_noise_bound
import Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_exists_noise_energy_long_constants
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_siteVariance_eq_zero_of_subcritical_actual_variance_identity

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_PosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.brownian_past_posterior_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let m := ρ[fun p => spinSign (p.1 v) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance]
    ∀ᵐ p ∂ρ, m p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin : Measurable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) :=
    hsign.comp (measurable_pi_apply v)
  have hspini : Integrable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) μ := by
    apply Integrable.of_bound hspin.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma v <;> norm_num [spinSign, hs]
  have hpull := condExp_comp_measurePreserving_comap hT
    (hspin.comp measurable_fst).stronglyMeasurable
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) v)
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v))
    (Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))) hspin hspini t
  have hb := hμ.gaussian_posterior_field_bound hbeta t v
  rw [← hT.map_eq] at hb
  have hb' := ae_of_ae_map hT.measurable.aemeasurable hb
  rw [hT.map_eq] at hb'
  dsimp only
  filter_upwards [hpast, hpull, hb'] with p hpast hpull hb
  change _ = posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v (T p)
    at hpull
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_DiagonalRecovery
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Problem367

theorem exists_eq_dirac_of_selfProd_ae_eq
    {X : Type*} [MeasurableSpace X] (nu : Measure X)
    [IsProbabilityMeasure nu]
    (h : ∀ᵐ p ∂nu.prod nu, p.1 = p.2) :
    ∃ x : X, nu = Measure.dirac x := by
  obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod h).exists
  refine ⟨x, ?_⟩
  have hconst : (fun y : X => y) =ᵐ[nu] (fun _ => x) := by
    filter_upwards [hx] with y hy using hy.symm
  simpa using Measure.map_congr hconst

theorem exists_measurable_dirac_of_forall
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (kappa : Kernel W X)
    (h : ∀ w, ∃ x : X, kappa w = Measure.dirac x) :
    ∃ F : W → X, Measurable F ∧ ∀ w, kappa w = Measure.dirac (F w) := by
  choose F hF using h
  refine ⟨F, ?_, hF⟩
  intro s hs
  have heq : F ⁻¹' s = (fun w => kappa w s) ⁻¹' {1} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff, hF w, Measure.dirac_apply' _ hs]
    exact (indicator_eq_one_iff_mem ENNReal).symm
  rw [heq]
  exact kappa.measurable_coe hs (measurableSet_singleton 1)

theorem exists_measurable_dirac_of_selfProd_ae_eq
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (mu : Measure W) (kappa : Kernel W X) [IsMarkovKernel kappa]
    (h : ∀ᵐ w ∂mu, ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2) :
    ∃ F : W → X, Measurable F ∧ ∀ᵐ w ∂mu, kappa w = Measure.dirac (F w) := by
  classical
  let good : Set W := {w | (kappa ×ₖ kappa) w (diagonal X)ᶜ = 0}
  have hgood : MeasurableSet good :=
    ((kappa ×ₖ kappa).measurable_coe measurableSet_diagonal.compl)
      (measurableSet_singleton 0)
  have hgood_ae : ∀ᵐ w ∂mu, w ∈ good := by
    filter_upwards [h] with w hw
    change (kappa ×ₖ kappa) w (diagonal X)ᶜ = 0
    rw [Kernel.prod_apply]
    exact hw
  let base : X := Classical.choice inferInstance
  let modified := Kernel.piecewise hgood kappa
    (Kernel.deterministic (fun _ : W => base) measurable_const)
  have hmodified : ∀ w, ∃ x : X, modified w = Measure.dirac x := by
    intro w
    by_cases hw : w ∈ good
    · have hdiag : ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2 := by
        change (kappa w).prod (kappa w) {p | ¬p.1 = p.2} = 0
        simpa only [good, mem_ofPred_eq, Kernel.prod_apply, diagonal, compl_ofPred] using hw
      obtain ⟨x, hx⟩ := exists_eq_dirac_of_selfProd_ae_eq (kappa w) hdiag
      exact ⟨x, by simpa [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw] using hx⟩
    · exact ⟨base, by simp [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw]⟩
  obtain ⟨F, hF, hdirac⟩ := exists_measurable_dirac_of_forall modified hmodified
  refine ⟨F, hF, ?_⟩
  filter_upwards [hgood_ae] with w hw
  simpa [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw] using hdirac w

theorem ae_eq_recovery_of_ae_dirac
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] (mu : Measure W) (kappa : Kernel W X)
    {F : W → X} (hF : Measurable F)
    (h : ∀ᵐ w ∂mu, kappa w = Measure.dirac (F w)) :
    ∀ᵐ p ∂mu ⊗ₘ kappa, p.2 = F p.1 := by
  apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun measurable_snd (hF.comp measurable_fst))
  filter_upwards [h] with w hw
  rw [hw]
  simp

theorem exists_measurable_recovery_of_conditionalCopies
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (mu : Measure W) [SFinite mu] (kappa : Kernel W X) [IsMarkovKernel kappa]
    (h : ∀ᵐ p ∂mu ⊗ₘ (kappa ×ₖ kappa), p.2.1 = p.2.2) :
    ∃ F : W → X, Measurable F ∧
      (∀ᵐ w ∂mu, kappa w = Measure.dirac (F w)) ∧
      ∀ᵐ p ∂mu ⊗ₘ kappa, p.2 = F p.1 := by
  have hcopies : ∀ᵐ w ∂mu, ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2 := by
    simpa only [Kernel.prod_apply] using Measure.ae_ae_of_ae_compProd h
  obtain ⟨F, hF, hdirac⟩ := exists_measurable_dirac_of_selfProd_ae_eq mu kappa hcopies
  exact ⟨F, hF, hdirac, ae_eq_recovery_of_ae_dirac mu kappa hF hdirac⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_RecoveryEquivariance
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Problem367

variable {W X G : Type*} [MeasurableSpace W] [MeasurableSpace X]

theorem ae_equivariant_of_joint_recovery [MeasurableEq X]
    {η : Measure (W × X)} {μ : Measure W}
    {T : W → W} {S : X → X} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ)
    (hT : Measurable T) (hS : Measurable S) (hF : Measurable F)
    (hjoint : Measure.QuasiMeasurePreserving
      (fun p : W × X => (T p.1, S p.2)) η η)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    ∀ᵐ w ∂μ, F (T w) = S (F w) := by
  rw [← hμ]
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_eq_fun (hF.comp hT) (hS.comp hF))).2
  have htrans := hjoint.ae hrecover
  filter_upwards [hrecover, htrans] with p hp hTp
  exact hTp.symm.trans (congrArg S hp)

theorem ae_equivariant_family_of_joint_recovery [MeasurableEq X]
    {η : Measure (W × X)} {μ : Measure W}
    {T : G → W → W} {S : G → X → X} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ)
    (hT : ∀ g, Measurable (T g)) (hS : ∀ g, Measurable (S g))
    (hF : Measurable F)
    (hjoint : ∀ g, Measure.QuasiMeasurePreserving
      (fun p : W × X => (T g p.1, S g p.2)) η η)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    ∀ g, ∀ᵐ w ∂μ, F (T g w) = S g (F w) :=
  fun g => ae_equivariant_of_joint_recovery hμ (hT g) (hS g) hF
    (hjoint g) hrecover

theorem map_eq_second_marginal_of_joint_recovery
    {η : Measure (W × X)} {μ : Measure W} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ) (hF : Measurable F)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    Measure.map F μ = Measure.map Prod.snd η := by
  rw [← hμ, Measure.map_map hF measurable_fst]
  apply Measure.map_congr
  filter_upwards [hrecover] with p hp
  exact hp.symm

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Transfer
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem measurable_vertexSampler {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) : Measurable (vertexSampler (d := d) f) := by
  exact Measurable.of_eval fun vertex => hf.comp (measurable_pi_apply vertex)

theorem map_vertexSampler_labelMeasure {d : ℕ} {α : Type*}
    [MeasurableSpace α] {f : ℝ → α} (hf : Measurable f) :
    Measure.map (vertexSampler (d := d) f) (labelMeasure d) =
      Measure.infinitePi (fun _ : TreeVertex d => Measure.map f uniform01) := by
  exact Measure.infinitePi_map_pi (fun _ => uniform01) (fun _ => hf)

theorem isFactorOfIID_of_product_sampler {d : ℕ} {theta : ℝ} {α : Type*}
    [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : ℝ → α) (hf : Measurable f) (hf_law : Measure.map f uniform01 = ν)
    (H : (TreeVertex d → α) → (TreeVertex d → IsingSpin))
    (hH : Measurable H)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map H (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (hEquiv : ∀ g : TreeAut d,
      ∀ᵐ W ∂Measure.infinitePi (fun _ : TreeVertex d => ν),
        H (relabel g W) = relabel g (H W)) :
    IsFactorOfIID d theta := by
  have hs := measurable_vertexSampler (d := d) hf
  have hslaw : Measure.map (vertexSampler (d := d) f) (labelMeasure d) =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    rw [map_vertexSampler_labelMeasure hf, hf_law]
  refine ⟨H ∘ vertexSampler f, hH.comp hs, ?_, ?_⟩
  · rw [← Measure.map_map hH hs, hslaw]
    exact hLaw
  · intro g
    have h : ∀ᵐ W ∂Measure.map (vertexSampler (d := d) f) (labelMeasure d),
        H (relabel g W) = relabel g (H W) := by
      rw [hslaw]
      exact hEquiv g
    filter_upwards [ae_of_ae_map hs.aemeasurable h] with U hU
    simpa only [Function.comp_apply, vertexSampler_relabel] using hU

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FactorRecovery
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem exists_ae_equivariant_recovery_of_conditionalCopies
    {W X G : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (μ : Measure W) [SFinite μ] (κ : Kernel W X) [IsMarkovKernel κ]
    (T : G → W → W) (S : G → X → X)
    (hT : ∀ g, Measurable (T g)) (hS : ∀ g, Measurable (S g))
    (hjoint : ∀ g, Measure.QuasiMeasurePreserving
      (fun p : W × X => (T g p.1, S g p.2)) (μ ⊗ₘ κ) (μ ⊗ₘ κ))
    (hcopies : ∀ᵐ p ∂μ ⊗ₘ (κ ×ₖ κ), p.2.1 = p.2.2) :
    ∃ F : W → X, Measurable F ∧
      (∀ᵐ w ∂μ, κ w = Measure.dirac (F w)) ∧
      Measure.map F μ = Measure.map Prod.snd (μ ⊗ₘ κ) ∧
      ∀ g, ∀ᵐ w ∂μ, F (T g w) = S g (F w) := by
  obtain ⟨F, hF, hdirac, hgraph⟩ :=
    exists_measurable_recovery_of_conditionalCopies μ κ hcopies
  have hfst : Measure.map Prod.fst (μ ⊗ₘ κ) = μ :=
    Measure.fst_compProd μ κ
  exact ⟨F, hF, hdirac,
    map_eq_second_marginal_of_joint_recovery hfst hF hgraph,
    ae_equivariant_family_of_joint_recovery hfst hT hS hF hjoint hgraph⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CompensatedSquareEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem secondMoment_le_of_ae_abs_le [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {t H : ℝ}
    (hInt : Integrable (fun ω => (X t ω) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ, |X t ω| ≤ H) :
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hsq : ∀ᵐ ω ∂μ, (X t ω) ^ 2 ≤ H ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).2 hω
  calc
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ ∫ _ : Ω, H ^ 2 ∂μ := integral_mono_ae hInt (integrable_const _) hsq
    _ = H ^ 2 := by simp

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
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

lemma measurable_fairSpinFactor (d : ℕ) : Measurable (fairSpinFactor d) := by
  exact Measurable.of_eval (fun vertex => measurable_fairSpin.comp (measurable_pi_apply vertex))

lemma fairSpinFactor_relabel (d : ℕ) (g : TreeAut d) (U : TreeVertex d → ℝ) :
    fairSpinFactor d (relabel g U) = relabel g (fairSpinFactor d U) := rfl

private lemma fairSpin_measurable_singleton (a : IsingSpin) : MeasurableSet ({a} : Set IsingSpin) := by
  trivial

lemma fairSpinFactor_cylinder (d : ℕ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    (Measure.map (fairSpinFactor d) (labelMeasure d))
      {x | ∀ v ∈ D, x v = eta v} = (1 / 2 : ENNReal) ^ D.card := by
  classical
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    exact MeasurableSet.pi D.countable_toSet (fun v hv => fairSpin_measurable_singleton (eta v))
  rw [Measure.map_apply (measurable_fairSpinFactor d) hmeas]
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01))
    (Set.pi (D : Set (TreeVertex d)) (fun v => fairSpin ⁻¹' {eta v})) = _
  rw [Measure.infinitePi_pi _ (fun v _ => measurable_fairSpin (fairSpin_measurable_singleton (eta v)))]
  simp [fairSpin_mass]

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

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

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

local instance localInst_r67423b_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

lemma ConnectedFinset.inducedEdges_image_snd {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    (inducedEdges D).image Prod.snd = D.erase r := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨⟨u, w⟩, huw, hwv⟩ := Finset.mem_image.mp hv
    have huw' : (u ∈ D ∧ w ∈ D) ∧ treeAdj u w ∧ u.1.length < w.1.length := by
      exact (mem_inducedEdges_8911 D u w).mp huw
    change w = v at hwv
    subst w
    apply Finset.mem_erase.mpr
    refine ⟨?_, huw'.1.2⟩
    intro heq
    subst v
    have := hmin u huw'.1.1
    omega
  · intro hv
    obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
    apply Finset.mem_image.mpr
    refine ⟨(parentVertex v, v), ?_, rfl⟩
    have hp := hD.parent_mem_of_ne_min hr hmin hv hne
    have hnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hne
    have hpos : 0 < v.1.length := List.length_pos_iff.mpr hnil
    have hadj := treeAdj_parentVertex hnil
    apply (mem_inducedEdges_8911 D _ _).mpr
    refine ⟨⟨hp, hv⟩, hadj, ?_⟩
    rw [parentVertex_length]
    omega

lemma ConnectedFinset.inducedEdges_card_add_one {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (inducedEdges D).card + 1 = D.card := by
  classical
  obtain ⟨r, hr, hmin⟩ := D.exists_min_image (fun v => v.1.length) hD.1
  have himage := hD.inducedEdges_image_snd hr hmin
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injOn (inducedEdges_snd_injOn D), Finset.card_erase_of_mem hr] at hcard
  have hpos : 0 < D.card := Finset.card_pos.mpr hD.1
  omega

end Problem367

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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ObservableDisintegration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservableDisintegration

variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X]

omit [StandardBorelSpace X] [Nonempty X] in
theorem snd_graphLaw (P : Measure X) {Z : X → W} (hZ : Measurable Z) :
    (graphLaw P Z).snd = P := by
  change (P.map (fun x => (Z x, x))).map Prod.snd = P
  rw [Measure.map_map measurable_snd (measurable_graphMap hZ)]
  exact Measure.map_id

theorem measurePreserving_snd_kernel (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z) :
    MeasurePreserving Prod.snd ((P.map Z) ⊗ₘ kernel P Z) P := by
  refine ⟨measurable_snd, ?_⟩
  rw [compProd_kernel P hZ]
  exact snd_graphLaw P hZ

theorem ae_observable_eq_input [MeasurableEq W]
    (P : Measure X) [IsFiniteMeasure P] {Z : X → W} (hZ : Measurable Z) :
    ∀ᵐ p ∂(P.map Z) ⊗ₘ kernel P Z, Z p.2 = p.1 := by
  rw [compProd_kernel P hZ]
  apply (ae_map_iff (hZ.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun (hZ.comp measurable_snd) measurable_fst)).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

end Problem367.ObservableDisintegration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

lemma threshold_iff_branching_sq {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) ≤ 1 := le_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma tanh_threshold_iff_branching_sq {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * Real.tanh beta ^ 2 ≤ 1 :=
  threshold_iff_branching_sq hd (tanh_nonneg_of_beta_nonneg hbeta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_SharedInnovationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter

namespace Problem367

theorem discrepancy_secondMoment_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h h' : Ω → ℝ} {H : ℝ}
    (hmeas : AEStronglyMeasurable (fun ω => h ω - h' ω) μ)
    (hbound : ∀ᵐ ω ∂μ, |h ω - h' ω| ≤ H) :
    MemLp (fun ω => h ω - h' ω) 2 μ ∧
      0 ≤ (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ∧
      (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hLp : MemLp (fun ω => h ω - h' ω) 2 μ :=
    MemLp.of_bound hmeas H (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hLp, integral_nonneg (fun _ => sq_nonneg _),
    DiscrepancyEnergy.secondMoment_le_of_ae_abs_le
      (X := fun _ ω => h ω - h' ω) (t := 0) hLp.integrable_sq hbound⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ContinuousRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter TopologicalSpace

namespace Problem367

theorem ae_eq_of_integral_sq_sub_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hInt : Integrable (fun ω => (f ω - g ω) ^ 2) μ)
    (hzero : (∫ ω, (f ω - g ω) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω - g ω))
    hInt).mp hzero
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Recovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.SpinRecovery

theorem measurable_decode : Measurable decode := by
  unfold decode
  apply Measurable.ite
  · exact measurableSet_tendsto (𝓝 (-1 : ℝ))
      (f := fun (n : ℕ) (x : ℕ → ℝ) => x n / (n : ℝ))
      (by intro n; fun_prop)
  · exact measurable_const
  · exact measurable_const

theorem decode_of_tendsto {x : ℕ → ℝ} {s : IsingSpin}
    (h : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (spinSign s))) :
    decode x = s := by
  cases s with
  | neg =>
      simp only [spinSign] at h
      simp [decode, h]
  | pos =>
      have hn : ¬ Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (-1 : ℝ)) := by
        intro hm
        have he : (-1 : ℝ) = 1 := tendsto_nhds_unique hm h
        norm_num at he
      simp [decode, hn]

theorem decode_signal_add_noise (s : IsingSpin) {z : ℕ → ℝ}
    (hz : Tendsto (fun n : ℕ => z n / (n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    decode (fun n : ℕ => (n : ℝ) * spinSign s + z n) = s := by
  apply decode_of_tendsto
  have he : (fun n : ℕ => ((n : ℝ) * spinSign s + z n) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => spinSign s + z n / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  apply (tendsto_congr' he).2
  simpa using tendsto_const_nhds.add hz

theorem measurable_decodeArray {V : Type*} :
    Measurable (decodeArray (V := V)) := by
  exact Measurable.of_eval fun vertex =>
    measurable_decode.comp (measurable_pi_apply vertex)

theorem decodeArray_relabel {d : ℕ} (g : TreeAut d)
    (x : TreeVertex d → ℕ → ℝ) :
    decodeArray (relabel g x) = relabel g (decodeArray x) := rfl

end Problem367.SpinRecovery

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ObservationFactorRecovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem isFactorOfIID_of_equal_observation_conditionalCopies
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) (TreeVertex d → ℕ → ℝ))
    [IsMarkovKernel kappa]
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        (relabel g p.1, relabel g p.2))
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa))
    (hcopies : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), p.2.1 = p.2.2) :
    IsFactorOfIID d theta := by
  obtain ⟨F, hF, _, hmap, heq⟩ :=
    exists_ae_equivariant_recovery_of_conditionalCopies
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa
      (fun g : TreeAut d => relabel g) (fun g : TreeAut d => relabel g)
      measurable_relabel measurable_relabel hjoint hcopies
  obtain ⟨sample, hsample, hsampleLaw⟩ := exists_uniform01_sampler nu
  apply isFactorOfIID_of_product_sampler nu sample hsample hsampleLaw
    (SpinRecovery.decodeArray ∘ F) (SpinRecovery.measurable_decodeArray.comp hF)
  · rw [← Measure.map_map SpinRecovery.measurable_decodeArray hF, hmap,
      Measure.map_map SpinRecovery.measurable_decodeArray measurable_snd]
    exact hLaw
  · intro g
    filter_upwards [heq g] with w hw
    change SpinRecovery.decodeArray (F (relabel g w)) =
      relabel g (SpinRecovery.decodeArray (F w))
    rw [hw, SpinRecovery.decodeArray_relabel]

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_InnovationFactorRecovery
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem observations_ae_eq_of_common_innovation_and_measurable_fields
    {O : Type*} [MeasurableSpace O] {mu : Measure O} [SFinite mu]
    {h h' : ℝ≥0 → O → ℝ} {X Y W : ℕ → O → ℝ}
    (hm : Measurable (fun q : ℝ × O => Real.tanh (h q.1.toNNReal q.2)))
    (hm' : Measurable (fun q : ℝ × O => Real.tanh (h' q.1.toNNReal q.2)))
    (heq : ∀ t, h t =ᵐ[mu] h' t)
    (hX : ∀ n, ∀ᵐ p ∂mu,
      X n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂mu,
      Y n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    ∀ n, X n =ᵐ[mu] Y n := by
  have htime : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ p ∂mu,
      Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p) := by
    apply Filter.Eventually.of_forall
    intro t
    filter_upwards [heq t.toNNReal] with p hp
    rw [hp]
  have hsample : ∀ᵐ p ∂mu, ∀ᵐ t ∂(volume : Measure ℝ),
      Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p) :=
    (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := mu)
      (p := fun t p => Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p))
      (measurableSet_eq_fun hm hm')).1 htime
  intro n
  filter_upwards [hsample, hX n, hY n] with p hp hx hy
  rw [hx, hy]
  congr 1
  unfold nnrealTimePrimitive
  apply intervalIntegral.integral_congr_ae
  exact hp.mono (fun _ ht _ => ht)

theorem observations_ae_eq_of_common_innovation_and_measurable_field_zero
    {O : Type*} [MeasurableSpace O] {mu : Measure O} [SFinite mu]
    {h h' : ℝ≥0 → O → ℝ} {X Y W : ℕ → O → ℝ}
    (hm : Measurable (fun q : ℝ × O => Real.tanh (h q.1.toNNReal q.2)))
    (hm' : Measurable (fun q : ℝ × O => Real.tanh (h' q.1.toNNReal q.2)))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2) mu)
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2 ∂mu) = 0)
    (hX : ∀ n, ∀ᵐ p ∂mu,
      X n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂mu,
      Y n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    ∀ n, X n =ᵐ[mu] Y n := by
  apply observations_ae_eq_of_common_innovation_and_measurable_fields hm hm' _ hX hY
  exact fun t => ae_eq_of_integral_sq_sub_eq_zero (hInt t) (hzero t)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProjectedObservationRecovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

private theorem measurable_time_copy_fst
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × (W × X) → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × (X × X)) => F (q.1, (q.2.1, q.2.2.1))) :=
  hF.comp (by fun_prop)

private theorem measurable_time_copy_snd
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × (W × X) → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × (X × X)) => F (q.1, (q.2.1, q.2.2.2))) :=
  hF.comp (by fun_prop)

theorem conditionalCopies_ae_eq_projected
    {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableEq Y]
    (mu : Measure W) [SFinite mu] (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (E : X → Y) (hE : Measurable E)
    (hcopy : ∀ᵐ p ∂mu ⊗ₘ (kappa ×ₖ kappa), E p.2.1 = E p.2.2) :
    ∀ᵐ p ∂mu ⊗ₘ ((kappa.map E) ×ₖ (kappa.map E)), p.2.1 = p.2.2 := by
  rw [Kernel.map_prod_map kappa kappa hE hE, Measure.compProd_map (hE.prodMap hE)]
  apply (ae_map_iff (measurable_id.prodMap (hE.prodMap hE)).aemeasurable
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd))).2
  exact hcopy

theorem isFactorOfIID_of_projected_observation_conditionalCopies
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (hcopies : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), E p.2.1 = E p.2.2) :
    IsFactorOfIID d theta := by
  let : IsMarkovKernel (kappa.map E) := Kernel.IsMarkovKernel.map kappa hE
  have hproject : (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E =
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map id E) := Measure.compProd_map hE
  apply isFactorOfIID_of_equal_observation_conditionalCopies nu (kappa.map E)
  · have hdecode : Measurable (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        SpinRecovery.decodeArray p.2) :=
      SpinRecovery.measurable_decodeArray.comp measurable_snd
    rw [hproject, Measure.map_map hdecode (measurable_id.prodMap hE)]
    exact hLaw
  · intro g
    have hpres : MeasurePreserving (Prod.map (relabel g) (S g))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa) :=
      ⟨(measurable_relabel g).prodMap (hS g), hjoint g⟩
    have heq : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
        (Prod.map id E) ((Prod.map (relabel g) (S g)) p) =
          (Prod.map (relabel g) (relabel g)) ((Prod.map id E) p) :=
      Filter.Eventually.of_forall (fun p => Prod.ext rfl (hEquiv g p.2))
    have hp := FactorTransport.map_invariant_of_ae_equivariant hpres
      ((measurable_relabel g).prodMap (measurable_relabel g))
      (measurable_id.prodMap hE) heq
    rw [← hproject] at hp
    exact (show MeasurePreserving (Prod.map (relabel g) (relabel g))
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E) from
      ⟨(measurable_relabel g).prodMap (measurable_relabel g), hp⟩).quasiMeasurePreserving
  · exact conditionalCopies_ae_eq_projected _ kappa E hE hcopies

theorem isFactorOfIID_of_projected_observation_reference_collapse
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (hroot : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), E p.2.1 o n = E p.2.2 o n) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_observation_conditionalCopies
    nu kappa E hE S hS hEquiv hLaw hjoint
  have hcoord : ∀ v n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      (kappa ×ₖ kappa), E p.2.1 v n = E p.2.2 v n := by
    intro v n
    obtain ⟨g, hg⟩ := exists_treeAut_map v o
    have hgo : g.toEquiv.symm o = v := by rw [← hg, Equiv.symm_apply_apply]
    have hT : MeasurePreserving (ObservationCopyStationarity.arrayRelabelEquiv (A := A) g)
        (Measure.infinitePi (fun _ : TreeVertex d => nu))
        (Measure.infinitePi (fun _ : TreeVertex d => nu)) :=
      ⟨measurable_relabel g, Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩
    have hi := conditionalCopies_invariant
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa
      (ObservationCopyStationarity.arrayRelabelEquiv g) (hS g) hT
      (by simpa [ObservationCopyStationarity.arrayRelabelEquiv] using hjoint g)
    have hpres : MeasurePreserving (Prod.map (relabel g) (Prod.map (S g) (S g)))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) :=
      ⟨(measurable_relabel g).prodMap ((hS g).prodMap (hS g)), hi⟩
    filter_upwards [hpres.quasiMeasurePreserving.ae (hroot n)] with p hp
    change E (S g p.2.1) o n = E (S g p.2.2) o n at hp
    rw [hEquiv, hEquiv] at hp
    simpa only [relabel, hgo] using hp
  have hall : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      (kappa ×ₖ kappa), ∀ v n, E p.2.1 v n = E p.2.2 v n :=
    ae_all_iff.2 (fun v => ae_all_iff.2 (hcoord v))
  filter_upwards [hall] with p hp
  exact funext (fun v => funext (hp v))

theorem isFactorOfIID_of_projected_innovation_field_zero
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (h h' : ℝ≥0 → ((TreeVertex d → A) × (X × X)) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h t.toNNReal p))))
    (hm' : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h' t.toNNReal p))))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)))
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2
      ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) = 0)
    (hX : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa),
      E p.2.1 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa),
      E p.2.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_observation_reference_collapse
    nu kappa E hE S hS hEquiv o hLaw hjoint
  exact observations_ae_eq_of_common_innovation_and_measurable_field_zero
    hm hm' hInt hzero hX hY

theorem isFactorOfIID_of_innovation_comparison
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (H : ℝ≥0 → ((TreeVertex d → A) × X) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (H t.toNNReal p))))
    (hInt : ∀ t, Integrable (fun p => (H t (p.1, p.2.1) - H t (p.1, p.2.2)) ^ 2)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)))
    (hzero : ∀ t, (∫ p, (H t (p.1, p.2.1) - H t (p.1, p.2.2)) ^ 2
      ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) = 0)
    (hInnovation : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
      E p.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (H t p)) n p) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_innovation_field_zero nu kappa E hE S hS hEquiv
    o hLaw hjoint (fun t p => H t (p.1, p.2.1))
    (fun t p => H t (p.1, p.2.2)) W
  · exact measurable_time_copy_fst hm
  · exact measurable_time_copy_snd hm
  · exact hInt
  · exact hzero
  · intro n
    exact (measurePreserving_conditionalCopy_fst
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa).quasiMeasurePreserving.ae
        (hInnovation n)
  · intro n
    exact (measurePreserving_conditionalCopy_snd
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa).quasiMeasurePreserving.ae
        (hInnovation n)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ObservableFactorRecovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

private theorem measurable_time_state
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × X → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × X) => F (q.1, q.2.2)) :=
  hF.comp (by fun_prop)

theorem isFactorOfIID_of_stationary_innovation_observable
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (P : Measure X) [IsProbabilityMeasure P]
    (Z : X → TreeVertex d → A) (hZ : Measurable Z)
    (hinput : P.map Z = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, MeasurePreserving (S g) P P)
    (hEeq : ∀ g x, E (S g x) = relabel g (E x))
    (hZeq : ∀ g, ∀ᵐ x ∂P, Z (S g x) = relabel g (Z x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta (P.map (fun x => SpinRecovery.decodeArray (E x))))
    (H : ℝ≥0 → X → ℝ) (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) x => Real.tanh (H t.toNNReal x))))
    (hInt : ∀ t, Integrable (fun p => (H t p.2.1 - H t p.2.2) ^ 2)
      ((P.map Z) ⊗ₘ ((ObservableDisintegration.kernel P Z) ×ₖ
        (ObservableDisintegration.kernel P Z))))
    (hzero : ∀ t, (∫ p, (H t p.2.1 - H t p.2.2) ^ 2
      ∂(P.map Z) ⊗ₘ ((ObservableDisintegration.kernel P Z) ×ₖ
        (ObservableDisintegration.kernel P Z))) = 0)
    (hInnovation : ∀ n, ∀ᵐ x ∂P,
      E x o n = W n (Z x) + nnrealTimePrimitive (fun t x => Real.tanh (H t x)) n x) :
    IsFactorOfIID d theta := by
  let kappa := ObservableDisintegration.kernel P Z
  have hproj : MeasurePreserving Prod.snd
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa) P := by
    simpa only [hinput] using ObservableDisintegration.measurePreserving_snd_kernel P hZ
  refine isFactorOfIID_of_innovation_comparison nu kappa E hE S
    (fun g => (hS g).measurable) hEeq o ?_ ?_
    (fun t p => H t p.2) W ?_ ?_ ?_ ?_
  · have hdecode : Measurable (fun x => SpinRecovery.decodeArray (E x)) :=
      SpinRecovery.measurable_decodeArray.comp hE
    change HasFreeIsingLaw theta
      (Measure.map ((fun x => SpinRecovery.decodeArray (E x)) ∘ Prod.snd)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa))
    rw [← Measure.map_map hdecode measurable_snd, hproj.map_eq]
    exact hLaw
  · intro g
    simpa only [hinput] using ObservableDisintegration.joint_kernel_invariant P hZ
      (measurable_relabel g) (hS g) (hZeq g)
  · exact measurable_time_state hm
  · simpa only [hinput] using hInt
  · simpa only [hinput] using hzero
  · intro n
    have hsupp : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
        Z p.2 = p.1 := by
      simpa only [hinput] using ObservableDisintegration.ae_observable_eq_input P hZ
    filter_upwards [hproj.quasiMeasurePreserving.ae (hInnovation n), hsupp] with p hp hs
    rw [hs] at hp
    exact hp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ZeroFactor
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

lemma freeCylinderWeight_zero_of_card {d : ℕ} (D : Finset (TreeVertex d))
    (hcard : (inducedEdges D).card + 1 = D.card) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight 0 D eta = (1 / 2 : ENNReal) ^ D.card := by
  simp only [freeCylinderWeight, neg_zero, ite_self, add_zero, Finset.prod_const]
  rw [← pow_succ', hcard, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpinFactor_hasFreeIsingLaw_of_card {d : ℕ}
    (hcard : ∀ D : Finset (TreeVertex d), ConnectedFinset D →
      (inducedEdges D).card + 1 = D.card) :
    HasFreeIsingLaw 0 (Measure.map (fairSpinFactor d) (labelMeasure d)) := by
  intro D hD eta
  rw [fairSpinFactor_cylinder, freeCylinderWeight_zero_of_card D (hcard D hD)]

lemma isFactorOfIID_zero_of_card (d : ℕ)
    (hcard : ∀ D : Finset (TreeVertex d), ConnectedFinset D →
      (inducedEdges D).card + 1 = D.card) : IsFactorOfIID d 0 := by
  refine ⟨fairSpinFactor d, measurable_fairSpinFactor d,
    fairSpinFactor_hasFreeIsingLaw_of_card hcard, ?_⟩
  intro g
  exact Filter.Eventually.of_forall (fairSpinFactor_relabel d g)

theorem isFactorOfIID_zero (d : ℕ) : IsFactorOfIID d 0 := by
  exact isFactorOfIID_zero_of_card d (fun _ hD => hD.inducedEdges_card_add_one)

theorem free_ising_factor_beta_zero (d : ℕ) : IsFactorOfIID d (Real.tanh 0) := by
  simpa only [Real.tanh_zero] using isFactorOfIID_zero d

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_NoiseSlope
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_tendsto_zero_of_tail_tsum_ne_top (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → (∑' n, μ {ω | ε ≤ |X n ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hsmall : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ∀ᶠ n in atTop, |X n ω| < 1 / (k + 1 : ℝ) := by
    intro k
    have h := ae_eventually_notMem (hX (1 / (k + 1 : ℝ)) (by positivity))
    simpa only [Set.mem_ofPred_eq, not_le] using h
  filter_upwards [ae_all_iff.mpr hsmall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).trans hk⟩

theorem ae_tendsto_zero_of_summable_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → Summable (fun n => μ.real {ω | ε ≤ |X n ω|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tail_tsum_ne_top X
  intro ε hε
  have h := (hX ε hε).tsum_ofReal_ne_top
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem ae_tendsto_zero_of_exp_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → ∃ C c : ℝ, 0 < c ∧
      ∀ n, μ.real {ω | ε ≤ |X n ω|} ≤ C * Real.exp (-(n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_tail X
  intro ε hε
  obtain ⟨C, c, hc, hbound⟩ := hX ε hε
  have hsum : Summable (fun n : ℕ => C * Real.exp (-(n : ℝ) * c)) := by
    simpa only [mul_neg, neg_mul] using
      (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hc)).mul_left C
  exact hsum.of_nonneg_of_le (fun _ => measureReal_nonneg) hbound

theorem subgaussian_abs_tail [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_union] using (le_abs (a := ε) (b := X ω))
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) ≤
        μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

theorem ae_tendsto_div_succ_zero_of_subgaussian [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasSubgaussianMGF (X n) ((n : ℝ≥0) + 1) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_exp_tail
  intro ε hε
  refine ⟨2, ε ^ 2 / 2, by positivity, ?_⟩
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hset : {ω | ε ≤ |X n ω / ((n : ℝ) + 1)|} =
      {ω | ε * ((n : ℝ) + 1) ≤ |X n ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hn, le_div_iff₀ hn]
  rw [hset]
  have ht := subgaussian_abs_tail (hX n) (mul_nonneg hε.le hn.le)
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at ht
  refine ht.trans ?_
  have heq : -(ε * ((n : ℝ) + 1)) ^ 2 / (2 * ((n : ℝ) + 1)) =
      -((n : ℝ) + 1) * (ε ^ 2 / 2) := by
    field_simp [ne_of_gt hn]
  rw [heq]
  gcongr
  nlinarith [sq_nonneg ε]

theorem hasSubgaussianMGF_of_hasLaw_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  have hg : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    constructor
    · intro t
      exact integrable_exp_mul_gaussianReal t
    · intro t
      simp [mgf_id_gaussianReal]
  rw [← hX.map_eq] at hg
  simpa only [Function.id_comp] using hg.of_map hX.aemeasurable

theorem ae_brownian_div_succ_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B ((n : ℝ≥0) + 1) ω / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ae_tendsto_div_succ_zero_of_subgaussian
    (fun n => B ((n : ℝ≥0) + 1))
    (fun n => hasSubgaussianMGF_of_hasLaw_gaussian (hB.hasLaw_eval _))

theorem ae_brownian_div_nat_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_brownian_div_succ_tendsto_zero B hB] with ω hω
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hω

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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

attribute [local instance] OAI.Problem367.progressiveIsingPosteriorNonemptyIsingSpin
theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      infiniteGibbsSpinMean beta v y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| ≤ (d : ℝ) * beta := by
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.brownian_past_posterior_field_bound hbeta ν hB hmB t v] with p heq hb
  dsimp only
  rw [heq]
  exact hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InnovationPathMap
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem nnrealTimePrimitive_ae_eq_of_jointlyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {m m' : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => m p.1 p.2))
    (hm' : Measurable (fun p : ℝ≥0 × Ω => m' p.1 p.2))
    (heq : ∀ s, m s =ᵐ[P] m' s) (t : ℝ≥0) :
    nnrealTimePrimitive m t =ᵐ[P] nnrealTimePrimitive m' t := by
  have hj : Measurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    hm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hj' : Measurable (fun p : ℝ × Ω => m' p.1.toNNReal p.2) :=
    hm'.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hswap : ∀ᵐ ω ∂P, ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)),
      m r.toNNReal ω = m' r.toNNReal ω :=
    (Measure.ae_ae_comm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) (ν := P)
      (p := fun r ω => m r.toNNReal ω = m' r.toNNReal ω)
      (measurableSet_eq_fun hj hj')).mp
      (Filter.Eventually.of_forall (fun (r : ℝ) => heq r.toNNReal))
  filter_upwards [hswap] with ω hω
  simp only [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_congr_ae hω

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem ae_observation_sub_bound_of_shared_progressive_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ 1)
    (hb' : ∀ t, ∀ᵐ ω ∂P, |m' t ω| ≤ 1)
    {x x' w : Ω → ℝ} (t : ℝ≥0)
    (hx : ∀ᵐ ω ∂P, x ω = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, x' ω = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |x ω - x' ω| ≤ 2 * (t : ℝ) := by
  have hL := ae_lipschitzWith_nnrealTimePrimitive hm (C := 1) hb
  have hL' := ae_lipschitzWith_nnrealTimePrimitive hm' (C := 1) hb'
  filter_upwards [hL, hL', hx, hx'] with ω hω hω' hxω hxω'
  have h1 : |nnrealTimePrimitive m t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω.dist_le_mul t 0
  have h2 : |nnrealTimePrimitive m' t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω'.dist_le_mul t 0
  rw [hxω, hxω']
  have heq : (w ω + nnrealTimePrimitive m t ω) -
      (w ω + nnrealTimePrimitive m' t ω) =
      nnrealTimePrimitive m t ω - nnrealTimePrimitive m' t ω := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.gibbsField_bound_of_observation_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {X : Ω → TreeVertex d → ℝ}
    (hX : IdentDistrib X (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) :
    ∀ᵐ ω ∂P, |Real.artanh (infiniteGibbsSpinMean beta v (X ω)) - X ω v| ≤
      (d : ℝ) * beta := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hmeas := (ha.comp (measurable_infiniteGibbsSpinMean beta v)).sub
    (measurable_pi_apply v)
  apply hX.symm.ae_snd (measurableSet_le hmeas.abs measurable_const)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hp
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [heq]
  exact hp.2

theorem HasFreeIsingLaw.gibbsField_copy_bound_of_shared_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    ∀ᵐ ω ∂P,
      |Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))| ≤
          2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation hm hm'
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _))
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)) t hx hx'
  have hl := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw
  have hr := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw'
  filter_upwards [hobs, hl, hr] with ω hobsω hlω hrω
  have htriangle := abs_sub_le
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)))
    (X v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  have htriangle' := abs_sub_le (X v t ω) (X' v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  rw [abs_sub_comm (X' v t ω)] at htriangle'
  linarith

theorem HasFreeIsingLaw.gibbsField_copy_secondMoment_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    MemLp U 2 P ∧ 0 ≤ (∫ ω, (U ω) ^ 2 ∂P) ∧
      (∫ ω, (U ω) ^ 2 ∂P) ≤ (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  dsimp only
  have hb := hμ.gibbsField_copy_bound_of_shared_innovation hbeta hX hX'
    t v hlaw hlaw' hx hx'
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hmeas := (ha.comp (((hm.stronglyAdapted t).mono (F.le t)).measurable)).sub
    (ha.comp (((hm'.stronglyAdapted t).mono (G.le t)).measurable))
  exact discrepancy_secondMoment_bounds hmeas.aestronglyMeasurable hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

theorem identDistrib_observation_copies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) :
    IdentDistrib (fun q : CopySpace d => fun i => q.2.1 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    IdentDistrib (fun q : CopySpace d => fun i => q.2.2 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ⟨(heval.comp hl.hasLaw).identDistrib hobs,
    (heval.comp hr.hasLaw).identDistrib hobs⟩

theorem ae_all_innovation_identities (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta), ∀ v t,
      q.2.1 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q ∧
      q.2.2 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q := by
  filter_upwards [ae_innovationMap_copies hjoint] with q hq
  intro v t
  have hl := congrArg (fun x : Paths d => x v t) hq.1
  have hr := congrArg (fun x : Paths d => x v t) hq.2
  change q.2.1 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q = q.1 v t at hl
  change q.2.2 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q = q.1 v t at hr
  constructor <;> linarith

theorem fieldDifference_secondMoment_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (fieldDifference beta v t) 2 (rho ⊗ₘ (eta ×ₖ eta)) ∧
      0 ≤ (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ∧
      (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  exact hμ.gibbsField_copy_secondMoment_bounds hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationRecovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationRecovery

open IsingObservationInnovation

theorem measurable_decode {d : ℕ} : Measurable (decode (d := d)) := by
  apply SpinRecovery.measurable_decodeArray.comp
  exact Measurable.of_eval fun v => Measurable.of_eval fun n =>
    (continuous_eval_const (n : ℝ≥0)).measurable.comp (measurable_pi_apply v)

theorem decode_uniformObservation_ae {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    (fun q : IsingInnovation.State d ℝ => decode (uniformObservation q)) =ᵐ[
      μ.prod (labelMeasure d)] Prod.fst := by
  have hnoise := ae_brownian_div_nat_tendsto_zero
    (fun t u => WienerSampler.sample u t)
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have hall : ∀ᵐ q : IsingInnovation.State d ℝ ∂μ.prod (labelMeasure d),
      ∀ v : TreeVertex d, Tendsto
        (fun n : ℕ => WienerSampler.sample (q.2 v) n / (n : ℝ)) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro v
    exact (planted_noise_coordinate_measurePreserving μ
      (fun _ : TreeVertex d => uniform01) v).quasiMeasurePreserving.ae hnoise
  filter_upwards [hall] with q hq
  funext v
  have h := SpinRecovery.decode_signal_add_noise (q.1 v) (hq v)
  change SpinRecovery.decode (fun n : ℕ => WienerSampler.sample (q.2 v) n +
    ((n : ℝ≥0) : ℝ) * spinSign (q.1 v)) = q.1 v
  have hsign (s : IsingSpin) : SpinRecovery.spinSign s = spinSign s := by
    cases s <;> rfl
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext n
  rw [NNReal.coe_natCast, hsign]
  exact add_comm _ _

theorem map_decode_observationLaw {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    (observationLaw μ).map decode = μ := by
  rw [observationLaw, Measure.map_map measurable_decode measurable_uniformObservation]
  change Measure.map (fun q => decode (uniformObservation q)) _ = μ
  rw [Measure.map_congr (decode_uniformObservation_ae μ)]
  have : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_decode <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem hasFreeIsingLaw_decode_observationLaw {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ) :
    HasFreeIsingLaw theta ((observationLaw μ).map decode) := by
  let := hμ.isProbabilityMeasure
  rw [map_decode_observationLaw μ]
  exact hμ

end Problem367.IsingObservationRecovery

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationFactor
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ}

theorem measurable_posterior_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × Paths d => posterior beta v p.1 p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive
    (posterior_progressive beta v)).measurable

theorem measurable_field_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × Paths d => field beta v p.1 p.2) := by
  have hm := measurable_posterior_joint beta v
  unfold field Real.artanh
  exact ((measurable_const.add hm).div (measurable_const.sub hm)).sqrt.log

private theorem measurable_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.measurable.div Real.continuous_cosh.measurable

theorem measurable_tanh_field_real_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => Real.tanh (field beta v p.1.toNNReal p.2)) := by
  have hmap : Measurable (fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) :=
    measurable_real_toNNReal.prodMap measurable_id
  have hf : Measurable (fun p : ℝ × Paths d => field beta v p.1.toNNReal p.2) :=
    Measurable.comp (g := fun q : ℝ≥0 × Paths d => field beta v q.1 q.2)
      (f := fun p : ℝ × Paths d => (p.1.toNNReal, p.2))
      (measurable_field_joint beta v) hmap
  exact Measurable.comp (g := Real.tanh)
    (f := fun p : ℝ × Paths d => field beta v p.1.toNNReal p.2) measurable_tanh hf

theorem posterior_mem_Ioo_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ x ∂observationLaw μ, posterior beta v t x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval fun i => measurable_evaluation i t)
  apply (ae_map_iff measurable_uniformObservation.aemeasurable (hm measurableSet_Ioo)).mpr
  have hb := hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    t v
  filter_upwards [hb] with q hq
  change infiniteGibbsSpinMean beta v
    (fun i => WienerSampler.sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i)) ∈ _
  simpa only [add_comm] using hq.1

theorem tanh_field_eq_posterior_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    (fun x => Real.tanh (field beta v t x)) =ᵐ[observationLaw μ] posterior beta v t := by
  filter_upwards [posterior_mem_Ioo_ae hμ hbeta v t] with x hx
  exact Real.tanh_artanh hx

theorem isFactorOfIID_of_root_field_zero {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d)
    (hInt : ∀ t, Integrable
      (fun p => (field beta o t p.2.1 - field beta o t p.2.2) ^ 2) (copies beta μ))
    (hzero : ∀ t, (∫ p, (field beta o t p.2.1 - field beta o t p.2.2) ^ 2
      ∂copies beta μ) = 0) :
    IsFactorOfIID d (Real.tanh beta) := by
  let E : Paths d → TreeVertex d → ℕ → ℝ := fun x v n => x v n
  have hE : Measurable E := Measurable.of_eval fun v =>
    Measurable.of_eval fun n => measurable_evaluation v n
  apply isFactorOfIID_of_stationary_innovation_observable
    WienerSampler.wienerMeasure (observationLaw μ) (innovationMap beta)
    (measurable_innovationMap beta) (map_innovationMap_observationLaw hμ)
    E hE (fun g => relabel g) (measurePreserving_observationLaw_relabel hμ)
    (fun _ _ => rfl) (innovationMap_relabel_ae hμ) o
    (IsingObservationRecovery.hasFreeIsingLaw_decode_observationLaw hμ)
    (field beta o) (fun n w => w o n)
    (measurable_tanh_field_real_joint beta o) hInt hzero
  intro n
  have hp := nnrealTimePrimitive_ae_eq_of_jointlyMeasurable
    (P := observationLaw μ)
    (measurable_tanh.comp (measurable_field_joint beta o))
    (measurable_posterior_joint beta o)
    (tanh_field_eq_posterior_ae hμ hbeta o) (n : ℝ≥0)
  filter_upwards [hp] with x hx
  change x o n = innovationMap beta x o n +
    nnrealTimePrimitive (fun t x => Real.tanh (field beta o t x)) n x
  rw [hx, innovationMap_apply]
  ring

end Problem367.IsingObservationFactor

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

theorem integrable_field_difference_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    Integrable (fun p => (field beta v t p.2.1 - field beta v t p.2.2) ^ 2)
      (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t v).1.integrable_sq

theorem isFactorOfIID_of_root_field_variance_zero
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d)
    (hzero : ∀ t, (∫ p, (field beta o t p.2.1 - field beta o t p.2.2) ^ 2
      ∂copies beta μ) = 0) :
    IsFactorOfIID d (Real.tanh beta) :=
  isFactorOfIID_of_root_field_zero hμ hbeta o
    (integrable_field_difference_sq hμ hbeta o) hzero

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalSpatialRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem isFactorOfIID_of_critical_variance_and_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u w : TreeVertex d) (huw : treeAdj u w)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0, ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ)
    (hnoise : ∀ T : ℝ≥0, ∃ B E c a q C₀ : ℝ,
      0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧
      ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_root_field_variance_zero hμ hb (root d)
  intro t
  obtain ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, hbound⟩ := hnoise t
  exact critical_root_variance_zero_of_noise_bound hμ hd hb hcritical t u w huw
    hB hE hc ha hq hbound (hAC t) (hderiv t) t le_rfl

theorem isFactorOfIID_of_critical_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u w : TreeVertex d) (huw : treeAdj u w)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0, ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_critical_variance_and_noise_bound hμ hd hb hcritical
    u w huw hAC hderiv
  intro T
  obtain ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, _, hnoise⟩ :=
    exists_noise_energy_long_constants hμ hd hb hcritical T
  exact ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, hnoise⟩

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_StrictFactorRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation IsingCopyResponseRowPaths IsingCopySmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem isFactorOfIID_of_subcritical_actual_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0,
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
        deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
          ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_root_field_variance_zero hμ hb (root d)
  intro t
  exact siteVariance_eq_zero_of_subcritical_actual_variance_identity
    hμ hb hstrict t (hAC t) (hderiv t) t le_rfl

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_SharpVarianceRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367
open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open ConnectedHull

theorem isFactorOfIID_of_sharp_actual_variance_identity
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hsharp : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (hvariance : ActualRootVarianceIdentity beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  rcases lt_or_eq_of_le hsharp with hstrict | hcritical
  · exact isFactorOfIID_of_subcritical_actual_variance_identity hμ hb hstrict
      (fun T => (hvariance T).1) (fun T => (hvariance T).2)
  · let c : Fin d := ⟨0, by omega⟩
    let w : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
    have hw : treeAdj (root d) w := Or.inl ⟨c, rfl⟩
    exact IsingCopyResponseRowPaths.isFactorOfIID_of_critical_variance_identity
      hμ hd hb hcritical (root d) w hw (fun T => (hvariance T).1)
      (fun T => ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
        (hvariance T).2)

theorem free_ising_factor_below_threshold_of_actual_variance_identity_oai
    (hvariance : ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 < beta →
      ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 →
      ActualRootVarianceIdentity beta (freeIsingMeasure d (Real.tanh beta))) :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta →
      Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) →
      IsFactorOfIID d (Real.tanh beta) := by
  intro d beta hd hb hthreshold
  rcases eq_or_lt_of_le hb with hzero | hpos
  · subst beta
    exact free_ising_factor_beta_zero d
  · have hsharp : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using
        (tanh_threshold_iff_branching_sq hd hpos.le).mp hthreshold
    exact isFactorOfIID_of_sharp_actual_variance_identity
      (freeIsingMeasure_hasFreeIsingLaw d (Real.neg_one_lt_tanh beta).le
        (Real.tanh_lt_one beta).le) hd hpos.le hsharp
      (hvariance d beta hd hpos hsharp)

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity_oai := @OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity_oai
