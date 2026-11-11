-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:27.13028+00:00
-- url     : https://prove2.me/submissions/04245c2e-81b2-4b33-9079-c547eedaccfc

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonicalCovarianceEnergy_integrable
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_compensatedSquare_martingale
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousPosterior_initial_zero
import Theorems.Thm_OAI_Problem367_LocalizedArtanhFormula_exists_jointExit_artanh_decomposition

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

end Problem367

end

end OAI
end

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
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

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

lemma measurable_infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsResponseRow beta v) := by
  exact (StronglyMeasurable.tsum (fun w =>
    ((measurable_infiniteGibbsResponse beta v w).pow_const 2).stronglyMeasurable)).measurable

theorem isStronglyProgressive_infiniteGibbsCovariance
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v w : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsCovariance beta v w (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsCovariance beta v w).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

theorem isStronglyProgressive_infiniteGibbsResponseRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsResponseRow beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsResponseRow beta v).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitiveFubini
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem ae_all_nnrealTimePrimitive_eq_of_modification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {F G : Filtration ℝ≥0 mΩ} {m k : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hk : IsStronglyProgressive G k)
    (heq : ∀ t, m t =ᵐ[P] k t) :
    ∀ᵐ ω ∂P, ∀ t, nnrealTimePrimitive m t ω = nnrealTimePrimitive k t ω := by
  have hlocal : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (fun u : ℝ => m u.toNNReal ω) =ᵐ[volume.restrict (Set.Ioc 0 (n : ℝ))]
        (fun u : ℝ => k u.toNNReal ω) := by
    intro n
    let ν : Measure ℝ := volume.restrict (Set.Ioc 0 (n : ℝ))
    have hcm : StronglyMeasurable
        (fun p : ℝ × Ω => m (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
      (stronglyMeasurable_clipped_nnreal_process hm (n : ℝ≥0)).mono
        (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le (n : ℝ≥0))))
    have hck : StronglyMeasurable
        (fun p : ℝ × Ω => k (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
      (stronglyMeasurable_clipped_nnreal_process hk (n : ℝ≥0)).mono
        (sup_le_sup le_rfl (MeasurableSpace.comap_mono (G.le (n : ℝ≥0))))
    have hc : ∀ᵐ ω ∂P, ∀ᵐ u ∂ν,
        m (min u.toNNReal (n : ℝ≥0)) ω = k (min u.toNNReal (n : ℝ≥0)) ω := by
      apply (Measure.ae_ae_comm (μ := ν) (ν := P)
        (p := fun u ω => m (min u.toNNReal (n : ℝ≥0)) ω =
          k (min u.toNNReal (n : ℝ≥0)) ω)
        (measurableSet_eq_fun hcm.measurable hck.measurable)).mp
      exact Filter.Eventually.of_forall fun u => heq (min u.toNNReal (n : ℝ≥0))
    filter_upwards [hc] with ω hω
    filter_upwards [hω, ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have hun : u.toNNReal ≤ (n : ℝ≥0) :=
      Real.toNNReal_le_iff_le_coe.mpr hmem.2
    simpa only [min_eq_left hun] using hu
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  simp only [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_congr_ae
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hn.le) (hω n))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ArtanhMartingaleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

omit mΩ in
lemma stronglyMeasurable_secondWeight {m : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) :
    StronglyMeasurable[m] (fun ω => secondWeight (X ω)) :=
  hX.div ((stronglyMeasurable_const.sub (hX.pow 2)).pow 2)

end Problem367.ArtanhMartingaleFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ArtanhResponseCoefficients
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367.ArtanhResponseCoefficients
open ArtanhMartingaleFormula

theorem secondWeight_mul_tsum_sq {ι : Type*} (m : ℝ) (C : ι → ℝ) :
    secondWeight m * (∑' i, C i ^ 2) =
      m * (∑' i, (C i / (1 - m ^ 2)) ^ 2) := by
  rw [show (∑' i, (C i / (1 - m ^ 2)) ^ 2) =
      (∑' i, C i ^ 2) / (1 - m ^ 2) ^ 2 by
    simp only [div_pow, tsum_div_const]]
  simp only [secondWeight, div_eq_mul_inv]
  ring

theorem secondWeight_infiniteGibbsCovarianceRow {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (y : TreeVertex d → ℝ) :
    secondWeight (infiniteGibbsSpinMean beta v y) *
      (∑' w, infiniteGibbsCovariance beta v w y ^ 2) =
      infiniteGibbsSpinMean beta v y * infiniteGibbsResponseRow beta v y :=
  secondWeight_mul_tsum_sq _ _

theorem isStronglyProgressive_covarianceSquareRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F (fun t ω =>
      ∑' w, infiniteGibbsCovariance beta v w (fun i => X i t ω) ^ 2) := by
  intro T
  have hc (w : TreeVertex d) :=
    isStronglyProgressive_infiniteGibbsCovariance F beta v w X hX T
  let : MeasurableSpace Ω := F T
  exact StronglyMeasurable.tsum (fun w => (hc w).pow 2)

theorem ae_all_primitive_eq_responseDrift
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {F : Filtration ℝ≥0 mΩ} (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i))
    {M : ℝ≥0 → Ω → ℝ} (hM : IsStronglyProgressive F M)
    (hversion : ∀ t, M t =ᵐ[μ]
      fun ω => infiniteGibbsSpinMean beta v (fun i => X i t ω)) :
    ∀ᵐ ω ∂μ, ∀ t,
      nnrealTimePrimitive (fun s p => secondWeight (M s p) *
        (∑' w, infiniteGibbsCovariance beta v w (fun i => X i s p) ^ 2)) t ω =
      nnrealTimePrimitive (fun s p => M s p *
        infiniteGibbsResponseRow beta v (fun i => X i s p)) t ω := by
  have hleft : IsStronglyProgressive F (fun s p => secondWeight (M s p) *
      (∑' w, infiniteGibbsCovariance beta v w (fun i => X i s p) ^ 2)) := by
    intro T
    exact (stronglyMeasurable_secondWeight (hM T)).mul
      (isStronglyProgressive_covarianceSquareRow F beta v X hX T)
  have hright := hM.mul (isStronglyProgressive_infiniteGibbsResponseRow F beta v X hX)
  apply ae_all_nnrealTimePrimitive_eq_of_modification hleft hright
  intro t
  filter_upwards [hversion t] with ω hω
  rw [hω]
  exact secondWeight_infiniteGibbsCovarianceRow beta v _

end Problem367.ArtanhResponseCoefficients

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousModification
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

theorem measurable_sampledLimit_at [MeasurableSpace Ω]
    {q : T → ℕ → T} {F : T → Ω → ℝ} (t : T)
    (hF : ∀ n, Measurable (F (q t n))) : Measurable (sampledLimit q F t) := by
  exact (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable

theorem ae_all_eq_of_continuous_modification [TopologicalSpace T] [MeasurableSpace Ω]
    {μ : Measure Ω} {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ s ∈ S, F s =ᵐ[μ] G s)
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, sampledLimit q F t ω = G t ω := by
  let : Countable S := hS.to_subtype
  have hEq : ∀ᵐ ω ∂μ, ∀ s : S, F s ω = G s ω :=
    ae_all_iff.mpr (fun s => hFG s s.property)
  filter_upwards [hEq, hG] with ω hEqω hGω
  intro t
  have hseq : (fun n => F (q t n) ω) = (fun n => G (q t n) ω) :=
    funext (fun n => hEqω ⟨q t n, hqS t n⟩)
  unfold sampledLimit
  rw [hseq]
  exact ((hGω.tendsto t).comp (hq t)).limUnder_eq

theorem isStronglyProgressive_sampledLimit [Preorder T] [MeasurableSpace T]
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration T mΩ)
    {q : T → ℕ → T} {F : T → Ω → ℝ}
    (hF : ∀ n, IsStronglyProgressive ℱ (fun t ω => F (q t n) ω)) :
    IsStronglyProgressive ℱ (sampledLimit q F) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  exact StronglyMeasurable.limUnder (fun n => hF n t)

end ContinuousModification
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem isStronglyProgressive_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ} (ha : IsStronglyProgressive F a) :
    IsStronglyProgressive F (nnrealTimePrimitive a) := by
  intro T
  have hi : StronglyMeasurable[Subtype.instMeasurableSpace.prod (F T)]
      (fun p : Iic T × Ω => ∫ r : ℝ,
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0) := by
    have hc := stronglyMeasurable_clipped_nnreal_process ha T
    let : MeasurableSpace Ω := F T
    have hf : StronglyMeasurable (fun q : (Iic T × Ω) × ℝ =>
        a (min q.2.toNNReal T) q.1.2) :=
      hc.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hs : MeasurableSet {q : (Iic T × Ω) × ℝ |
        0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (measurable_subtype_coe.comp (measurable_subtype_coe.comp
            (measurable_fst.comp measurable_fst))))
    have hu : StronglyMeasurable (Function.uncurry (fun p : Iic T × Ω => fun r : ℝ =>
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0)) := by
      exact hf.piecewise hs stronglyMeasurable_zero
    exact hu.integral_prod_right
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) (p.1 : ℝ≥0)
  · have hrt : r.toNNReal ≤ T :=
      (by simpa using Real.toNNReal_mono hr.2 : r.toNNReal ≤ (p.1 : ℝ≥0)).trans p.1.2
    simp only [Set.indicator_of_mem hr, Set.mem_Ioc] at hr ⊢
    rw [ite_eq_left hr, min_eq_left hrt]
  · simp only [Set.indicator_of_notMem hr]
    exact (ite_eq_right hr).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveVersionPushforward
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ProgressiveVersionPushforward
open ContinuousModification

attribute [local instance] OAI.Problem367.ProgressiveVersionPushforward.instMeasurableSpaceContinuousMapNNRealReal_solutions
local instance instBorelSpaceContinuousMapNNRealReal_solutions : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma leftTime_le (t : ℝ≥0) (n : ℕ) : leftTime t n ≤ t := by
  simpa only [leftTime, Real.toNNReal_coe] using Real.toNNReal_mono (dyadicLeft_le t n)

lemma tendsto_leftTime (t : ℝ≥0) : Tendsto (leftTime t) atTop (𝓝 t) := by
  change Tendsto (fun n => (dyadicLeft (t : ℝ) n).toNNReal) atTop (𝓝 t)
  simpa only [ Function.comp_def, Real.toNNReal_coe] using
    continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_dyadicLeft (t : ℝ))

lemma leftTime_mem_range (t : ℝ≥0) (n : ℕ) : leftTime t n ∈ range gridTime :=
  ⟨(⌊(2 : ℝ)^n * (t : ℝ)⌋, n), rfl⟩

lemma denseRange_gridTime : DenseRange gridTime := by
  intro t
  exact mem_closure_of_tendsto (tendsto_leftTime t)
    (Eventually.of_forall (leftTime_mem_range t))

lemma measurable_leftTime (n : ℕ) : Measurable (fun t => leftTime t n) := by
  unfold leftTime dyadicLeft
  fun_prop

lemma measurable_version {Ω : Type*} [MeasurableSpace Ω]
    {M : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (M t)) (t : ℝ≥0) :
    Measurable (version M t) :=
  measurable_sampledLimit_at t (fun n => hm (leftTime t n))

lemma progressive_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F (version M) := by
  apply isStronglyProgressive_sampledLimit F
  intro n
  apply hM.comp _ (fun t _ => leftTime_le t n)
  intro T
  exact ((measurable_leftTime n).comp measurable_fst.subtype_val).stronglyMeasurable

lemma version_eq_of_grid {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (f : C(ℝ≥0, ℝ)) (h : ∀ p, M (gridTime p) ω = f (gridTime p)) :
    ∀ t, version M t ω = f t := by
  intro t
  have he : (fun n => M (leftTime t n) ω) = fun n => f (leftTime t n) := by
    funext n
    exact h (⌊(2 : ℝ)^n * (t : ℝ)⌋, n)
  unfold version sampledLimit
  rw [he]
  exact ((f.continuous.tendsto t).comp (tendsto_leftTime t)).limUnder_eq

lemma ae_all_version_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M G : ℝ≥0 → Ω → ℝ} (he : ∀ t, M t =ᵐ[μ] G t)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, version M t ω = G t ω := by
  apply ae_all_eq_of_continuous_modification (Set.countable_range gridTime)
    leftTime_mem_range tendsto_leftTime (fun t _ => he t) hc

lemma measurableEmbedding_gridEval : MeasurableEmbedding
    (fun f : C(ℝ≥0, ℝ) => fun p : ℤ × ℕ => f (gridTime p)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun _ => (continuous_eval_const _).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact denseRange_gridTime.equalizer f.continuous g.continuous h

theorem continuous_progressive_version_of_pullback
    {Ω Ξ : Type*} [MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {φ : Ω → Ξ} (hφ : Measurable φ)
    {F : Filtration ℝ≥0 mΞ} {M : ℝ≥0 → Ξ → ℝ}
    (hM : IsStronglyProgressive F M)
    {G : ℝ≥0 → Ω → ℝ}
    (hcG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω))
    (heG : ∀ t, G t =ᵐ[μ] fun ω => M t (φ ω)) :
    IsStronglyProgressive F (version M) ∧
      (∀ᵐ x ∂μ.map φ, Continuous (fun t => version M t x)) ∧
      (∀ t, version M t =ᵐ[μ.map φ] M t) := by
  have hm (t : ℝ≥0) : Measurable (M t) :=
    ((hM.stronglyAdapted t).mono (F.le t)).measurable
  let samples : Ξ → (ℤ × ℕ → ℝ) := fun x p => M (gridTime p) x
  let encode : C(ℝ≥0, ℝ) → (ℤ × ℕ → ℝ) := fun f p => f (gridTime p)
  have hms : Measurable samples := Measurable.of_eval (fun point => hm (gridTime point))
  have hgoodSet : MeasurableSet {x : Ξ | samples x ∈ range encode} :=
    measurableEmbedding_gridEval.measurableSet_range.preimage hms
  have hgoodPullback : ∀ᵐ ω ∂μ, samples (φ ω) ∈ range encode := by
    have heGrid : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℕ, G (gridTime p) ω = M (gridTime p) (φ ω) :=
      ae_all_iff.mpr (fun p => heG (gridTime p))
    filter_upwards [hcG, heGrid] with ω hc he
    exact ⟨⟨fun t => G t ω, hc⟩, funext he⟩
  have hgood : ∀ᵐ x ∂μ.map φ, samples x ∈ range encode :=
    (ae_map_iff hφ.aemeasurable hgoodSet).mpr hgoodPullback
  have hid : ∀ᵐ ω ∂μ, ∀ t, version M t (φ ω) = G t ω :=
    ae_all_version_eq (fun t => (heG t).symm) hcG
  refine ⟨progressive_version hM, ?_, ?_⟩
  · filter_upwards [hgood] with x hx
    obtain ⟨f, hf⟩ := hx
    have he := version_eq_of_grid f (fun p => (congrFun hf p).symm)
    simpa only [he] using f.continuous
  · intro t
    apply (ae_map_iff hφ.aemeasurable
      (measurableSet_eq_fun (measurable_version hm t) (hm t))).mpr
    filter_upwards [hid, heG t] with ω hi he
    exact (hi t).trans he

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InteriorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

theorem field_bound_iff_tanh_bounds {m X K : ℝ} :
    (m ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh m - X| ≤ K) ↔
      (Real.tanh (X - K) ≤ m ∧ m ≤ Real.tanh (X + K)) := by
  constructor
  · rintro ⟨hm, hb⟩
    constructor
    · apply (Real.artanh_le_artanh_iff
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hm).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).1]
    · apply (Real.artanh_le_artanh_iff hm
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).2]
  · intro hb
    have h := posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => m) tendsto_const_nhds (fun _ => hb)
    exact ⟨h.1, h.2.1⟩

private theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_tanh_response t).continuousAt

theorem ae_all_field_bound_of_continuous
    {T Ω : Type*} [TopologicalSpace T] [SeparableSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} {M X : T → Ω → ℝ} {K : ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ t,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense T
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ t : S,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K :=
    ae_all_iff.mpr (fun t => hb t)
  filter_upwards [hM, hX, hS] with ω hMω hXω hSω
  have hall : ∀ t, Real.tanh (X t ω - K) ≤ M t ω ∧
      M t ω ≤ Real.tanh (X t ω + K) := by
    refine isClosed_property hSd.denseRange_val
      (p := fun t => Real.tanh (X t ω - K) ≤ M t ω ∧
        M t ω ≤ Real.tanh (X t ω + K)) ?_ ?_
    · exact (isClosed_le (continuous_tanh.comp (hXω.sub continuous_const)) hMω).inter
        (isClosed_le hMω (continuous_tanh.comp (hXω.add continuous_const)))
    · intro t
      exact field_bound_iff_tanh_bounds.mp (hSω t)
  exact fun t => field_bound_iff_tanh_bounds.mpr (hall t)

theorem continuous_artanh_of_interior
    {T : Type*} [TopologicalSpace T] {m : T → ℝ}
    (hm : Continuous m) (hi : ∀ t, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    Continuous (fun t => Real.artanh (m t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_artanh_interval (hi t)).continuousAt.comp (hm.continuousAt)

end Problem367.PosteriorInteriorLocalization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem posterior_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    Martingale (posterior beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  have h := martingale_condExp (fun q : State d A => spinSign (q.1 v))
    (ArrayPosteriorStationarity.filtration B hmB)
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
  exact h.congr (posterior_progressive beta B hmB hcB v).stronglyAdapted
    (fun t => (posterior_eq_condExp hμ ν hB hmB t v).symm)

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem filtration_eq_comap_past (d : ℕ) (t : ℝ≥0) :
    filtration d t = MeasurableSpace.comap (past t) inferInstance :=
  arrayNaturalFiltration_eq_comap evaluation measurable_evaluation t

theorem filtration_comap_uniformObservation (d : ℕ) (t : ℝ≥0)
    (hm : ∀ s, Measurable (fun u => WienerSampler.sample u s)) :
    (filtration d t).comap uniformObservation =
      ArrayPosteriorStationarity.filtration
        (fun s u => WienerSampler.sample u s) hm t := by
  rw [filtration_eq_comap_past, MeasurableSpace.comap_comp]
  unfold ArrayPosteriorStationarity.filtration arrayObservationFiltration
  rw [arrayNaturalFiltration_eq_comap]
  rfl

end Problem367.IsingObservationInnovation

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

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousPosteriorInterior
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

theorem HasFreeIsingLaw.continuous_posterior_all_time_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      (∀ t, m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
          (d : ℝ) * beta) ∧
      Continuous (fun t => Real.artanh (m v t p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hX : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Continuous (fun t : ℝ≥0 => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v)) := by
    have hnoise := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).cont
    filter_upwards [hnoise] with p hp
    exact (continuous_subtype_val.mul continuous_const).add hp
  have hb : ∀ t, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
    intro t
    filter_upwards [hversion v t,
      hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν
        (fun i => (hB i).toIsPreBrownianReal) hmB t v] with p hp hb
    rw [hp]
    exact hb
  filter_upwards [hcm v,
    PosteriorInteriorLocalization.ae_all_field_bound_of_continuous (hcm v) hX hb]
      with p hp hb
  exact ⟨hb, PosteriorInteriorLocalization.continuous_artanh_of_interior hp
    (fun t => (hb t).1)⟩

theorem isStronglyProgressive_artanh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    IsStronglyProgressive F (fun t ω => Real.artanh (m t ω)) := by
  have ha : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  intro t
  let : MeasurableSpace Ω := F t
  exact (ha.comp (hm t).measurable).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalContinuousFields
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma field_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (field beta v) :=
  isStronglyProgressive_artanh (filtration d) (posterior_progressive beta v)

lemma continuousField_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousField beta v) :=
  ProgressiveVersionPushforward.progressive_version (field_progressive beta v)

theorem continuousField_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousField beta v t x)) ∧
      (∀ t, continuousField beta v t =ᵐ[observationLaw μ] field beta v t) := by
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (u : ℝ) : Continuous (fun t => B t u) := (WienerSampler.sample u).continuous
  obtain ⟨Z, hZ⟩ := Classical.axiomOfChoice
    (fun w : TreeVertex d => IsingInnovation.exists_continuous_posterior
      hd hμ hb hcrit uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB w)
  have hcont (w : TreeVertex d) : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Z w t q) := (hZ w).2.2.1
  have hver (w : TreeVertex d) (t : ℝ≥0) : Z w t =ᵐ[μ.prod (labelMeasure d)]
      (fun q => infiniteGibbsSpinMean beta w
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    filter_upwards [(hZ w).2.2.2.2.2 t] with q hq
    refine hq.trans ?_
    change infiniteGibbsSpinMean beta w
      (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)) = _
    apply congrArg (infiniteGibbsSpinMean beta w)
    funext i
    exact add_comm _ _
  have hfields := hμ.continuous_posterior_all_time_field_bound hb
    (fun _ : TreeVertex d => uniform01) (fun _ => WienerSampler.sample_isBrownianReal)
    (fun _ => hmB) hcont hver
  have hc : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Real.artanh (Z v t q)) :=
    hfields.mono (fun q hq => (hq v).2)
  have he (t : ℝ≥0) : (fun q => Real.artanh (Z v t q)) =ᵐ[μ.prod (labelMeasure d)]
      (fun q => field beta v t (uniformObservation q)) := by
    filter_upwards [hver v t] with q hq
    change Real.artanh (Z v t q) = Real.artanh
      (infiniteGibbsSpinMean beta v
        (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)))
    apply congrArg Real.artanh
    refine hq.trans ?_
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    exact add_comm _ _
  exact (ProgressiveVersionPushforward.continuous_progressive_version_of_pullback
    measurable_uniformObservation (field_progressive beta v) hc he).2

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurePreserving_uniformObservation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
  ⟨measurable_uniformObservation, rfl⟩

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalPosteriorStops
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

private lemma continuous_real_tanh : Continuous Real.tanh :=
  lipschitzWith_tanh_response.continuous

lemma continuousPosterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousPosterior beta v) := by
  intro T
  exact continuous_real_tanh.comp_stronglyMeasurable (continuousField_progressive beta v T)

lemma continuousPosterior_interior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : continuousPosterior beta v t x ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

lemma artanh_continuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) :
    Real.artanh (continuousPosterior beta v t x) = continuousField beta v t x :=
  Real.artanh_tanh _

 theorem continuousPosterior_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousPosterior beta v t x)) ∧
      (∀ t, continuousPosterior beta v t =ᵐ[observationLaw μ] posterior beta v t) := by
  obtain ⟨hc, he⟩ := continuousField_modification hd hμ hb hcrit v
  refine ⟨hc.mono (fun x hx => continuous_real_tanh.comp hx), fun t => ?_⟩
  filter_upwards [he t, tanh_field_eq_posterior_ae hμ hb v t] with x hx ht
  exact (congrArg Real.tanh hx).trans ht

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_Pushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set

namespace Problem367.MartingalePushforward

 theorem martingale_of_pullback
    {ι Ω Ξ : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : Ω → Ξ} (hφ : MeasurePreserving φ μ ν)
    {F : Filtration ι mΩ} {G : Filtration ι mΞ}
    (hpast : ∀ t, (G t).comap φ ≤ F t)
    {X : ι → Ξ → ℝ} (hX : StronglyAdapted G X)
    (hM : Martingale (fun t ω => X t (φ ω)) F μ) : Martingale X G ν := by
  have hm (t : ι) : AEStronglyMeasurable (X t) ν :=
    ((hX t).mono (G.le t)).aestronglyMeasurable
  have hi (t : ι) : Integrable (X t) ν :=
    (hφ.integrable_comp (hm t)).mp (hM.integrable t)
  refine ⟨hX, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hi t)
    (fun A _ _ => (hi s).integrableOn) _ (hX s).aestronglyMeasurable
  intro A hA _
  have hpre : MeasurableSet[F s] (φ ⁻¹' A) :=
    hpast s _ ((comap_measurable (m := G s) φ) hA)
  have he (u : ι) : (∫ x in A, X u x ∂ν) = ∫ ω in φ ⁻¹' A, X u (φ ω) ∂μ := by
    rw [← hφ.map_eq]
    exact setIntegral_map (G.le s _ hA) (by simpa only [hφ.map_eq] using hm u)
      hφ.measurable.aemeasurable
  rw [he s, he t]
  exact hM.setIntegral_eq hst hpre

end Problem367.MartingalePushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalMartingales
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma evaluation_progressive {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (evaluation v) :=
  (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation v).isStronglyProgressive_of_continuous
    (fun x => (x v).continuous)

 theorem canonical_posterior_martingale
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  apply MartingalePushforward.martingale_of_pullback (measurePreserving_uniformObservation μ)
    (F := ArrayPosteriorStationarity.filtration B hmB)
    (fun t => (filtration_comap_uniformObservation d t hmB).le)
    (posterior_progressive beta v).stronglyAdapted
  exact IsingInnovation.posterior_martingale hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB
    (fun u => (WienerSampler.sample u).continuous) v

 theorem continuousPosterior_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (continuousPosterior beta v) (filtration d) (observationLaw μ) :=
  (canonical_posterior_martingale hμ v).congr
    (continuousPosterior_progressive beta v).stronglyAdapted
    (fun t => ((continuousPosterior_modification hd hμ hb hcrit v).2 t).symm)

lemma canonicalCovarianceEnergy_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (canonicalCovarianceEnergy beta v) :=
  ArtanhResponseCoefficients.isStronglyProgressive_covarianceSquareRow _ beta v _ evaluation_progressive

 theorem continuousPosterior_compensatedSquare_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (fun t x => continuousPosterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x)
      (filtration d) (observationLaw μ) := by
  apply (canonical_compensatedSquare_martingale hd hμ hb hcrit v).congr
    (fun t => ((continuousPosterior_progressive beta v).stronglyAdapted t).pow 2 |>.sub
      ((isStronglyProgressive_nnrealTimePrimitive
        (canonicalCovarianceEnergy_progressive beta v)).stronglyAdapted t))
  intro t
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit v).2 t] with x hx
  change posterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x =
    continuousPosterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x
  rw [hx]

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalArtanh
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

lemma canonicalResponseDrift_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (canonicalResponseDrift beta v) :=
  (posterior_progressive beta v).mul
    (isStronglyProgressive_infiniteGibbsResponseRow _ beta v _ evaluation_progressive)

 theorem canonical_artanh_decomposition_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) (T : ℝ≥0) :
    let τ := canonicalPosteriorExit beta v n
    let N := stoppedProcess (continuousPosterior beta v) τ
    ∃ L : Paths d → ℝ, StronglyMeasurable L ∧ MemLp L 2 (observationLaw μ) ∧
      Tendsto (fun k => ∫ x,
        (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) T k x - L x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0) ∧
      stoppedProcess (continuousField beta v) τ T =ᵐ[observationLaw μ]
        (fun x => L x + stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta v)) τ T x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨L, hmL, hL, hl, he⟩ := LocalizedArtanhFormula.exists_jointExit_artanh_decomposition
    (continuousPosterior_martingale hd hμ hb hcrit v)
    (continuousPosterior_compensatedSquare_martingale hd hμ hb hcrit v)
    (continuousPosterior_progressive beta v) (canonicalCovarianceEnergy_progressive beta v)
    (continuousPosterior_modification hd hμ hb hcrit v).1
    (continuousPosterior_initial_zero hd hμ hb hcrit v)
    (Eventually.of_forall (fun x t => (abs_lt.mpr (continuousPosterior_interior beta v t x)).le))
    (Eventually.of_forall (fun x t => tsum_nonneg (fun _ => sq_nonneg _)))
    (canonicalCovarianceEnergy_integrable hμ v) n T
  have hd1 := ArtanhResponseCoefficients.ae_all_primitive_eq_responseDrift beta v evaluation
    evaluation_progressive (continuousPosterior_progressive beta v)
    (continuousPosterior_modification hd hμ hb hcrit v).2
  have hd2 := ae_all_nnrealTimePrimitive_eq_of_modification
    ((continuousPosterior_progressive beta v).mul
      (isStronglyProgressive_infiniteGibbsResponseRow _ beta v _ evaluation_progressive))
    (canonicalResponseDrift_progressive beta v)
    (fun t => ((continuousPosterior_modification hd hμ hb hcrit v).2 t).mono
      (fun x hx => congrArg (fun r => r * infiniteGibbsResponseRow beta v (fun i => x i t)) hx))
  refine ⟨L, hmL, hL, hl, ?_⟩
  filter_upwards [he, continuousPosterior_initial_zero hd hμ hb hcrit v, hd1, hd2]
    with x hx hz h1 h2
  simp only [hz, Pi.zero_apply, Real.artanh_zero, sub_zero] at hx
  change Real.artanh (continuousPosterior beta v _ x) = _ at hx
  rw [artanh_continuousPosterior] at hx
  refine hx.trans ?_
  congr 1
  exact (h1 _).trans (h2 _)

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition_oai := @OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition_oai
