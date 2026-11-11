-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:48:00.101141+00:00
-- url     : https://prove2.me/submissions/8b2fe5d0-682e-4e46-84a1-f4776006085e

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopyEnergy_copy_row_energy_integrable
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousPosterior_initial_zero
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_isLocalizingSequence_commonPosteriorExit

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367.DiscrepancyEnergy

theorem absolutelyContinuousOnInterval_congr_on
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have heq : (∑ i ∈ Finset.range E.1,
      dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]
  rw [← heq]
  exact hδf E hE hlen

theorem absolutelyContinuousOnInterval_of_integral_representation
    {V k : ℝ → ℝ} {a b c : ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hV : ∀ t ∈ uIcc a b, V t = c + ∫ s in a..t, k s) :
    AbsolutelyContinuousOnInterval V a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr_on
    (hc.fun_add (hk.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
  intro t ht
  exact (hV t ht).symm

theorem intervalIntegrable_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {E : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    IntervalIntegrable (fun s => ∫ ω, E s ω ∂μ) volume 0 T := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hE.integral_prod_left

theorem ae_deriv_of_integral_representation
    {V k : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hk : IntervalIntegrable k volume a b)
    (hV : ∀ t ∈ Icc a b, V t = c + ∫ s in a..t, k s) :
    ∀ᵐ t ∂volume.restrict (Icc a b), deriv V t = k t := by
  rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hk.ae_hasDerivAt_integral] with t ht hmem
  have ht' : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hlocal : V =ᶠ[𝓝 t] (fun x => c + ∫ s in a..x, k s) := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    exact hV x ⟨hx.1.le, hx.2.le⟩
  exact ((ht ht' a (by simp)).const_add c).congr_of_eventuallyEq hlocal |>.deriv

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem summable_sq_sub {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    Summable (fun i => (c i - c' i) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hc.add hc').mul_left 2)
  intro i
  nlinarith [sq_nonneg (c i + c' i)]

theorem tsum_sq_sub_le {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    (∑' i, (c i - c' i) ^ 2) ≤ 2 * ((∑' i, (c i) ^ 2) + ∑' i, (c' i) ^ 2) := by
  calc
    (∑' i, (c i - c' i) ^ 2) ≤ ∑' i, 2 * ((c i) ^ 2 + (c' i) ^ 2) := by
      exact Summable.tsum_le_tsum (fun i => by nlinarith [sq_nonneg (c i + c' i)])
        (summable_sq_sub hc hc') ((hc.add hc').mul_left 2)
    _ = _ := by rw [tsum_mul_left, hc.tsum_add hc']

theorem abs_noise_add_drift_le
    {R X m m' A A' H : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hnoise : R ≤ 2 * (A + A')) (hX : |X| ≤ H)
    (hm : |m| ≤ 1) (hm' : |m'| ≤ 1) :
    |R + 2 * X * (m * A - m' * A')| ≤ (2 + 2 * H) * (A + A') := by
  have hH : 0 ≤ H := (abs_nonneg X).trans hX
  have hd : |m * A - m' * A'| ≤ A + A' := by
    calc
      |m * A - m' * A'| ≤ |m * A| + |m' * A'| := abs_sub _ _
      _ = |m| * A + |m'| * A' := by rw [abs_mul, abs_mul, abs_of_nonneg hA,
        abs_of_nonneg hA']
      _ ≤ A + A' := by nlinarith
  calc
    |R + 2 * X * (m * A - m' * A')| ≤ |R| + |2 * X * (m * A - m' * A')| :=
      abs_add_le _ _
    _ = R + 2 * |X| * |m * A - m' * A'| := by
      rw [abs_of_nonneg hR, abs_mul, abs_mul]
      norm_num
    _ ≤ R + 2 * H * (A + A') := by gcongr
    _ ≤ (2 + 2 * H) * (A + A') := by nlinarith

theorem integrable_sq_difference_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2)) :
    Integrable (fun ω => ∑' i, (c i ω - c' i ω) ^ 2) μ := by
  apply ((hA.add hA').const_mul 2).mono'
    (AEStronglyMeasurable.tsum (fun i => ((hc i).sub (hc' i)).pow 2))
  filter_upwards [hsum] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
  exact tsum_sq_sub_le hω.1 hω.2

theorem integrable_noise_add_drift
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ} {X m m' : Ω → ℝ} {H : ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hXm : AEStronglyMeasurable X μ)
    (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2))
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ H ∧ |m ω| ≤ 1 ∧ |m' ω| ≤ 1) :
    Integrable (fun ω => (∑' i, (c i ω - c' i ω) ^ 2) +
      2 * X ω * (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2))) μ := by
  have hn := integrable_sq_difference_row hc hc' hA hA' hsum
  have hmeas := hn.aestronglyMeasurable.add
    ((hXm.const_mul 2).mul
      ((hm.mul hA.aestronglyMeasurable).sub (hm'.mul hA'.aestronglyMeasurable)))
  apply ((hA.add hA').const_mul (2 + 2 * H)).mono' hmeas
  filter_upwards [hsum, hbound] with ω hsumω hb
  rw [Real.norm_eq_abs]
  exact abs_noise_add_drift_le (tsum_nonneg (fun _ => sq_nonneg _))
    (tsum_nonneg (fun _ => sq_nonneg _)) (tsum_nonneg (fun _ => sq_nonneg _))
    (tsum_sq_sub_le hsumω.1 hsumω.2) hb.1 hb.2.1 hb.2.2

end Problem367.DiscrepancyEnergy

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

end Problem367

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IntegrableTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {a : ℝ≥0 → Ω → ℝ}

theorem ae_intervalIntegrable_horizons_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (n : ℝ) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [(ha n).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hω

theorem ae_continuous_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

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

theorem progressive_memLp_two_on_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → ℝ}
    (hU : IsStronglyProgressive F U) (T : ℝ≥0) (C : ℝ)
    (hb : ∀ t ≤ T, ∀ᵐ ω ∂P, |U t ω| ≤ C) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P,
      |U p.1.toNNReal p.2| ≤ C) ∧
    MemLp (fun p : ℝ × Ω => U p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (T : ℝ))
  have hclip : StronglyMeasurable (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hU T).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le T)))
  have hbc : ∀ᵐ p ∂ν.prod P, |U (min p.1.toNNReal T) p.2| ≤ C := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hclip.measurable.abs measurable_const)).2
    exact Filter.Eventually.of_forall fun r => hb _ (min_le_right r.toNNReal T)
  have hc : MemLp (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) 2 (ν.prod P) :=
    MemLp.of_bound hclip.aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hbc)
  have heq : (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) =ᵐ[ν.prod P]
      (fun p => U p.1.toNNReal p.2) := by
    have hmem : ∀ᵐ p ∂ν.prod P, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    have ht : p.1.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hp.2
    simp only [min_eq_left ht]
  refine ⟨?_, MemLp.ae_eq heq hc⟩
  filter_upwards [heq, hbc] with p heq hp
  rwa [← heq]

theorem HasFreeIsingLaw.gibbsField_copy_joint_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive F (X' i))
    (T : ℝ≥0) (v : TreeVertex d)
    (hlaw : ∀ t ≤ T, IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : ∀ t ≤ T, IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {W : ℝ≥0 → Ω → ℝ}
    (hx : ∀ t ≤ T, ∀ᵐ ω ∂P, X v t ω = W t ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ t ≤ T, ∀ᵐ ω ∂P, X' v t ω = W t ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun t ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P,
      |U p.1.toNNReal p.2| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta) ∧
    MemLp (fun p : ℝ × Ω => U p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
  dsimp only
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean F beta v X' hX'
  have hU : IsStronglyProgressive F (fun t ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))) := by
    intro t
    exact ((ha.comp (hm t).measurable).sub
      (ha.comp (hm' t).measurable)).stronglyMeasurable
  apply progressive_memLp_two_on_horizon hU T (2 * (T : ℝ) + 2 * (d : ℝ) * beta)
  intro t ht
  filter_upwards [hμ.gibbsField_copy_bound_of_shared_innovation hbeta
    hX hX' t v (hlaw t ht) (hlaw' t ht) (hx t ht) (hx' t ht)] with ω hω
  exact hω.trans (by have htr : (t : ℝ) ≤ T := ht; linarith)

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

theorem ae_fieldDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ q ∂rho ⊗ₘ (eta ×ₖ eta),
      |fieldDifference beta v t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_bound_of_shared_innovation hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

theorem fieldDifference_joint_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (T : ℝ≥0) (v : TreeVertex d) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (rho ⊗ₘ (eta ×ₖ eta)),
      |fieldDifference beta v p.1.toNNReal p.2| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta) ∧
    MemLp (fun p : ℝ × CopySpace d => fieldDifference beta v p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (rho ⊗ₘ (eta ×ₖ eta))) := by
  have hlaws := identDistrib_observation_copies hμ hjoint
  have hx (t : ℝ≥0) :=
    (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' (t : ℝ≥0) :=
    (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_joint_bounds hbeta progressive_leftObservation
      progressive_rightObservation T v (fun t _ => (hlaws t).1)
      (fun t _ => (hlaws t).2) (fun t _ => hx t) (fun t _ => hx' t)

end Copies

end Problem367.IsingConditionalCopyBounds

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

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedDiscrepancyEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_integral_stopped_density [SFinite P]
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, Measurable (τ n))
    {E : ℝ → Ω → ℝ} {T : ℝ≥0}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..(T : ℝ),
      ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, E s ω ∂P)) := by
  let Q := (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P
  let A n := {p : ℝ × Ω | (p.1.toNNReal : WithTop ℝ≥0) ≤ τ n p.2}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_le ((measurable_real_toNNReal.comp measurable_fst).withTop_coe)
      ((hτ n).comp measurable_snd)
  have hEn (n : ℕ) : Integrable ((A n).indicator (fun p : ℝ × Ω => E p.1 p.2)) Q :=
    hE.indicator (hA n)
  have hlim : Tendsto (fun n => ∫ p, (A n).indicator (fun p : ℝ × Ω => E p.1 p.2) p ∂Q)
      atTop (𝓝 (∫ p : ℝ × Ω, E p.1 p.2 ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun p : ℝ × Ω => ‖E p.1 p.2‖)
      (fun n => (hEn n).aestronglyMeasurable) hE.norm
    · intro n
      apply Eventually.of_forall
      intro p
      by_cases hp : p ∈ A n <;> simp [hp]
    · have hm : ∀ᵐ p ∂Q, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      have he : ∀ᵐ p ∂Q, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n p.2 :=
        Measure.quasiMeasurePreserving_snd.ae hexit
      filter_upwards [hm, he] with p hp he
      have hpT : p.1.toNNReal ≤ T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hp.2
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      exact (Set.indicator_of_mem (show p ∈ A n from
        (WithTop.coe_le_coe.mpr hpT).trans hn) (fun p : ℝ × Ω => E p.1 p.2)).symm
  have heq (n : ℕ) : (∫ p, (A n).indicator (fun p : ℝ × Ω => E p.1 p.2) p ∂Q) =
      ∫ s in (0 : ℝ)..(T : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P := by
    rw [integral_prod _ (hEn n), intervalIntegral.integral_of_le T.coe_nonneg]
    simp only [Set.indicator, A, mem_ofPred_eq]
  have heq' : (∫ p : ℝ × Ω, E p.1 p.2 ∂Q) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, E s ω ∂P := by
    rw [integral_prod _ hE, intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [heq, heq'] using hlim

theorem tendsto_integral_stopped_square [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T t : ℝ≥0} (ht : t ≤ T) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω) :
    Tendsto (fun n => ∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P)
      atTop (𝓝 (∫ ω, (X t ω) ^ 2 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C ^ 2)
  · intro n
    have hm : AEStronglyMeasurable (stoppedProcess X (τ n) t) P :=
      (((hX.stoppedProcess (hτ n)).stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    exact hm.pow 2
  · exact integrable_const _
  · intro n
    filter_upwards [hb] with ω hω
    have hs : |stoppedProcess X (τ n) t ω| ≤ C := by
      exact hω _ ((WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n ω))).trans ht)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
  · filter_upwards [hexit] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    rw [stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn)]

theorem secondMoment_integral_representation_of_stopped [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T : ℝ≥0} {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω)
    {E : ℝ → Ω → ℝ}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :
    ∀ t ≤ T, (∫ ω, (X t ω) ^ 2 ∂P) =
      (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, E s ω ∂P := by
  intro t ht
  have hEt : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) (t : ℝ))).prod P) :=
    hE.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (show (t : ℝ) ≤ T from ht))) le_rfl)
  have hxt : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (t : WithTop ℝ≥0) ≤ τ n ω := by
    filter_upwards [hexit] with ω hω
    filter_upwards [hω] with n hn
    exact (WithTop.coe_le_coe.mpr ht).trans hn
  have hl := tendsto_integral_stopped_square hX hτ ht hb hexit
  have hr := (tendsto_integral_stopped_density (fun n => (hτ n).measurable') hEt hxt).const_add
    (∫ ω, (X 0 ω) ^ 2 ∂P)
  have heq : (fun n => ∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
      (fun n => (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :=
    funext (fun n => hlocal n t ht)
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem secondMoment_analysis_of_stopped [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T : ℝ≥0} {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω)
    {E : ℝ → Ω → ℝ}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ ω, (X t.toNNReal ω) ^ 2 ∂P) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        deriv (fun s : ℝ => ∫ ω, (X s.toNNReal ω) ^ 2 ∂P) t = ∫ ω, E t ω ∂P) := by
  have hrep : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      (∫ ω, (X t.toNNReal ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂P := by
    intro t ht
    have htT : t.toNNReal ≤ T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
    simpa only [Real.coe_toNNReal t ht.1] using
      secondMoment_integral_representation_of_stopped hX hτ hb hexit hE hlocal t.toNNReal htT
  refine ⟨?_, ae_deriv_of_integral_representation T.coe_nonneg
    (intervalIntegrable_mean T.coe_nonneg hE) hrep⟩
  apply absolutelyContinuousOnInterval_of_integral_representation
    (intervalIntegrable_mean T.coe_nonneg hE)
  simpa only [uIcc_of_le T.coe_nonneg] using hrep

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStoppedEnergy
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem ae_all_field_difference_version_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2)) :
    ∀ᵐ q ∂copies beta μ, ∀ t, |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hfixed (t : ℝ≥0) : ∀ᵐ q ∂copies beta μ,
      |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
    filter_upwards [hver t, IsingConditionalCopyBounds.ae_fieldDifference_bound
      hμ hb kernel_graphLaw t v] with q hq hbound
    exact hq ▸ hbound
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ q ∂copies beta μ, ∀ t : S,
      |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta :=
    ae_all_iff.mpr (fun t => hfixed t)
  filter_upwards [hc, hS] with q hqc hSq
  refine isClosed_property hSd.denseRange_val
    (p := fun t : ℝ≥0 => |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta) ?_ hSq
  exact isClosed_le hqc.abs
    ((continuous_const.mul continuous_subtype_val).add continuous_const)

theorem ae_horizon_field_difference_version_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2)) (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ t ≤ T,
      |X t q| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  filter_upwards [ae_all_field_difference_version_bound hμ hb v hc hver] with q hq
  intro t ht
  exact (hq t).trans (by gcongr)

theorem field_difference_energy_analysis_of_stopped_version
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d)
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Paths d × (Paths d × Paths d)))}
    {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hX : IsStronglyProgressive F X)
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2))
    {τ : ℕ → (Paths d × (Paths d × Paths d)) → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime F (τ n)) {T : ℝ≥0}
    (hexit : ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n q)
    {E : ℝ → (Paths d × (Paths d × Paths d)) → ℝ}
    (hE : Integrable (fun p : ℝ × (Paths d × (Paths d × Paths d)) => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess X (τ n) t q) ^ 2 ∂copies beta μ) =
        (∫ q, (X 0 q) ^ 2 ∂copies beta μ) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n q then E s q else 0 ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        deriv (fun s : ℝ => ∫ q,
          (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
            ∂copies beta μ) t = ∫ q, E t q ∂copies beta μ) := by
  have heq (t : ℝ≥0) : (∫ q, (X t q) ^ 2 ∂copies beta μ) =
      ∫ q, (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ :=
    integral_congr_ae ((hver t).mono (fun q hq => congrArg (fun x : ℝ => x ^ 2) hq))
  simpa only [heq] using DiscrepancyEnergy.secondMoment_analysis_of_stopped hX hτ
    (ae_horizon_field_difference_version_bound hμ hb v hc hver T) hexit hE hlocal

end Problem367.IsingObservationFactor

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

theorem exists_uniform_radius_of_compact
    {T : Type*} [TopologicalSpace T] {s : Set T} (hs : IsCompact s)
    {m : T → ℝ} (hm : ContinuousOn m s)
    (hi : ∀ t ∈ s, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ t ∈ s, |m t| ≤ r := by
  by_cases hne : s.Nonempty
  · obtain ⟨t, ht, hmax⟩ := hs.exists_isMaxOn hne hm.abs
    exact ⟨|m t|, abs_nonneg _, abs_lt.mpr (hi t ht), fun u hu => hmax hu⟩
  · exact ⟨0, le_rfl, by norm_num, fun t ht => (hne ⟨t, ht⟩).elim⟩

theorem tendsto_radius : Tendsto radius atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hden
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [sub_zero, Function.comp_def] using
    tendsto_const_nhds.sub hi

end Problem367.PosteriorInteriorLocalization

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

lemma continuousDifference_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (continuousDifference beta v) := by
  have hl : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : IsingConditionalCopyBounds.CopySpace d) => field beta v t q.2.1) :=
    isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
      IsingConditionalCopyBounds.progressive_leftObservation)
  have hr : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : IsingConditionalCopyBounds.CopySpace d) => field beta v t q.2.2) :=
    isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
      IsingConditionalCopyBounds.progressive_rightObservation)
  exact (ProgressiveVersionPushforward.progressive_version hl).sub
    (ProgressiveVersionPushforward.progressive_version hr)

theorem continuousDifference_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ q ∂copies beta μ, Continuous (fun t => continuousDifference beta v t q)) ∧
      (∀ t, continuousDifference beta v t =ᵐ[copies beta μ]
        (fun q => field beta v t q.2.1 - field beta v t q.2.2)) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ) (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  obtain ⟨hc, he⟩ := continuousField_modification hd hμ hb hcrit v
  constructor
  · filter_upwards [hl.quasiMeasurePreserving.ae hc, hr.quasiMeasurePreserving.ae hc]
      with q hql hqr
    exact hql.sub hqr
  · intro t
    filter_upwards [hl.quasiMeasurePreserving.ae (he t), hr.quasiMeasurePreserving.ae (he t)]
      with q hql hqr
    exact congrArg₂ (fun x y : ℝ => x - y) hql hqr

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_DominatedMartingaleRightContinuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

namespace Problem367.DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

theorem isStronglyProgressive_mono_filtration
    {G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) (hM : IsStronglyProgressive F M) :
    IsStronglyProgressive G M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hFG t)))

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_StoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

theorem le_rationalExit_of_bound {Ω : Type*} {M : ℝ≥0 → Ω → ℝ}
    {r : ℝ} {T : ℝ≥0} {ω : Ω}
    (hbound : ∀ t ≤ T, |M t ω| ≤ r) :
    (T : WithTop ℝ≥0) ≤ rationalExit M r ω := by
  apply le_iInf
  intro q
  by_cases hq : r < |M (q : ℝ≥0) ω|
  · simp only [hq, ite_true, if_true, WithTop.coe_le_coe]
    exact le_of_not_gt (fun h => (not_lt_of_ge (hbound q h.le)) hq)
  · simp only [hq, ite_false, if_false]
    exact le_top

theorem eventually_lt_threshold {r : ℝ} (hr : r < 1) :
    ∀ᶠ n in atTop, r < threshold n :=
  PosteriorInteriorLocalization.tendsto_radius.eventually_const_lt hr

theorem eventually_le_posteriorExit {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {T : ℝ≥0} (hcompact : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ posteriorExit M n ω := by
  obtain ⟨r, hr, hb⟩ := hcompact
  have hcap : ∀ᶠ n : ℕ in atTop, T ≤ (n : ℝ≥0) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop T)
  filter_upwards [eventually_lt_threshold hr, hcap] with n hn hTn
  apply le_min
  · exact le_rationalExit_of_bound (fun t ht => (hb t ht).trans hn.le)
  · exact WithTop.coe_le_coe.mpr (hTn.trans (le_add_of_nonneg_right zero_le))

end Problem367.PosteriorStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CompensatorStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorCompensatorStopping

open PosteriorStoppingTimes

theorem eventually_le_compensatorExit {Ω : Type*} {A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => A t ω)) (T : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, (T : WithTop ℝ≥0) ≤ rationalExit A ((n : ℝ) + 1) ω := by
  obtain ⟨r, hr⟩ := isCompact_Icc.bddAbove_image
    (hc.abs.continuousOn : ContinuousOn (fun t => |A t ω|) (Icc 0 T))
  have hn : ∀ᶠ n : ℕ in atTop, r ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop r)
  filter_upwards [hn] with n hnr
  apply le_rationalExit_of_bound
  intro t ht
  exact (hr (mem_image_of_mem _ ⟨zero_le, ht⟩)).trans (by linarith)

theorem eventually_le_jointExit {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {T : ℝ≥0} (hM : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hA : Continuous (fun t => A t ω)) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ jointExit M A n ω := by
  filter_upwards [eventually_le_posteriorExit hM, eventually_le_compensatorExit hA T]
    with n hn hA
  exact le_min hn hA

end Problem367.PosteriorCompensatorStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEnergyIntegrability
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingCopyEnergy
open IsingObservationInnovation IsingObservationFactor

theorem measurable_responseRow {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (responseRow beta v w) := by
  apply (measurable_infiniteGibbsResponse beta v w).comp
  apply Measurable.of_eval
  intro i
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_snd).prodMk
      (measurable_real_toNNReal.comp measurable_fst))

private theorem projection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ)
    (rho := (observationLaw μ).map (innovationMap beta)) (eta := kernel beta μ) kernel_graphLaw
  cases j
  · exact hr
  · exact hl

private theorem timeProjection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) (T : ℝ) :
    MeasurePreserving (timeProjection (d := d) j)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) :=
  (MeasurePreserving.id _).prod (projection_measurePreserving beta μ j)

theorem density_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => density beta v p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) := by
  have hl := copy_row_energy_integrable hμ hb v true T.coe_nonneg
  have hr := copy_row_energy_integrable hμ hb v false T.coe_nonneg
  have hmap (j : Bool) : Measurable (fun p : ℝ × Joint d =>
      (p.1.toNNReal, projection j p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      ((projection_measurePreserving beta μ j).measurable.comp measurable_snd)
  have hbound := (IsingConditionalCopyBounds.fieldDifference_joint_bounds
    hμ hb kernel_graphLaw T v).1
  apply DiscrepancyEnergy.integrable_noise_add_drift
    (c := fun w p => responseRow beta v w (timeProjection true p))
    (c' := fun w p => responseRow beta v w (timeProjection false p))
    (H := 2 * (T : ℝ) + 2 * (d : ℝ) * beta)
    (fun w => ((measurable_responseRow beta v w).comp
      (timeProjection_measurePreserving beta μ true T).measurable).aestronglyMeasurable)
    (fun w => ((measurable_responseRow beta v w).comp
      (timeProjection_measurePreserving beta μ false T).measurable).aestronglyMeasurable)
    (((measurable_field_joint beta v).comp (hmap true)).sub
      ((measurable_field_joint beta v).comp (hmap false))).aestronglyMeasurable
    (((measurable_posterior_joint beta v).comp (hmap true)).aestronglyMeasurable)
    (((measurable_posterior_joint beta v).comp (hmap false)).aestronglyMeasurable)
    hl.2.1 hr.2.1 (hl.1.and hr.1)
  filter_upwards [hbound] with p hp
  exact ⟨hp, posterior_norm_le_one beta v p.1.toNNReal p.2.2.1,
    posterior_norm_le_one beta v p.1.toNNReal p.2.2.2⟩

end Problem367.IsingCopyEnergy

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

lemma copyProjection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ) (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  cases j
  · exact hr
  · exact hl

 theorem copyContinuousPosterior_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) (j : Bool) :
    (∀ᵐ q ∂copies beta μ, Continuous (fun t => copyContinuousPosterior beta v j t q)) ∧
      (∀ t, copyContinuousPosterior beta v j t =ᵐ[copies beta μ]
        (fun q => posterior beta v t (projection j q))) := by
  obtain ⟨hc, he⟩ := continuousPosterior_modification hd hμ hb hcrit v
  have hp := (copyProjection_measurePreserving beta μ j).quasiMeasurePreserving
  exact ⟨hp.ae hc, fun t => hp.ae (he t)⟩

 theorem copyContinuousPosterior_compact
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) (j : Bool) :
    ∀ᵐ q ∂copies beta μ, ∀ T : ℝ≥0,
      ∃ r < (1 : ℝ), ∀ t ≤ T, |copyContinuousPosterior beta v j t q| ≤ r := by
  filter_upwards [(copyContinuousPosterior_modification hd hμ hb hcrit v j).1] with q hc
  intro T
  obtain ⟨r, hr0, hr1, hr⟩ := PosteriorInteriorLocalization.exists_uniform_radius_of_compact
    (s := Icc (0 : ℝ≥0) T) isCompact_Icc hc.continuousOn
    (fun t _ => continuousPosterior_interior beta v t (projection j q))
  exact ⟨r, hr1, fun t ht => hr t ⟨zero_le, ht⟩⟩

 theorem copyResponseEnergy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseEnergy beta v j p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) :=
  (copy_row_energy_integrable hμ hb v j T.coe_nonneg).2.1

 theorem commonResponseCompensator_continuous
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t => commonResponseCompensator beta v t q) := by
  apply ae_continuous_nnrealTimePrimitive_of_joint
  intro n
  have hi := (copyResponseEnergy_integrable hμ hb v true (n : ℝ≥0)).add
    (copyResponseEnergy_integrable hμ hb v false (n : ℝ≥0))
  exact hi

 theorem ae_eventually_le_commonPosteriorExit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop,
      (T : WithTop ℝ≥0) ≤ commonPosteriorExit beta v n q := by
  filter_upwards [copyContinuousPosterior_compact hd hμ hb hcrit v true,
    copyContinuousPosterior_compact hd hμ hb hcrit v false,
    commonResponseCompensator_continuous hμ hb v] with q hl hr hA
  filter_upwards [eventually_le_jointExit (hl T) hA,
    eventually_le_jointExit (hr T) hA] with n hn hn'
  exact le_min hn hn'

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalLocalSquare
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
open IsingObservationInnovation IsingCopyEnergy

 theorem continuousField_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousField beta v 0 =ᵐ[observationLaw μ] 0 := by
  filter_upwards [continuousPosterior_initial_zero hd hμ hb hcrit v] with x hx
  have he := artanh_continuousPosterior beta v 0 x
  rw [hx] at he
  simpa only [Pi.zero_apply, Real.artanh_zero] using he.symm

 theorem continuousDifference_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousDifference beta v 0 =ᵐ[copies beta μ] 0 := by
  have h0 := continuousField_initial_zero hd hμ hb hcrit v
  filter_upwards [(copyProjection_measurePreserving beta μ true).quasiMeasurePreserving.ae h0,
    (copyProjection_measurePreserving beta μ false).quasiMeasurePreserving.ae h0] with q hl hr
  change continuousField beta v 0 q.2.1 - continuousField beta v 0 q.2.2 = 0
  change continuousField beta v 0 q.2.1 = 0 at hl
  change continuousField beta v 0 q.2.2 = 0 at hr
  rw [hl, hr, sub_self]

theorem actual_variance_analysis_of_common_local_square_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (T : ℝ≥0)
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess (continuousDifference beta v)
        (commonPosteriorExit beta v n) t q) ^ 2 ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ commonPosteriorExit beta v n q
          then density beta v s q else 0 ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ q,
        (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
          ∂copies beta μ) t = ∫ q, density beta v t q ∂copies beta μ) := by
  obtain ⟨hc, hver⟩ := continuousDifference_modification hd hμ hb hcrit v
  have hprog := DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
    ContinuousCopyBrownian.joinedFiltration.le_rightCont
    (continuousDifference_progressive beta v)
  have hτ := isLocalizingSequence_commonPosteriorExit hd hμ hb hcrit v
  apply field_difference_energy_analysis_of_stopped_version hμ hb v hprog hc hver
    hτ.isStoppingTime (ae_eventually_le_commonPosteriorExit hd hμ hb hcrit v T)
    (density_integrable hμ hb v T)
  have hzero : (∫ q, (continuousDifference beta v 0 q) ^ 2 ∂copies beta μ) = 0 := by
    calc
      _ = ∫ _q, (0 : ℝ) ∂copies beta μ := integral_congr_ae
        ((continuousDifference_initial_zero hd hμ hb hcrit v).mono (fun q hq => by
          change continuousDifference beta v 0 q = 0 at hq
          rw [hq, zero_pow (by decide : 2 ≠ 0)]))
      _ = 0 := integral_zero _ _
  intro n t ht
  rw [hzero, zero_add]
  exact hlocal n t ht

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square_oai := @OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square_oai
