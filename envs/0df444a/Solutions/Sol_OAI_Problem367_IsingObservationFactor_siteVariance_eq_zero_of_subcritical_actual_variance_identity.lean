-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:41.213833+00:00
-- url     : https://prove2.me/submissions/d429badb-884d-415d-808d-b50f1260c631

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopySpectral_norm_cavityLogDifference_sq_le

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LeafDeletion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem inducedEdges_eq_insert_erase_of_unique_lower_neighbor
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hleaf : ∀ x ∈ D, treeAdj v x → x = p) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have hyp := hleaf y hy hxy
      subst y
      omega
    by_cases hyv : y = v
    · exact Or.inl ⟨hleaf x hx ((hyv ▸ hxy).elim Or.inr Or.inl), hyv⟩
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem tendsto_conditional_covariance_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[fun x => f x * g x | ℱ n]) ω -
        (μ[f | ℱ n]) ω * (μ[g | ℱ n]) ω)
      atTop (𝓝 ((μ[fun x => f x * g x | ⨆ n, ℱ n]) ω -
        (μ[f | ⨆ n, ℱ n]) ω * (μ[g | ⨆ n, ℱ n]) ω)) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (fun x => f x * g x),
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g] with ω hfg hf hg
  exact hfg.sub (hf.mul hg)

end Problem367

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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_LogOdds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityMessage_eq_half_log_cosh_ratio (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (1 / 2 : ℝ) * Real.log (Real.cosh (z + beta) / Real.cosh (z - beta)) := by
  have htheta_sq : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hmem := cavityMessage_argument_mem htheta_sq z
  have hratio : (1 + Real.tanh beta * Real.tanh z) /
      (1 - Real.tanh beta * Real.tanh z) =
      Real.cosh (z + beta) / Real.cosh (z - beta) := by
    apply (div_eq_div_iff (by linarith [hmem.2]) (Real.cosh_pos (z - beta)).ne').2
    rw [Real.cosh_add, Real.cosh_sub]
    simp only [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [cavityMessage, Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio]

theorem cavityMessage_eq_log_cosh_sub (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 := by
  rw [cavityMessage_eq_half_log_cosh_ratio beta,
    Real.log_div (Real.cosh_pos (z + beta)).ne' (Real.cosh_pos (z - beta)).ne']
  ring

theorem tanh_field_difference_eq (beta z : ℝ) :
    (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2 =
      Real.tanh beta * (1 - Real.tanh z ^ 2) /
        (1 - Real.tanh beta ^ 2 * Real.tanh z ^ 2) := by
  have hp := ((Real.hasDerivAt_cosh (z + beta)).comp z
    ((hasDerivAt_id z).add_const beta)).log (Real.cosh_pos (z + beta)).ne'
  have hm := ((Real.hasDerivAt_cosh (z - beta)).comp z
    ((hasDerivAt_id z).sub_const beta)).log (Real.cosh_pos (z - beta)).ne'
  simp only [id_eq, mul_one, Function.comp_apply, ← Real.tanh_eq_sinh_div_cosh] at hp hm
  have h : HasDerivAt (cavityMessage (Real.tanh beta))
      ((Real.tanh (z + beta) - Real.tanh (z - beta)) / 2) z := by
    apply ((hp.sub hm).div_const 2).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => cavityMessage_eq_log_cosh_sub beta x
  simpa only [responseAttenuation, mul_div_assoc] using
    h.unique (hasDerivAt_cavityMessage (Real.tanh_sq_lt_one beta).le z)

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

theorem solve_swap (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    solve hψ hθ z.swap = (solve hψ hθ z).swap := by
  apply solve_eq hψ hθ
  exact ⟨(solve_spec hψ hθ z).2, (solve_spec hψ hθ z).1⟩

end CavityPair
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Homeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityFromSites_eq {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    {z p : ℝ × ℝ}
    (hp : p.1 + cavityMessage theta p.2 = z.1 ∧
      p.2 + cavityMessage theta p.1 = z.2) : cavityFromSites h0 h1 z = p :=
  CavityPair.solve_eq (lipschitzWith_cavityMessage h0 h1.le) h1 hp

theorem cavityFromSites_swap {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 z.swap = (cavityFromSites h0 h1 z).swap :=
  CavityPair.solve_swap (lipschitzWith_cavityMessage h0 h1.le) h1 z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_AttenuationMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma log_responseAttenuation_sub_sq_le {theta x y : ℝ} (hθ : theta ^ 2 ≤ 1) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * (x - y) ^ 2 := by
  have h := (lipschitzWith_log_responseAttenuation hθ).dist_le_mul x y
  have ha : |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      2 * |x - y| := by simpa [Real.dist_eq] using h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (abs_nonneg (x - y)))).mpr ha
  norm_num [mul_pow, sq_abs] at hs ⊢
  exact hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {Y Y' : Ω → ℝ}

lemma integrable_log_responseAttenuation_sub_sq
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ) :
    Integrable (fun w =>
      (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2) μ := by
  have hm : Measurable (fun x => Real.log (responseAttenuation theta x)) :=
    (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  apply (hInt.const_mul 4).mono'
    (((hm.comp hY).sub (hm.comp hY')).pow_const 2).aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_responseAttenuation_sub_sq_le hθ

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_AttenuationProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem prod_responseAttenuation_pos {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    0 < ∏ i ∈ s, responseAttenuation theta (z i) := by
  exact Finset.prod_pos (fun i _ => responseAttenuation_pos htheta (z i))

theorem prod_attenuation_le_one {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    ∏ i ∈ s, responseAttenuation theta (z i) ≤ 1 := by
  exact Finset.prod_le_one (fun index _ => le_of_lt (responseAttenuation_pos htheta (z index)))
    (fun i _ => responseAttenuation_le_one htheta (z i))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem field_reverse (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H w v = (cavityFromSites h0 h1 (H v, H w)).2 := by
  exact congrArg Prod.fst (cavityFromSites_swap h0 h1 (H v, H w))

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InhomogeneousSpinChain
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

theorem weight_eq_prod (K : ℕ → A → A → ℝ) (n : ℕ)
    (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n,
      K i ((Fin.cons a x : Fin (n + 1) → A) i.castSucc) (x i) := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

@[simp] theorem jointWeight_cons (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (a : A) (x : Fin n → A) :
    jointWeight K w n (Fin.cons a x) = w a * weight K n a x := by
  rw [weight_eq_prod]
  simp [jointWeight]

variable [Fintype A]

theorem expectation_succ (K : ℕ → A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n + 1) f a =
      ∑ b, K 0 a b * expectation (fun i => K (i + 1)) n f b := by
  unfold expectation
  rw [FiniteChain.sum_cons]
  simp only [weight_cons, FiniteChain.endpoint_cons, mul_assoc, Finset.mul_sum]

theorem sum_weight (K : ℕ → A → A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) (a : A) :
    ∑ x : Fin n → A, weight K n a x = 1 := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [FiniteChain.sum_cons]
    simp only [weight_cons, ← Finset.mul_sum]
    simp only [ih (fun i => K (i + 1)) (fun i => hK (i + 1)), mul_one]
    exact hK 0 a

theorem sum_jointWeight (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (hw : ∑ a, w a = 1) (n : ℕ) :
    ∑ x : Fin (n + 1) → A, jointWeight K w n x = 1 := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, ← Finset.mul_sum, sum_weight K hK, mul_one]
  exact hw

theorem sum_jointWeight_endpoints (K : ℕ → A → A → ℝ) (w f g : A → ℝ) (n : ℕ) :
    (∑ x : Fin (n + 1) → A,
      jointWeight K w n x * f (x 0) * g (x (Fin.last n))) =
    ∑ a, w a * f a * expectation K n g a := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero, ← FiniteChain.endpoint_eq_last]
  apply Finset.sum_congr rfl
  intro a _
  rw [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_affine (K : ℕ → A → A → ℝ) (f : A → ℝ)
    (p q : ℕ → ℝ) (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    ∃ c : ℝ, ∀ a, expectation K n f a =
      c + (∏ i ∈ Finset.range n, q i) * f a := by
  induction n generalizing K p q with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (fun i => K (i + 1))
      (fun i => p (i + 1)) (fun i => q (i + 1))
      (fun i => hK (i + 1)) (fun i => hmean (i + 1))
    let Q := ∏ i ∈ Finset.range n, q (i + 1)
    refine ⟨c + Q * p 0, ?_⟩
    intro a
    rw [expectation_succ]
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    have hconst : (∑ b, K 0 a b * c) = c := by
      rw [← Finset.sum_mul, hK, one_mul]
    have hlinear : (∑ b, K 0 a b * (Q * f b)) =
        Q * (p 0 + q 0 * f a) := by
      calc
        _ = Q * ∑ b, K 0 a b * f b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [hmean]
    change (∑ b, K 0 a b * c) + (∑ b, K 0 a b * (Q * f b)) = _
    rw [hconst, hlinear, Finset.prod_range_succ']
    dsimp [Q]
    ring

theorem covariance_eq_variance_mul_prod
    (K : ℕ → A → A → ℝ) (f : A → ℝ) (p q : ℕ → ℝ)
    (w : A → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    (∑ a, w a * f a * expectation K n f a) -
      (∑ a, w a * f a) * (∑ a, w a * expectation K n f a) =
    ((∑ a, w a * (f a) ^ 2) - (∑ a, w a * f a) ^ 2) *
      (∏ i ∈ Finset.range n, q i) := by
  obtain ⟨c, hc⟩ := expectation_affine K f p q hK hmean n
  let Q := ∏ i ∈ Finset.range n, q i
  have hfirst : (∑ a, w a * expectation K n f a) =
      c + Q * (∑ a, w a * f a) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    calc
      _ = (∑ a, w a) * c + Q * (∑ a, w a * f a) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [hw, one_mul]
  have hsecond : (∑ a, w a * f a * expectation K n f a) =
      c * (∑ a, w a * f a) + Q * (∑ a, w a * (f a) ^ 2) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  rw [hfirst, hsecond]
  dsimp [Q]
  ring

end Problem367.InhomogeneousChain

namespace Problem367.PosteriorChain

theorem transition_spinMean_affine (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b * spinSign b =
      intercept beta z + slope beta z * spinSign a := by
  rw [transition_spinMean]
  cases a <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one,
    ← sub_eq_add_neg, intercept, slope] <;> ring

theorem slope_eq_responseAttenuation (beta z : ℝ) :
    slope beta z = Real.tanh beta * responseAttenuation (Real.tanh beta) z := by
  simpa only [slope, responseAttenuation, mul_div_assoc] using
    tanh_field_difference_eq beta z

theorem covariance_eq_response_product (beta : ℝ) (z : ℕ → ℝ)
    (w : IsingSpin → ℝ) (hw : ∑ a, w a = 1) (n : ℕ) :
    (∑ a, w a * spinSign a *
      InhomogeneousChain.expectation (fun i => transition beta (z i)) n spinSign a) -
      (∑ a, w a * spinSign a) *
        (∑ a, w a * InhomogeneousChain.expectation
          (fun i => transition beta (z i)) n spinSign a) =
    (1 - (∑ a, w a * spinSign a) ^ 2) * Real.tanh beta ^ n *
      (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta) (z i)) := by
  have h := InhomogeneousChain.covariance_eq_variance_mul_prod
    (fun i => transition beta (z i)) spinSign
    (fun i => intercept beta (z i)) (fun i => slope beta (z i)) w hw
    (fun i => transition_sum beta (z i))
    (fun i => transition_spinMean_affine beta (z i)) n
  simp only [spinSign_sq, mul_one, hw] at h
  rw [h]
  simp_rw [slope_eq_responseAttenuation]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  ring

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_BinaryMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PosteriorChain

private theorem tanh_add_ratio (x y : ℝ) :
    Real.tanh (x + y) =
      (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  have hm := cavityMessage_argument_mem (Real.tanh_sq_lt_one x).le y
  have hd : 1 + Real.tanh x * Real.tanh y ≠ 0 := by linarith [hm.1]
  apply (eq_div_iff hd).2
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.sinh_add, Real.cosh_add]
  ring

private theorem tanh_sub_ratio (x y : ℝ) :
    Real.tanh (x - y) =
      (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  simpa only [sub_eq_add_neg, Real.tanh_neg, mul_neg] using tanh_add_ratio x (-y)

theorem affine_mean_eq_cavity_mean (beta z H : ℝ) :
    intercept beta z + slope beta z * Real.tanh H =
      Real.tanh (z + cavityMessage (Real.tanh beta)
        (H - cavityMessage (Real.tanh beta) z)) := by
  have htheta : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hinner : Real.tanh (cavityMessage (Real.tanh beta) z) =
      Real.tanh beta * Real.tanh z :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta z)
  have houter : Real.tanh (cavityMessage (Real.tanh beta)
      (H - cavityMessage (Real.tanh beta) z)) =
      Real.tanh beta * Real.tanh (H - cavityMessage (Real.tanh beta) z) :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta _)
  rw [tanh_add_ratio, houter, tanh_sub_ratio H, hinner]
  unfold intercept slope
  rw [tanh_add_ratio, tanh_sub_ratio]
  have hz := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le beta
  have hh := cavityMessage_argument_mem (Real.tanh_sq_lt_one H).le
    (cavityMessage (Real.tanh beta) z)
  rw [hinner] at hh
  have hdplus : 1 + Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.1]
  have hdminus : 1 - Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.2]
  have hdinner : 1 - Real.tanh H * (Real.tanh beta * Real.tanh z) ≠ 0 := by
    linarith [hh.2]
  have hout := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le
    (cavityMessage (Real.tanh beta) (H - cavityMessage (Real.tanh beta) z))
  rw [houter, tanh_sub_ratio H, hinner] at hout
  have hdouter : 1 + Real.tanh z * (Real.tanh beta *
      ((Real.tanh H - Real.tanh beta * Real.tanh z) /
        (1 - Real.tanh H * (Real.tanh beta * Real.tanh z)))) ≠ 0 := by
    linarith [hout.1]
  apply (eq_div_iff hdouter).2
  have hdinner' : 1 - Real.tanh z * Real.tanh beta * Real.tanh H ≠ 0 := by
    convert hdinner using 1
    all_goals try with_reducible_and_instances rfl
    ring
  field_simp [hdplus, hdminus, hdinner, hdinner']
  ring

theorem cavityFromSites_affine_mean {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H)) =
        (H - cavityMessage (Real.tanh beta) z, z) := by
  apply cavityFromSites_eq
  constructor
  · ring
  · simp only [affine_mean_eq_cavity_mean, Real.artanh_tanh]

theorem cavityFromSites_affine_mean_snd {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H))).2 = z := by
  rw [cavityFromSites_affine_mean hbeta]

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CovarianceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_ae_posteriorCovariance (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorCovariance μ (F n) f g ω) atTop
      (𝓝 (posteriorCovariance μ (⨆ n, F n) f g ω)) := by
  exact tendsto_conditional_covariance_ae μ F f g

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

private theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem measurable_infiniteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v w : TreeVertex d) : Measurable (infiniteCavityField hbeta v w) := by
  exact (CavityArray.measurable_field_apply _ _ v w).comp
    (Measurable.of_eval (fun u => measurable_artanh.comp
      (measurable_infiniteGibbsSpinMean beta u)))

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.exhaustionSiteField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n))
    (hex : ∀ u, ∃ n, u ∈ D n) (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteSiteField beta (D n) ⟨v, hv n⟩ (observation t p))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v (observation t p)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  have hce (n : ℕ) := hμ.finiteObservation_condExp (D n) (hconn n) t
    (fun eta => spinSign (eta ⟨v, hv n⟩))
  filter_upwards [hlim, ae_all_iff.mpr hce,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp hce hinf
  convert hp.2.2 using 1
  · ext n
    exact congrArg Real.artanh (hce n).symm
  · exact congrArg (fun x : ℝ => 𝓝 (Real.artanh x)) hinf

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback_ae {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    pullback hp f =ᵐ[ν] fun z => f (p z) :=
  Lp.coeFn_compMeasurePreserving f hp

theorem operator_ae {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f =ᵐ[ν] fun z => f (p z) - f (q z) := by
  have hd := Lp.coeFn_sub (pullback hp f) (pullback hq f)
  exact hd.trans ((pullback_ae hp f).sub (pullback_ae hq f))

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Comparison
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Real MeasureTheory

namespace Problem367

theorem eq_zero_of_ae_deriv_le_mul_self {V : ℝ → ℝ} {a b C : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc a b → deriv V t ≤ C * V t) :
    ∀ t ∈ Icc a b, V t = 0 := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  let E : ℝ → ℝ := fun x => Real.exp (-C * x)
  let G : ℝ → ℝ := fun x => E x * V x
  have hEsmooth : ContDiff ℝ 1 E := by dsimp [E]; fun_prop
  have hEac : AbsolutelyContinuousOnInterval E a b :=
    hEsmooth.contDiffOn.absolutelyContinuousOnInterval
  have hGac : AbsolutelyContinuousOnInterval G a b := hEac.fun_mul hV
  have hGderiv : ∀ᵐ x : ℝ, x ∈ Icc a b → deriv G x ≤ 0 := by
    filter_upwards [hV.ae_differentiableAt, hderiv] with x hdiff hle hx
    have hVdiff : DifferentiableAt ℝ V x := hdiff (by simpa [uIcc_of_le hab] using hx)
    have hEdiff : HasDerivAt E (Real.exp (-C * x) * (-C)) x := by
      simpa [E, mul_comm] using ((hasDerivAt_id x).const_mul (-C)).exp
    have hGdiff := hEdiff.mul hVdiff.hasDerivAt
    change deriv (E * V) x ≤ 0
    rw [hGdiff.deriv]
    have hb := hle hx
    dsimp [E]
    nlinarith [Real.exp_pos (-C * x)]
  have hsub : uIcc a t ⊆ uIcc a b := by
    simp only [uIcc_of_le ht.1, uIcc_of_le hab]
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hGat := hGac.mono hsub
  have hint : (∫ x in a..t, deriv G x) ≤ 0 := by
    calc
      _ ≤ ∫ x in a..t, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_ae_restrict ht.1
          hGat.intervalIntegrable_deriv intervalIntegrable_const
        apply (ae_restrict_iff' measurableSet_Icc).2
        filter_upwards [hGderiv] with x hx hxat
        exact hx ⟨hxat.1, hxat.2.trans ht.2⟩
      _ = 0 := by simp
  rw [hGat.integral_deriv_eq_sub] at hint
  have hprod : Real.exp (-C * t) * V t ≤ 0 := by
    simpa [G, E, ha] using hint
  exact le_antisymm ((mul_le_mul_iff_right₀ (Real.exp_pos (-C * t))).1 (by simpa using hprod))
    (hnonneg t ht)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialSummability
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem summable_radial_iff (d : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable (fun v : TreeVertex d => f v.1.length) ↔
      Summable (fun n : ℕ => (Fintype.card (TreeShell d n) : ℝ) * f n) := by
  rw [← (treeShellSigmaEquiv d).summable_iff]
  change Summable (fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length) ↔ _
  rw [summable_sigma_of_nonneg
    (f := fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length)
    (fun s => hf s.2.1.1.length)]
  simp only [tsum_treeShell_radial]
  exact and_iff_right (fun _ => (hasSum_fintype _).summable)

theorem tsum_radial (d : ℕ) (f : ℕ → ℝ)
    (hf : Summable (fun v : TreeVertex d => f v.1.length)) :
    (∑' v : TreeVertex d, f v.1.length) =
      ∑' n : ℕ, (Fintype.card (TreeShell d n) : ℝ) * f n := by
  have hs := (treeShellSigmaEquiv d).summable_iff.mpr hf
  calc
    (∑' v : TreeVertex d, f v.1.length) =
        ∑' s : Σ n : ℕ, TreeShell d n, f s.2.1.1.length :=
      ((treeShellSigmaEquiv d).tsum_eq (fun v : TreeVertex d => f v.1.length)).symm
    _ = ∑' n : ℕ, ∑' v : TreeShell d n, f v.1.1.length := hs.tsum_sigma
    _ = _ := by simp only [tsum_treeShell_radial]

theorem summable_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    Summable (fun v : TreeVertex d => q ^ v.1.length) := by
  apply (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mpr
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun n : ℕ => ((d - 1 : ℕ) * q) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch
  have h := hgeom.mul_left ((d : ℝ) * q)
  refine h.congr fun n => ?_
  simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
  ring

theorem summable_norm_sq_of_radial_bound {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {theta : ℝ}
    (hbranch : (d - 1 : ℕ) * theta ^ 2 < 1)
    (c : TreeVertex d → E) (hc : ∀ v, ‖c v‖ ≤ theta ^ v.1.length) :
    Summable (fun v => ‖c v‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun v => sq_nonneg ‖c v‖) (fun v => ?_)
    (summable_geometric_radial d (sq_nonneg theta) hbranch)
  calc
    ‖c v‖ ^ 2 ≤ (theta ^ v.1.length) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc v) 2
    _ = (theta ^ 2) ^ v.1.length := by simp only [← pow_mul, Nat.mul_comm]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoupledPathProducts
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

private theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have hcancel : a * (b / a) = b := by field_simp
  nlinarith

theorem abs_sub_le_max_mul_abs_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| ≤ max a b * |Real.log a - Real.log b| := by
  rcases le_total b a with hba | hab
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba))]
    exact sub_le_mul_log_sub ha hb
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab))]
    have h := sub_le_mul_log_sub hb ha
    nlinarith

theorem positive_sub_sq_le_log_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 ≤ (a ^ 2 + b ^ 2) * (Real.log a - Real.log b) ^ 2 := by
  have h := abs_sub_le_max_mul_abs_log_sub ha hb
  have hmax : 0 ≤ max a b := le_trans ha.le (le_max_left _ _)
  have hs := (sq_le_sq₀ (abs_nonneg (a - b))
    (mul_nonneg hmax (abs_nonneg _))).2 h
  rw [sq_abs, mul_pow, sq_abs] at hs
  have hmaxsq : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total b a with hba | hab
    · rw [max_eq_left hba]
      nlinarith [sq_nonneg b]
    · rw [max_eq_right hab]
      nlinarith [sq_nonneg a]
  exact hs.trans (mul_le_mul_of_nonneg_right hmaxsq (sq_nonneg _))

theorem abs_sq_sub_sq_le_log_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a ^ 2 - b ^ 2| ≤ 2 * (a ^ 2 + b ^ 2) * |Real.log a - Real.log b| := by
  have h := abs_sub_le_max_mul_abs_log_sub (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  rw [Real.log_pow, Real.log_pow, ← mul_sub, abs_mul] at h
  norm_num at h
  have hmax : max (a ^ 2) (b ^ 2) ≤ a ^ 2 + b ^ 2 := by
    exact max_le (by nlinarith [sq_nonneg b]) (by nlinarith [sq_nonneg a])
  calc
    |a ^ 2 - b ^ 2| ≤ max (a ^ 2) (b ^ 2) * (2 * |Real.log a - Real.log b|) := h
    _ ≤ (a ^ 2 + b ^ 2) * (2 * |Real.log a - Real.log b|) :=
      mul_le_mul_of_nonneg_right hmax (by positivity)
    _ = _ := by ring

theorem log_prod_responseAttenuation_sub {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Real.log (∏ i ∈ s, responseAttenuation theta (x i)) -
        Real.log (∏ i ∈ s, responseAttenuation theta (y i)) =
      ∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i))) := by
  rw [Real.log_prod (fun i _ => (responseAttenuation_pos hθ (x i)).ne'),
    Real.log_prod (fun i _ => (responseAttenuation_pos hθ (y i)).ne'),
    Finset.sum_sub_distrib]

theorem prod_responseAttenuation_sub_sq_le {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ((∏ i ∈ s, responseAttenuation theta (x i)) -
        (∏ i ∈ s, responseAttenuation theta (y i))) ^ 2 ≤
      ((∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 +
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i)))) ^ 2 := by
  have h := positive_sub_sq_le_log_weight
    (prod_responseAttenuation_pos s x hθ) (prod_responseAttenuation_pos s y hθ)
  rwa [log_prod_responseAttenuation_sub s x y hθ] at h

theorem abs_prod_responseAttenuation_sq_sub_sq_le {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    |(∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 -
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2| ≤
      2 * ((∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 +
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2) *
      |∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i)))| := by
  have h := abs_sq_sub_sq_le_log_weight
    (prod_responseAttenuation_pos s x hθ) (prod_responseAttenuation_pos s y hθ)
  rwa [log_prod_responseAttenuation_sub s x y hθ] at h

section Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_sq_sum_le_card_sq (s : Finset ι) (D : ι → Ω → ℝ)
    (hD : ∀ i ∈ s, MemLp (D i) 2 μ) {S : ℝ}
    (hS : ∀ i ∈ s, (∫ ω, D i ω ^ 2 ∂μ) ≤ S) :
    (∫ ω, (∑ i ∈ s, D i ω) ^ 2 ∂μ) ≤ (s.card : ℝ) ^ 2 * S := by
  have hSum : MemLp (fun ω => ∑ i ∈ s, D i ω) 2 μ := memLp_finsetSum s hD
  have hInt := integrable_finsetSum s (fun i hi => (hD i hi).integrable_sq)
  calc
    (∫ ω, (∑ i ∈ s, D i ω) ^ 2 ∂μ) ≤
        ∫ ω, (s.card : ℝ) * ∑ i ∈ s, D i ω ^ 2 ∂μ := by
      apply integral_mono hSum.integrable_sq (hInt.const_mul _)
      intro ω
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => D i ω)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∫ ω, D i ω ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum s (fun i hi => (hD i hi).integrable_sq)]
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, S := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hS) (Nat.cast_nonneg _)
    _ = (s.card : ℝ) ^ 2 * S := by simp [pow_two, mul_assoc]

theorem measurable_responseAttenuation (theta : ℝ) : Measurable (responseAttenuation theta) := by
  have ht : Measurable Real.tanh := lipschitzWith_tanh_response.continuous.measurable
  exact (measurable_const.sub (ht.pow_const 2)).div
    (measurable_const.sub (measurable_const.mul (ht.pow_const 2)))

theorem measurable_prod_responseAttenuation (s : Finset ι) (theta : ℝ)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)) :=
  s.measurable_prod (fun i hi => (measurable_responseAttenuation theta).comp (hX i hi))

theorem memLp_sum_log_responseAttenuation_sub (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    MemLp (fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))) 2 μ := by
  apply memLp_finsetSum s
  intro i hi
  have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  exact (memLp_two_iff_integrable_sq
    (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
      (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))

theorem integral_prod_responseAttenuation_sub_sq_le (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ ∧
      Integrable (fun ω => (P ω - P' ω) ^ 2) μ ∧
      (∫ ω, (P ω - P' ω) ^ 2 ∂μ) ≤
        ∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ := by
  dsimp only
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hZ : MemLp Z 2 μ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  have hweight (ω : Ω) : P ω ^ 2 + P' ω ^ 2 ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    nlinarith
  have hQ : Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ := by
    apply (hZ.integrable_sq.const_mul 2).mono'
      (((hP.pow_const 2).add (hP'.pow_const 2)).aestronglyMeasurable.mul
        (hZ.aestronglyMeasurable.pow 2))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hweight ω) (sq_nonneg _)
  have hpoint (ω : Ω) : (P ω - P' ω) ^ 2 ≤ (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 :=
    prod_responseAttenuation_sub_sq_le s (fun i => X i ω) (fun i => Y i ω) hθ
  have hDiff : Integrable (fun ω => (P ω - P' ω) ^ 2) μ := by
    apply hQ.mono' (((hP.sub hP').pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  exact ⟨hQ, hDiff, integral_mono hDiff hQ hpoint⟩

theorem integral_weighted_path_log_sq_le (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    {S : ℝ}
    (hS : ∀ i ∈ s, (∫ ω, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω))) ^ 2 ∂μ) ≤ S) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * (s.card : ℝ) ^ 2 * S := by
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let D := fun i ω => Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω))
  let Z := fun ω => ∑ i ∈ s, D i ω
  have hQ := (integral_prod_responseAttenuation_sub_sq_le s hθ hX hY hInt).1
  have hD : ∀ i ∈ s, MemLp (D i) 2 μ := by
    intro i hi
    have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
    exact (memLp_two_iff_integrable_sq
      (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
        (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))
  have hZ : MemLp Z 2 μ := memLp_finsetSum s hD
  have hw (ω : Ω) : P ω ^ 2 + P' ω ^ 2 ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    nlinarith
  change (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) ≤ _
  calc
    (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) ≤ ∫ ω, 2 * Z ω ^ 2 ∂μ :=
      integral_mono hQ (hZ.integrable_sq.const_mul 2)
        (fun ω => mul_le_mul_of_nonneg_right (hw ω) (sq_nonneg _))
    _ = 2 * ∫ ω, Z ω ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ 2 * ((s.card : ℝ) ^ 2 * S) :=
      mul_le_mul_of_nonneg_left (integral_sq_sum_le_card_sq s D hD hS) (by norm_num)
    _ = _ := by ring

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoupledPathDrift
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_abs_mul_le_sqrt_moments {U Z : Ω → ℝ}
    (hU : MemLp U 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ ω, |U ω| * |Z ω| ∂μ) ≤
      Real.sqrt (∫ ω, U ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Z ω ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    norm_num [Real.holderConjugate_iff]
  have h := integral_mul_norm_le_Lp_mul_Lq hpq (by simpa using hU) (by simpa using hZ)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using h

theorem integral_weighted_abs_mul_le {U Z w : Ω → ℝ} {C : ℝ}
    (hU : MemLp U 2 μ) (hZ : MemLp Z 2 μ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hwC : ∀ ω, w ω ≤ C) :
    Integrable (fun ω => |U ω| * w ω * |Z ω|) μ ∧
    (∫ ω, |U ω| * w ω * |Z ω| ∂μ) ≤
      Real.sqrt (C * ∫ ω, U ω ^ 2 ∂μ) *
        Real.sqrt (∫ ω, w ω * Z ω ^ 2 ∂μ) := by
  let F := fun ω => U ω * Real.sqrt (w ω)
  let G := fun ω => Z ω * Real.sqrt (w ω)
  have hwt : MemLp (fun ω => Real.sqrt (w ω)) (⊤ : ENNReal) μ := by
    apply memLp_top_of_bound hw.sqrt.aestronglyMeasurable (Real.sqrt C)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hwC ω)
  have hF : MemLp F 2 μ := MeasureTheory.MemLp.mul (hφ := hU) (hf := hwt)
  have hG : MemLp G 2 μ := MeasureTheory.MemLp.mul (hφ := hZ) (hf := hwt)
  have hFsq (ω : Ω) : F ω ^ 2 = w ω * U ω ^ 2 := by
    dsimp [F]
    rw [mul_pow, Real.sq_sqrt (hw0 ω), mul_comm]
  have hGsq (ω : Ω) : G ω ^ 2 = w ω * Z ω ^ 2 := by
    dsimp [G]
    rw [mul_pow, Real.sq_sqrt (hw0 ω), mul_comm]
  have hprod (ω : Ω) : |F ω| * |G ω| = |U ω| * w ω * |Z ω| := by
    dsimp [F, G]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      |U ω| * Real.sqrt (w ω) * (|Z ω| * Real.sqrt (w ω)) =
          |U ω| * |Z ω| * (Real.sqrt (w ω)) ^ 2 := by ring
      _ = |U ω| * w ω * |Z ω| := by rw [Real.sq_sqrt (hw0 ω)]; ring
  have hI : Integrable (fun ω => |U ω| * w ω * |Z ω|) μ := by
    have h := hF.norm.integrable_mul hG.norm
    change Integrable (fun ω => ‖F ω‖ * ‖G ω‖) μ at h
    simpa only [Real.norm_eq_abs, Pi.mul_apply, hprod] using h
  have hcs := integral_abs_mul_le_sqrt_moments hF hG
  simp_rw [hprod, hFsq, hGsq] at hcs
  have hFbound : (∫ ω, w ω * U ω ^ 2 ∂μ) ≤ C * ∫ ω, U ω ^ 2 ∂μ := by
    have hint : Integrable (fun ω => w ω * U ω ^ 2) μ := by
      simpa only [hFsq] using hF.integrable_sq
    calc
      (∫ ω, w ω * U ω ^ 2 ∂μ) ≤ ∫ ω, C * U ω ^ 2 ∂μ :=
        integral_mono hint (hU.integrable_sq.const_mul C)
          (fun ω => mul_le_mul_of_nonneg_right (hwC ω) (sq_nonneg _))
      _ = C * ∫ ω, U ω ^ 2 ∂μ := integral_const_mul _ _
  exact ⟨hI, hcs.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hFbound) (Real.sqrt_nonneg _))⟩

theorem integral_abs_mul_prod_responseAttenuation_sq_sub_sq_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ} {U : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    (hU : MemLp U 2 μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => |U ω| * |P ω ^ 2 - P' ω ^ 2|) μ ∧
      (∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ) ≤
        2 * Real.sqrt (2 * ∫ ω, U ω ^ 2 ∂μ) *
          Real.sqrt (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) := by
  dsimp only
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
  let w := fun ω => P ω ^ 2 + P' ω ^ 2
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hw : Measurable w := (hP.pow_const 2).add (hP'.pow_const 2)
  have hw0 (ω : Ω) : 0 ≤ w ω := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hw2 (ω : Ω) : w ω ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    dsimp only [w]
    nlinarith
  have hZ : MemLp Z 2 μ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  have hbound := integral_weighted_abs_mul_le hU hZ hw hw0 hw2
  have hpoint (ω : Ω) : |U ω| * |P ω ^ 2 - P' ω ^ 2| ≤
      2 * (|U ω| * w ω * |Z ω|) := by
    calc
      |U ω| * |P ω ^ 2 - P' ω ^ 2| ≤ |U ω| * (2 * w ω * |Z ω|) :=
        mul_le_mul_of_nonneg_left
          (abs_prod_responseAttenuation_sq_sub_sq_le s
            (fun i => X i ω) (fun i => Y i ω) hθ) (abs_nonneg _)
      _ = _ := by ring
  have hDiff : Integrable (fun ω => |U ω| * |P ω ^ 2 - P' ω ^ 2|) μ := by
    apply (hbound.1.const_mul 2).mono'
      (hU.aestronglyMeasurable.aemeasurable.abs.aestronglyMeasurable.mul
        (((hP.pow_const 2).sub (hP'.pow_const 2)).abs.aestronglyMeasurable))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hpoint ω
  refine ⟨hDiff, ?_⟩
  calc
    (∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ) ≤
        ∫ ω, 2 * (|U ω| * w ω * |Z ω|) ∂μ :=
      integral_mono hDiff (hbound.1.const_mul 2) hpoint
    _ = 2 * ∫ ω, |U ω| * w ω * |Z ω| ∂μ := integral_const_mul _ _
    _ ≤ 2 * (Real.sqrt (2 * ∫ ω, U ω ^ 2 ∂μ) *
        Real.sqrt (∫ ω, w ω * Z ω ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hbound.2 (by norm_num)
    _ = _ := by ring

theorem integral_mul_prod_responseAttenuation_sq_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X : ι → Ω → ℝ} {U : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hU : MemLp U 2 μ) :
    Integrable (fun ω => U ω ^ 2 *
      (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2) μ ∧
    (∫ ω, U ω ^ 2 * (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 ∂μ) ≤
      ∫ ω, U ω ^ 2 ∂μ := by
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hpoint (ω : Ω) : U ω ^ 2 * P ω ^ 2 ≤ U ω ^ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    change 0 < P ω at hp
    change P ω ≤ 1 at hl
    have hsq : P ω ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hsq (sq_nonneg (U ω))
  have hint : Integrable (fun ω => U ω ^ 2 * P ω ^ 2) μ := by
    apply hU.integrable_sq.mono'
      ((hU.aestronglyMeasurable.pow 2).mul ((hP.pow_const 2).aestronglyMeasurable))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpoint ω
  exact ⟨hint, integral_mono hint hU.integrable_sq hpoint⟩

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SubcriticalPathSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem367

theorem regularPathWeight_eq (d : ℕ) (theta : ℝ) (n : ℕ) :
    regularPathWeight d theta n =
      (d : ℝ) * theta ^ 2 * (((d - 1 : ℕ) : ℝ) * theta ^ 2) ^ n := by
  simp only [regularPathWeight, card_treeShell_succ, Nat.cast_mul, Nat.cast_pow]
  rw [pow_mul, pow_succ, mul_pow]
  ring

theorem regularPathWeight_nonneg (d : ℕ) (theta : ℝ) (n : ℕ) :
    0 ≤ regularPathWeight d theta n := by
  rw [regularPathWeight_eq]
  positivity

theorem summable_regularPathWeight_mul_length_sq
    {d : ℕ} {theta : ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (fun n => regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  let q : ℝ := ((d - 1 : ℕ) : ℝ) * theta ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hsub
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ n) := by
    convert! (h2.add (h1.mul_left 2)).add h0 using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Nat.cast_add, Nat.cast_one, pow_one, pow_zero, one_mul]
    ring
  convert! hs.mul_left ((d : ℝ) * theta ^ 2) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [regularPathWeight_eq]
  dsimp only [q]
  ring

theorem path_noise_drift_le_length_sq
    {Q L V C : ℝ} (n : ℕ) (hQ : 0 ≤ Q) (_hL : 0 ≤ L) (hV : 0 ≤ V)
    (hQbound : Q ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 * V) (hLbound : L ≤ V) :
    Q + 2 * L + 4 * Real.sqrt (2 * V) * Real.sqrt Q ≤
      (3 * C + 6) * ((n + 1 : ℕ) : ℝ) ^ 2 * V := by
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hVr : V ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * V := by
    have hr2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hr2 hV
  have hsV := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV)
  have hsQ := Real.sq_sqrt hQ
  have hcross := sq_nonneg (Real.sqrt (2 * V) - Real.sqrt Q)
  nlinarith

theorem subcritical_noise_drift_bound
    {d : ℕ} {theta C V D : ℝ} {Q L : ℕ → ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1)
    (_hC : 0 ≤ C) (hV : 0 ≤ V)
    (hQ : ∀ n, 0 ≤ Q n) (hL : ∀ n, 0 ≤ L n)
    (hQbound : ∀ n, Q n ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 * V)
    (hLbound : ∀ n, L n ≤ V)
    (hD : D ≤ 2 * V + ∑' n : ℕ, regularPathWeight d theta n *
      (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))) :
    Summable (fun n : ℕ => regularPathWeight d theta n *
      (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))) ∧
      D ≤ subcriticalPathConstant d theta C * V := by
  let f := fun n : ℕ => regularPathWeight d theta n *
    (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))
  let g := fun n : ℕ => ((3 * C + 6) * V) *
    (regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hf0 (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact mul_nonneg (regularPathWeight_nonneg d theta n)
      (add_nonneg (add_nonneg (hQ n) (mul_nonneg (by norm_num) (hL n))) (by positivity))
  have hfg (n : ℕ) : f n ≤ g n := by
    have h := mul_le_mul_of_nonneg_left
      (path_noise_drift_le_length_sq n (hQ n) (hL n) hV (hQbound n) (hLbound n))
      (regularPathWeight_nonneg d theta n)
    calc
      f n ≤ regularPathWeight d theta n *
          ((3 * C + 6) * ((n + 1 : ℕ) : ℝ) ^ 2 * V) := h
      _ = g n := by dsimp only [g] <;> ring
  have hg : Summable g :=
    (summable_regularPathWeight_mul_length_sq hsub).mul_left ((3 * C + 6) * V)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfg hg
  refine ⟨hf, hD.trans ?_⟩
  calc
    2 * V + ∑' n : ℕ, f n ≤ 2 * V + ∑' n : ℕ, g n :=
      add_le_add le_rfl (hf.tsum_le_tsum hfg hg)
    _ = subcriticalPathConstant d theta C * V := by
      dsimp only [g, subcriticalPathConstant]
      rw [tsum_mul_left]
      ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledResponseRows
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem367

theorem abs_tanh_weight_drift_le (h h' p p' : ℝ) :
    |(h - h') * (Real.tanh h * p ^ 2 - Real.tanh h' * p' ^ 2)| ≤
      (h - h') ^ 2 * p ^ 2 + |h - h'| * |p ^ 2 - p' ^ 2| := by
  have hdiff : |Real.tanh h - Real.tanh h'| ≤ |h - h'| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      lipschitzWith_tanh_response.dist_le_mul h h'
  have hm : |Real.tanh h'| ≤ 1 := by
    have hsq := Real.tanh_sq_lt_one h'
    nlinarith [sq_abs (Real.tanh h'), abs_nonneg (Real.tanh h')]
  have hsplit : Real.tanh h * p ^ 2 - Real.tanh h' * p' ^ 2 =
      (Real.tanh h - Real.tanh h') * p ^ 2 +
        Real.tanh h' * (p ^ 2 - p' ^ 2) := by ring
  rw [abs_mul, hsplit]
  calc
    |h - h'| * |(Real.tanh h - Real.tanh h') * p ^ 2 +
        Real.tanh h' * (p ^ 2 - p' ^ 2)| ≤
      |h - h'| * (|(Real.tanh h - Real.tanh h') * p ^ 2| +
        |Real.tanh h' * (p ^ 2 - p' ^ 2)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |h - h'| * (|Real.tanh h - Real.tanh h'| * p ^ 2 +
        |Real.tanh h'| * |p ^ 2 - p' ^ 2|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg p)]
    _ ≤ |h - h'| * (|h - h'| * p ^ 2 + |p ^ 2 - p' ^ 2|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add (mul_le_mul_of_nonneg_right hdiff (sq_nonneg p))
      exact mul_le_of_le_one_left (abs_nonneg _) hm
    _ = _ := by rw [mul_add, ← mul_assoc, ← sq, sq_abs]

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_abs_tanh_path_drift_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => (H ω - H' ω) *
      (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)) μ ∧
    (∫ ω, |(H ω - H' ω) *
      (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)| ∂μ) ≤
      (∫ ω, (H ω - H' ω) ^ 2 * P ω ^ 2 ∂μ) +
        2 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
          Real.sqrt (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) := by
  dsimp only
  let U := fun ω => H ω - H' ω
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω)))
  let D := fun ω => U ω *
    (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hL := (integral_mul_prod_responseAttenuation_sq_le s hθ hX hU).1
  have hB := integral_abs_mul_prod_responseAttenuation_sq_sub_sq_le s hθ hX hY hInt hU
  have htanh := lipschitzWith_tanh_response.continuous.measurable
  have hDm : Measurable D := (hH.sub hH').mul
    (((htanh.comp hH).mul (hP.pow_const 2)).sub
      ((htanh.comp hH').mul (hP'.pow_const 2)))
  have hpoint (ω : Ω) : |D ω| ≤ U ω ^ 2 * P ω ^ 2 +
      |U ω| * |P ω ^ 2 - P' ω ^ 2| :=
    abs_tanh_weight_drift_le (H ω) (H' ω) (P ω) (P' ω)
  have hD : Integrable D μ := by
    apply (hL.add hB.1).mono' hDm.aestronglyMeasurable
    filter_upwards [] with ω
    exact (show ‖D ω‖ ≤ _ by simpa only [Real.norm_eq_abs, Pi.add_apply, U, P, P'] using hpoint ω)
  refine ⟨hD, ?_⟩
  calc
    (∫ ω, |D ω| ∂μ) ≤ ∫ ω, U ω ^ 2 * P ω ^ 2 + |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ :=
      integral_mono hD.abs (hL.add hB.1) hpoint
    _ = (∫ ω, U ω ^ 2 * P ω ^ 2 ∂μ) +
        ∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ := integral_add hL hB.1
    _ ≤ _ := add_le_add le_rfl hB.2

theorem integrable_series_of_summable_integral_abs
    {ι : Type*} [Countable ι] {F : ι → Ω → ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ ω, |F i ω| ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => |F i ω|)) ∧
      Integrable (fun ω => ∑' i, F i ω) μ ∧
      (∫ ω, (∑' i, F i ω) ∂μ) = ∑' i, ∫ ω, F i ω ∂μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal |F i ω|) μ :=
    (hF i).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal |F i ω| ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal |F i ω| ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, |F i ω| ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hF i).abs
          (Filter.Eventually.of_forall (fun ω => abs_nonneg (F i ω)))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hAe : ∀ᵐ ω ∂μ, Summable (fun i => |F i ω|) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
      ENNReal.summable_toReal hω.ne
  have hIabs : Integrable (fun ω => ∑' i, |F i ω|) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
    simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (abs_nonneg _)] using h
  refine ⟨hAe, ?_, ?_⟩
  · apply hIabs.mono' (AEStronglyMeasurable.tsum (fun i => (hF i).aestronglyMeasurable))
    filter_upwards [hAe] with ω hω
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (show Summable (fun i => ‖F i ω‖) by
        simpa only [Real.norm_eq_abs] using hω)
  · exact (integral_tsum_of_summable_integral_norm hF
      (by simpa only [Real.norm_eq_abs] using hs)).symm

theorem integral_series_le_of_abs_majorant
    {ι : Type*} [Countable ι] {F : ι → Ω → ℝ} {B : ι → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hB : Summable B)
    (hbound : ∀ i, (∫ ω, |F i ω| ∂μ) ≤ B i) :
    Integrable (fun ω => ∑' i, F i ω) μ ∧
      |∫ ω, (∑' i, F i ω) ∂μ| ≤ ∑' i, B i := by
  have hs : Summable (fun i => ∫ ω, |F i ω| ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun ω => abs_nonneg _)) hbound hB
  have hseries := integrable_series_of_summable_integral_abs hF hs
  refine ⟨hseries.2.1, ?_⟩
  rw [hseries.2.2]
  have hnorm : Summable (fun i => |∫ ω, F i ω ∂μ|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _)
      (fun i => abs_integral_le_integral_abs) hs
  calc
    |∑' i, ∫ ω, F i ω ∂μ| ≤ ∑' i, |∫ ω, F i ω ∂μ| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (show Summable (fun i => ‖∫ ω, F i ω ∂μ‖) by
          simpa only [Real.norm_eq_abs] using hnorm)
    _ ≤ ∑' i, B i := hnorm.tsum_le_tsum
      (fun i => abs_integral_le_integral_abs.trans (hbound i)) hB

theorem integral_response_row_density_le
    {ι : Type*} [Countable ι]
    {c c' : ι → Ω → ℝ} {U m m' : Ω → ℝ} {N D : ι → ℝ}
    (hnoise : ∀ i, Integrable (fun ω => (c i ω - c' i ω) ^ 2) μ)
    (hdrift : ∀ i, Integrable (fun ω => U ω *
      (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)) μ)
    (hN : Summable N) (hD : Summable D)
    (hNb : ∀ i, (∫ ω, (c i ω - c' i ω) ^ 2 ∂μ) ≤ N i)
    (hDb : ∀ i, (∫ ω, |U ω *
      (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)| ∂μ) ≤ D i)
    (hrows : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2)) :
    Integrable (DiscrepancyEnergy.density c c' U m m') μ ∧
      (∫ ω, DiscrepancyEnergy.density c c' U m m' ω ∂μ) ≤
        (∑' i, N i) + 2 * ∑' i, D i := by
  let A := fun ω => ∑' i, (c i ω - c' i ω) ^ 2
  let B := fun ω => ∑' i, U ω * (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)
  have hAb : ∀ i, (∫ ω, |(c i ω - c' i ω) ^ 2| ∂μ) ≤ N i := by
    simpa only [abs_sq] using hNb
  have hA := integral_series_le_of_abs_majorant hnoise hN hAb
  have hB := integral_series_le_of_abs_majorant hdrift hD hDb
  have heq : DiscrepancyEnergy.density c c' U m m' =ᵐ[μ]
      (fun ω => A ω + 2 * B ω) := by
    filter_upwards [hrows] with ω hω
    have hs : Summable (fun i => (U ω * m ω) * (c i ω) ^ 2) :=
      hω.1.mul_left (U ω * m ω)
    have hs' : Summable (fun i => (U ω * m' ω) * (c' i ω) ^ 2) :=
      hω.2.mul_left (U ω * m' ω)
    have hBω : B ω = U ω *
        (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2)) := by
      calc
        B ω = ∑' i, ((U ω * m ω) * (c i ω) ^ 2 -
            (U ω * m' ω) * (c' i ω) ^ 2) := by
          apply tsum_congr
          intro i
          ring
        _ = _ := by rw [hs.tsum_sub hs', tsum_mul_left, tsum_mul_left]; ring
    dsimp only [DiscrepancyEnergy.density, A]
    rw [hBω]
    ring
  have hint : Integrable (DiscrepancyEnergy.density c c' U m m') μ :=
    (hA.1.add (hB.1.const_mul 2)).congr heq.symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae heq, integral_add hA.1 (hB.1.const_mul 2), integral_const_mul]
  exact add_le_add ((le_abs_self _).trans hA.2)
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hB.2) (by norm_num))

namespace ResponseRows

theorem integral_density_le_path_energies
    {J ι : Type*} [Countable J]
    (s : J → Finset ι) (a : J → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : J → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ j i, i ∈ s j → Measurable (X j i))
    (hY : ∀ j i, i ∈ s j → Measurable (Y j i))
    (hInt : ∀ j i, i ∈ s j → Integrable (fun ω => (X j i ω - Y j i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    (hQsum : Summable (fun j => (a j) ^ 2 * pathNoiseEnergy μ theta (s j) (X j) (Y j)))
    (hLsum : Summable (fun j => (a j) ^ 2 *
      pathLinearEnergy μ theta (s j) (X j) (fun ω => H ω - H' ω)))
    (hRsum : Summable (fun j => (a j) ^ 2 *
      Real.sqrt (pathNoiseEnergy μ theta (s j) (X j) (Y j))))
    (hrows : ∀ᵐ ω ∂μ, Summable (fun j => (coefficient theta a s X j ω) ^ 2) ∧
      Summable (fun j => (coefficient theta a s Y j ω) ^ 2)) :
    Integrable (DiscrepancyEnergy.density (coefficient theta a s X)
      (coefficient theta a s Y) (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density (coefficient theta a s X)
      (coefficient theta a s Y) (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      (∑' j, (a j) ^ 2 * pathNoiseEnergy μ theta (s j) (X j) (Y j)) +
      2 * (∑' j, (a j) ^ 2 * pathLinearEnergy μ theta (s j) (X j) (fun ω => H ω - H' ω)) +
      4 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
        (∑' j, (a j) ^ 2 * Real.sqrt (pathNoiseEnergy μ theta (s j) (X j) (Y j))) := by
  let U := fun ω => H ω - H' ω
  let P := fun j => pathProduct theta (s j) (X j)
  let P' := fun j => pathProduct theta (s j) (Y j)
  let Q := fun j => pathNoiseEnergy μ theta (s j) (X j) (Y j)
  let L := fun j => pathLinearEnergy μ theta (s j) (X j) U
  let V := ∫ ω, U ω ^ 2 ∂μ
  let K := 2 * Real.sqrt (2 * V)
  let F := fun j ω => U ω *
    (Real.tanh (H ω) * P j ω ^ 2 - Real.tanh (H' ω) * P' j ω ^ 2)
  have hfiniteN (j : J) := integral_prod_responseAttenuation_sub_sq_le
    (s j) hθ (hX j) (hY j) (hInt j)
  have hfiniteD (j : J) := integral_abs_tanh_path_drift_le
    (s j) hθ (hX j) (hY j) (hInt j) hH hH' hU
  have hnoiseEq (j : J) (ω : Ω) :
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2 =
        (a j) ^ 2 * (P j ω - P' j ω) ^ 2 := by
    dsimp only [coefficient, P, P']
    ring
  have hdriftEq (j : J) (ω : Ω) : U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2) =
      (a j) ^ 2 * F j ω := by
    dsimp only [coefficient, F, P, P']
    ring
  have hnoise (j : J) : Integrable (fun ω =>
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2) μ := by
    simp_rw [hnoiseEq]
    exact (hfiniteN j).2.1.const_mul _
  have hdrift (j : J) : Integrable (fun ω => U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2)) μ := by
    simp_rw [hdriftEq]
    exact (hfiniteD j).1.const_mul _
  have hNb (j : J) : (∫ ω,
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2 ∂μ) ≤
        (a j) ^ 2 * Q j := by
    simp_rw [hnoiseEq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hfiniteN j).2.2 (sq_nonneg _)
  have hDb (j : J) : (∫ ω, |U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2)| ∂μ) ≤
        (a j) ^ 2 * (L j + K * Real.sqrt (Q j)) := by
    simp_rw [hdriftEq, abs_mul, abs_sq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hfiniteD j).2 (sq_nonneg _)
  have hDsum : Summable (fun j => (a j) ^ 2 * (L j + K * Real.sqrt (Q j))) := by
    convert hLsum.add (hRsum.mul_left K) using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    dsimp only [L, Q, U]
    ring
  have hb := integral_response_row_density_le hnoise hdrift hQsum hDsum hNb hDb hrows
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  have hsumD : (∑' j, (a j) ^ 2 * (L j + K * Real.sqrt (Q j))) =
      (∑' j, (a j) ^ 2 * L j) + K * ∑' j, (a j) ^ 2 * Real.sqrt (Q j) := by
    calc
      _ = ∑' j, ((a j) ^ 2 * L j + K * ((a j) ^ 2 * Real.sqrt (Q j))) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := by rw [hLsum.tsum_add (hRsum.mul_left K), tsum_mul_left]
  rw [hsumD]
  dsimp only [K, V, Q, L, U]
  ring

end ResponseRows

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteLeafCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

theorem expectation_eq_mean_zero {A : Type*} [Fintype A] (E f : A → ℝ) :
    expectation E f = FinitePosterior.mean E (fun _ => 0) f 0 := by
  simp only [expectation, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, zero_mul, add_zero]

end Problem367.LeafGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_ae_posteriorResponse
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f g : Ω → ℝ)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorResponse μ (F n) f g ω) atTop
      (𝓝 (posteriorResponse μ (⨆ n, F n) f g ω)) := by
  filter_upwards [tendsto_ae_posteriorCovariance μ F f g,
    tendsto_ae_condExp (μ := μ) (ℱ := F) f, hinterior] with ω hc hm hi
  have hden : 1 - (μ[f | ⨆ n, F n] ω) ^ 2 ≠ 0 := by
    have hsq : (μ[f | ⨆ n, F n] ω) ^ 2 < 1 := by
      nlinarith [mul_pos (show 0 < 1 - μ[f | ⨆ n, F n] ω by linarith [hi.2])
        (show 0 < 1 + μ[f | ⨆ n, F n] ω by linarith [hi.1])]
    exact ne_of_gt (sub_pos.mpr hsq)
  exact hc.div (tendsto_const_nhds.sub (hm.pow 2)) hden

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
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

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma pairExhaustion_monotone {d : ℕ} (v w : TreeVertex d) :
    Monotone (pairExhaustion v w) := by
  intro n m hnm
  exact connectedExhaustion_monotone v (Nat.add_le_add_right hnm _)

lemma pairExhaustion_connected {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    ConnectedFinset (pairExhaustion v w n) := connectedExhaustion_connected v _

lemma exists_mem_pairExhaustion {d : ℕ} (v w u : TreeVertex d) :
    ∃ n, u ∈ pairExhaustion v w n := by
  obtain ⟨n, hn⟩ := (eventually_mem_connectedExhaustion v u).exists
  exact ⟨n, connectedExhaustion_monotone v (Nat.le_add_right n _) hn⟩

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

lemma spinSign_pair_norm_le_one {d : ℕ} (v w : TreeVertex d)
    (sigma : TreeVertex d → IsingSpin) : ‖spinSign (sigma v) * spinSign (sigma w)‖ ≤ 1 := by
  cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsPairMean beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (pairExhaustion v w n)
    (pairExhaustion_connected v w n) t
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (pairExhaustion v w)
      (pairExhaustion_monotone v w) t)
    (fun p => spinSign (p.1 v) * spinSign (p.1 w))
  rw [finiteObservationFiltration_iSup (pairExhaustion v w)
    (pairExhaustion_monotone v w) (exists_mem_pairExhaustion v w) t] at hlim
  have hb := ae_bdd_norm_condExp_of_ae_bdd_norm
    (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (m := observationSigma (TreeVertex d) t)
    (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  filter_upwards [ae_all_iff.mpr hce, hlim, hb] with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsPairMean beta v w n (observation t p)) atTop
      (𝓝 ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] p)) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hp n).symm
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsCovariance beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (observationSigma (TreeVertex d) t)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.infiniteGibbsSpinMean_eq_posterior t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ResponseRowEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ResponseRows

theorem summable_weighted_tree_profile {d : ℕ} (theta : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n => regularPathWeight d theta n * f (n + 1))) :
    Summable (fun v : TreeVertex d => theta ^ (2 * v.1.length) * f v.1.length) := by
  have hp (n : ℕ) : 0 ≤ theta ^ (2 * n) := by
    rw [pow_mul]
    positivity
  apply (summable_radial_iff d (fun n => theta ^ (2 * n) * f n)
    (fun n => mul_nonneg (hp n) (hf n))).mpr
  apply (summable_nat_add_iff 1).mp
  simpa only [regularPathWeight, mul_assoc] using hs

theorem tsum_weighted_tree_profile {d : ℕ} (theta : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n => regularPathWeight d theta n * f (n + 1))) :
    (∑' v : TreeVertex d, theta ^ (2 * v.1.length) * f v.1.length) =
      f 0 + ∑' n, regularPathWeight d theta n * f (n + 1) := by
  have hrad := summable_weighted_tree_profile theta f hf hs
  rw [tsum_radial d (fun n => theta ^ (2 * n) * f n) hrad]
  have hp (n : ℕ) : 0 ≤ theta ^ (2 * n) * f n := by
    have he : 0 ≤ theta ^ (2 * n) := by rw [pow_mul]; positivity
    exact mul_nonneg he (hf n)
  have hshell := (summable_radial_iff d (fun n => theta ^ (2 * n) * f n) hp).mp hrad
  rw [hshell.tsum_eq_zero_add]
  simp only [card_treeShell_zero, Nat.cast_one, mul_zero, pow_zero, one_mul]
  congr 1
  apply tsum_congr
  intro n
  simp only [regularPathWeight, mul_assoc]

theorem summable_and_tsum_le_shell_budget
    {d : ℕ} (theta : ℝ) {F : TreeVertex d → ℝ} {root : ℝ} {tail : ℕ → ℝ}
    (hF : ∀ v, 0 ≤ F v) (hroot : 0 ≤ root) (htail : ∀ n, 0 ≤ tail n)
    (hs : Summable (fun n => regularPathWeight d theta n * tail n))
    (hzero : ∀ v : TreeVertex d, v.1.length = 0 → F v ≤ root)
    (hpos : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      F v ≤ theta ^ (2 * (n + 1)) * tail n) :
    Summable F ∧ (∑' v, F v) ≤ root + ∑' n, regularPathWeight d theta n * tail n := by
  let f := shellProfile root tail
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    cases n with
    | zero => exact hroot
    | succ n => exact htail n
  have hsum : Summable (fun n => regularPathWeight d theta n * f (n + 1)) := hs
  have hrad := summable_weighted_tree_profile theta f hf hsum
  have hbound (v : TreeVertex d) : F v ≤ theta ^ (2 * v.1.length) * f v.1.length := by
    cases he : v.1.length with
    | zero => simpa only [f, shellProfile_zero, mul_zero, pow_zero, one_mul] using hzero v he
    | succ n => exact hpos n v he
  have hFs := Summable.of_nonneg_of_le hF hbound hrad
  refine ⟨hFs, ?_⟩
  calc
    (∑' v, F v) ≤ ∑' v : TreeVertex d, theta ^ (2 * v.1.length) * f v.1.length :=
      hFs.tsum_le_tsum hbound hrad
    _ = root + ∑' n, regularPathWeight d theta n * tail n :=
      tsum_weighted_tree_profile theta f hf hsum

theorem weighted_energy_shell_bound
    {d : ℕ} (theta : ℝ) {E : TreeVertex d → ℝ} {root : ℝ} {tail : ℕ → ℝ}
    (hE : ∀ v, 0 ≤ E v) (hroot : 0 ≤ root) (htail : ∀ n, 0 ≤ tail n)
    (hs : Summable (fun n => regularPathWeight d theta n * tail n))
    (hzero : ∀ v : TreeVertex d, v.1.length = 0 → E v ≤ root)
    (hpos : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 → E v ≤ tail n) :
    Summable (fun v : TreeVertex d => (theta ^ v.1.length) ^ 2 * E v) ∧
      (∑' v : TreeVertex d, (theta ^ v.1.length) ^ 2 * E v) ≤
        root + ∑' n, regularPathWeight d theta n * tail n := by
  apply summable_and_tsum_le_shell_budget theta
    (fun v => mul_nonneg (sq_nonneg _) (hE v)) hroot htail hs
  · intro v hv
    simpa only [hv, pow_zero, one_pow, one_mul] using hzero v hv
  · intro n v hv
    rw [hv]
    have hp : (theta ^ (n + 1)) ^ 2 = theta ^ (2 * (n + 1)) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hp]
    exact mul_le_mul_of_nonneg_left (hpos n v hv) (by rw [pow_mul]; positivity)

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem pathNoiseEnergy_nonneg {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) : 0 ≤ pathNoiseEnergy μ theta s X Y :=
  integral_nonneg (fun _ => mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))

theorem pathLinearEnergy_nonneg {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X : ι → Ω → ℝ) (U : Ω → ℝ) : 0 ≤ pathLinearEnergy μ theta s X U :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem integral_tree_density_le_shell_energies
    {d : ℕ} {ι : Type*} (s : TreeVertex d → Finset ι)
    (hcard : ∀ v, (s v).card = v.1.length)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : TreeVertex d → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ v i, i ∈ s v → Measurable (X v i))
    (hY : ∀ v i, i ∈ s v → Measurable (Y v i))
    (hInt : ∀ v i, i ∈ s v → Integrable (fun ω => (X v i ω - Y v i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    {Q L : ℕ → ℝ} (hQ0 : ∀ n, 0 ≤ Q n) (hL0 : ∀ n, 0 ≤ L n)
    (hQ : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤ Q n)
    (hL : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      pathLinearEnergy μ theta (s v) (X v) (fun ω => H ω - H' ω) ≤ L n)
    (hQs : Summable (fun n => regularPathWeight d theta n * Q n))
    (hLs : Summable (fun n => regularPathWeight d theta n * L n))
    (hRs : Summable (fun n => regularPathWeight d theta n * Real.sqrt (Q n)))
    (hrows : ∀ᵐ ω ∂μ,
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) ∧
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y v ω) ^ 2)) :
    let c := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X
    let c' := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y
    Integrable (DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      2 * (∫ ω, (H ω - H' ω) ^ 2 ∂μ) + ∑' n, regularPathWeight d theta n *
        (Q n + 2 * L n + 4 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
          Real.sqrt (Q n)) := by
  dsimp only
  let U := fun ω => H ω - H' ω
  let V := ∫ ω, U ω ^ 2 ∂μ
  let A := fun v => pathNoiseEnergy μ theta (s v) (X v) (Y v)
  let B := fun v => pathLinearEnergy μ theta (s v) (X v) U
  let K := 4 * Real.sqrt (2 * V)
  have hV : 0 ≤ V := integral_nonneg (fun ω => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  have hempty (v : TreeVertex d) (hv : v.1.length = 0) : s v = ∅ :=
    Finset.card_eq_zero.mp ((hcard v).trans hv)
  have hA0 (v : TreeVertex d) (hv : v.1.length = 0) : A v = 0 := by
    simp only [A, hempty v hv, pathNoiseEnergy_empty]
  have hB0 (v : TreeVertex d) (hv : v.1.length = 0) : B v = V := by
    simp only [B, hempty v hv, pathLinearEnergy_empty, V]
  have hAb := weighted_energy_shell_bound theta
    (fun v => pathNoiseEnergy_nonneg theta (s v) (X v) (Y v))
    (le_refl (0 : ℝ)) hQ0 hQs (fun v hv => (hA0 v hv).le) hQ
  have hBb := weighted_energy_shell_bound theta
    (fun v => pathLinearEnergy_nonneg theta (s v) (X v) U)
    hV hL0 hLs (fun v hv => (hB0 v hv).le) hL
  have hRb := weighted_energy_shell_bound theta
    (fun v => Real.sqrt_nonneg (A v)) (le_refl (0 : ℝ))
    (fun n => Real.sqrt_nonneg (Q n)) hRs
    (fun v hv => by rw [hA0 v hv, Real.sqrt_zero])
    (fun n v hv => Real.sqrt_le_sqrt (hQ n v hv))
  have hb := integral_density_le_path_energies s (fun v : TreeVertex d => theta ^ v.1.length)
    hθ hX hY hInt hH hH' hU hAb.1 hBb.1 hRb.1 hrows
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hsum : (∑' n, regularPathWeight d theta n *
      (Q n + 2 * L n + K * Real.sqrt (Q n))) =
      (∑' n, regularPathWeight d theta n * Q n) +
      2 * (∑' n, regularPathWeight d theta n * L n) +
      K * (∑' n, regularPathWeight d theta n * Real.sqrt (Q n)) := by
    calc
      _ = ∑' n, ((regularPathWeight d theta n * Q n +
          2 * (regularPathWeight d theta n * L n)) +
          K * (regularPathWeight d theta n * Real.sqrt (Q n))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        rw [(hQs.add (hLs.mul_left 2)).tsum_add (hRs.mul_left K),
          hQs.tsum_add (hLs.mul_left 2), tsum_mul_left, tsum_mul_left]
  change (∑' v, (theta ^ v.1.length) ^ 2 * A v) +
      2 * (∑' v, (theta ^ v.1.length) ^ 2 * B v) +
      K * (∑' v, (theta ^ v.1.length) ^ 2 * Real.sqrt (A v)) ≤ _
  calc
    _ ≤ (0 + ∑' n, regularPathWeight d theta n * Q n) +
        2 * (V + ∑' n, regularPathWeight d theta n * L n) +
        K * (0 + ∑' n, regularPathWeight d theta n * Real.sqrt (Q n)) :=
      add_le_add (add_le_add hAb.2 (mul_le_mul_of_nonneg_left hBb.2 (by norm_num)))
        (mul_le_mul_of_nonneg_left hRb.2 hK)
    _ = 2 * V + ∑' n, regularPathWeight d theta n *
        (Q n + 2 * L n + K * Real.sqrt (Q n)) := by rw [hsum]; ring

end Probability

end Problem367.ResponseRows

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_SubcriticalResponseComparison
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem367.ResponseRows

section Deterministic

variable {Ω ι : Type*}

theorem norm_tree_coefficient_le
    {d : ℕ} {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (s : TreeVertex d → Finset ι) (X : TreeVertex d → ι → Ω → ℝ)
    (v : TreeVertex d) (ω : Ω) :
    ‖coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω‖ ≤
      theta ^ v.1.length := by
  have hp := prod_responseAttenuation_pos (s v) (fun i => X v i ω) hθ
  have hle := prod_attenuation_le_one (s v) (fun i => X v i ω) hθ
  have hw : 0 ≤ theta ^ v.1.length := pow_nonneg hθ0 _
  rw [coefficient, pathProduct, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw,
    abs_of_pos hp]
  exact mul_le_of_le_one_right hw hle

theorem summable_tree_coefficient_sq
    {d : ℕ} {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1)
    (s : TreeVertex d → Finset ι) (X : TreeVertex d → ι → Ω → ℝ) (ω : Ω) :
    Summable (fun v : TreeVertex d =>
      (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    summable_norm_sq_of_radial_bound d hsub
      (fun v => coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω)
      (fun v => norm_tree_coefficient_le hθ0 hθ s X v ω)

theorem summable_regularPathWeight {d : ℕ} {theta : ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (regularPathWeight d theta) := by
  have hs := summable_regularPathWeight_mul_length_sq hsub
  apply Summable.of_nonneg_of_le (regularPathWeight_nonneg d theta) _ hs
  intro n
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hr2 (regularPathWeight_nonneg d theta n)

theorem summable_regularPathWeight_sqrt_length_sq
    {d : ℕ} {theta A : ℝ} (hA : 0 ≤ A)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (fun n => regularPathWeight d theta n *
      Real.sqrt (A * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs := (summable_regularPathWeight_mul_length_sq hsub).mul_left (Real.sqrt A)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg
    (regularPathWeight_nonneg d theta n) (Real.sqrt_nonneg _)) _ hs
  intro n
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [Real.sqrt_mul hA, Real.sqrt_sq (Nat.cast_nonneg _)]
  have hr2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  calc
    regularPathWeight d theta n * (Real.sqrt A * ((n + 1 : ℕ) : ℝ)) ≤
        regularPathWeight d theta n * (Real.sqrt A * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hr2 (Real.sqrt_nonneg A))
        (regularPathWeight_nonneg d theta n)
    _ = _ := by ring

end Deterministic

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_tree_density_le_subcritical
    {d : ℕ} {ι : Type*} (s : TreeVertex d → Finset ι)
    (hcard : ∀ v, (s v).card = v.1.length)
    {theta C : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) (hC : 0 ≤ C)
    {X Y : TreeVertex d → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ v i, i ∈ s v → Measurable (X v i))
    (hY : ∀ v i, i ∈ s v → Measurable (Y v i))
    (hInt : ∀ v i, i ∈ s v → Integrable (fun ω => (X v i ω - Y v i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    (hlog : ∀ v i, i ∈ s v →
      (∫ ω, (Real.log (responseAttenuation theta (X v i ω)) -
        Real.log (responseAttenuation theta (Y v i ω))) ^ 2 ∂μ) ≤
        C * (∫ ω, (H ω - H' ω) ^ 2 ∂μ)) :
    let c := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X
    let c' := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y
    Integrable (DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      subcriticalPathConstant d theta (2 * C) * (∫ ω, (H ω - H' ω) ^ 2 ∂μ) := by
  dsimp only
  let V := ∫ ω, (H ω - H' ω) ^ 2 ∂μ
  let Q := fun n : ℕ => (2 * C) * ((n + 1 : ℕ) : ℝ) ^ 2 * V
  let L := fun _ : ℕ => V
  have hV : 0 ≤ V := integral_nonneg (fun ω => sq_nonneg _)
  have hQ0 (n : ℕ) : 0 ≤ Q n := by dsimp [Q] <;> positivity
  have hL0 (n : ℕ) : 0 ≤ L n := hV
  have hQ (n : ℕ) (v : TreeVertex d) (hv : v.1.length = n + 1) :
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤ Q n := by
    have h := integral_weighted_path_log_sq_le (s v) hθ (hX v) (hY v) (hInt v) (hlog v)
    rw [hcard v, hv] at h
    change _ ≤ _ at h
    calc
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤
          2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (C * V) := h
      _ = Q n := by dsimp [Q] <;> ring
  have hL (n : ℕ) (v : TreeVertex d) (_hv : v.1.length = n + 1) :
      pathLinearEnergy μ theta (s v) (X v) (fun ω => H ω - H' ω) ≤ L n :=
    (integral_mul_prod_responseAttenuation_sq_le (s v) hθ (hX v) hU).2
  have hQs : Summable (fun n => regularPathWeight d theta n * Q n) := by
    convert! (summable_regularPathWeight_mul_length_sq hsub).mul_left (2 * C * V) using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    dsimp only [Q]
    ring
  have hLs : Summable (fun n => regularPathWeight d theta n * L n) :=
    (summable_regularPathWeight hsub).mul_right V
  have hRs : Summable (fun n => regularPathWeight d theta n * Real.sqrt (Q n)) := by
    convert! summable_regularPathWeight_sqrt_length_sq (A := 2 * C * V)
      (by positivity) hsub using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    congr 2
    dsimp only [Q]
    ring
  have hrows : ∀ᵐ ω ∂μ,
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) ∧
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y v ω) ^ 2) := by
    filter_upwards [] with ω
    exact ⟨summable_tree_coefficient_sq hθ0 hθ hsub s X ω,
      summable_tree_coefficient_sq hθ0 hθ hsub s Y ω⟩
  have hb := integral_tree_density_le_shell_energies s hcard hθ hX hY hInt hH hH' hU
    hQ0 hL0 hQ hL hQs hLs hRs hrows
  refine ⟨hb.1, ?_⟩
  exact (subcritical_noise_drift_bound hsub (by positivity : 0 ≤ 2 * C) hV
    hQ0 hL0 (fun n => le_rfl) (fun n => le_rfl) hb.2).2

end Probability

end Problem367.ResponseRows

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ChainMarginals
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*} [Fintype A]

theorem sum_advance (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ a, ∑ b, K 0 a b = 1) (hw : ∑ a, w a = 1) :
    ∑ b, advance K w b = 1 := by
  unfold advance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hw

theorem sum_jointWeight_tail (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    (∑ x : Fin (n + 2) → A, jointWeight K w (n + 1) x * F (Fin.tail x)) =
      ∑ x : Fin (n + 1) → A,
        jointWeight (fun i => K (i + 1)) (advance K w) n x * F x := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, weight, Fin.tail_cons]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [jointWeight, advance, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [weight_eq_prod]
  simp only [Fin.cons_self_tail, Fin.tail]
  ring

theorem coordinateMean_succ (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (n : ℕ) (i : Fin (n + 1)) :
    coordinateMean K w f (n + 1) i.succ =
      coordinateMean (fun j => K (j + 1)) (advance K w) f n i := by
  exact sum_jointWeight_tail K w n (fun x => f (x i))

theorem coordinateMean_zero (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) :
    coordinateMean K w f n 0 = ∑ a, w a * f a := by
  unfold coordinateMean
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x, w a * weight K n a x * f a) =
        w a * f a * ∑ x, weight K n a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [sum_weight K hK, mul_one]

theorem coordinateMean_affine (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (p q : ℕ → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a)
    (n : ℕ) (i : Fin n) :
    coordinateMean K w f n i.succ =
      p i + q i * coordinateMean K w f n i.castSucc := by
  induction n generalizing K w p q with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [coordinateMean_succ, coordinateMean_zero _ _ _ (fun i => hK (i + 1)),
        show (Fin.castSucc (0 : Fin (n + 1))) = 0 by rfl,
        coordinateMean_zero K w f hK]
      simp only [Fin.val_zero]
      unfold advance
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc
        (∑ a, ∑ b, w a * K 0 a b * f b) =
            ∑ a, w a * (p 0 + q 0 * f a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← hmean 0 a, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    · rw [coordinateMean_succ, show j.succ.castSucc = j.castSucc.succ by rfl,
        coordinateMean_succ]
      exact ih (fun k => K (k + 1)) (advance K w)
        (fun k => p (k + 1)) (fun k => q (k + 1))
        (sum_advance K w (hK 0) hw) (fun k => hK (k + 1))
        (fun k => hmean (k + 1)) j

end Problem367.InhomogeneousChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CoupledSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem cavityLogVarianceCoefficient_nonneg (theta : ℝ) :
    0 ≤ cavityLogVarianceCoefficient theta := by
  unfold cavityLogVarianceCoefficient
  positivity

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Leaf
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem energy_update_eq_erase_add
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    energy beta h D (Function.update eta v s) = energy beta h (D.erase v) eta +
      (h v + beta * spinSign (eta p)) * spinSign s := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  have hfield : (∑ x ∈ D, h x * spinSign (Function.update eta v s x)) =
      (∑ x ∈ D.erase v, h x * spinSign (eta x)) + h v * spinSign s := by
    rw [← Finset.sum_erase_add D _ hv]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  have hedge : (∑ e ∈ inducedEdges (D.erase v),
      spinSign (Function.update eta v s e.1) * spinSign (Function.update eta v s e.2)) =
      ∑ e ∈ inducedEdges (D.erase v), spinSign (eta e.1) * spinSign (eta e.2) := by
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hm
    rw [Function.update_of_ne (Finset.mem_erase.mp hu).1,
      Function.update_of_ne (Finset.mem_erase.mp hw).1]
  unfold energy
  rw [hfield, hedges, Finset.sum_insert hnot, hedge]
  simp only [Function.update_of_ne hpne, Function.update_self]
  ring

theorem sum_weight_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      2 * Real.cosh (h v + beta * spinSign (eta p)) * weight beta h (D.erase v) eta := by
  simp only [weight, energy_update_eq_erase_add beta h hv hpne hedges, Real.exp_add]
  rw [← Finset.mul_sum, sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one]
  rw [Real.cosh_eq]
  ring

theorem sum_weight_eq_erase_sum
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        2 * Real.cosh (h v + beta * spinSign (extendFiniteSpin (D.erase v) eta p)) *
          weight beta h (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        weight beta h D (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => weight beta h D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact sum_weight_update_of_edges beta h hv hpne hedges _

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_LeafMessage
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem eliminationConstant_pos (beta z : ℝ) : 0 < eliminationConstant beta z := by
  unfold eliminationConstant
  positivity

theorem cosh_eq_eliminationConstant_mul_message (beta z : ℝ) (s : IsingSpin) :
    2 * Real.cosh (z + beta * spinSign s) =
      eliminationConstant beta z * Real.exp
        (cavityMessage (Real.tanh beta) z * spinSign s) := by
  unfold eliminationConstant
  rw [mul_assoc, ← Real.exp_add, cavityMessage_eq_log_cosh_sub]
  cases s
  · simp only [spinSign_neg, mul_neg_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        -((Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2) =
        Real.log (Real.cosh (z - beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]
    congr 2
  · simp only [spinSign_pos, mul_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 =
        Real.log (Real.cosh (z + beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]

theorem energy_update_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {p : TreeVertex d} (hp : p ∈ D)
    (z : ℝ) (eta : TreeVertex d → IsingSpin) :
    energy beta (Function.update h p (h p + z)) D eta =
      energy beta h D eta + z * spinSign (eta p) := by
  classical
  have hsum : (∑ x ∈ D.erase p, Function.update h p (h p + z) x * spinSign (eta x)) =
      ∑ x ∈ D.erase p, h x * spinSign (eta x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  unfold energy
  rw [← Finset.sum_erase_add D
    (fun x => Function.update h p (h p + z) x * spinSign (eta x)) hp,
    ← Finset.sum_erase_add D (fun x => h x * spinSign (eta x)) hp, hsum]
  simp only [Function.update_self]
  ring

theorem sum_weight_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      eliminationConstant beta (h v) *
        weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) eta := by
  rw [sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges,
    cosh_eq_eliminationConstant_mul_message]
  simp only [weight, energy_update_field beta h (D.erase v) hp, Real.exp_add]
  ring

theorem partition_eq_cavity_partition
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      eliminationConstant beta (h v) *
        ∑ eta : D.erase v → IsingSpin,
          weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  rw [sum_weight_eq_erase_sum beta h hv (Finset.mem_erase.mp hp).1 hedges, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [← sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges]
  exact sum_weight_update_eq_cavity beta h hv hp hedges _

theorem sum_mass_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, mass beta h D (Function.update eta v s)) =
      mass beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) eta := by
  classical
  simp only [mass, ← Finset.sum_div]
  rw [sum_weight_update_eq_cavity beta h hv hp hedges]
  unfold partition
  rw [partition_eq_cavity_partition beta h hv hp hedges]
  exact mul_div_mul_left _ _ (ne_of_gt (eliminationConstant_pos beta (h v)))

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LeafMarginal
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_expectation_eq_sum_mass
    {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (f : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) f =
      ∑ eta : D → IsingSpin, GibbsLeaf.mass beta h D (extendFiniteSpin D eta) * f eta := by
  classical
  simp only [LeafGibbs.expectation, GibbsLeaf.mass, GibbsLeaf.weight,
    GibbsLeaf.partition, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro eta heta
  ring

theorem tree_gibbs_expectation_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f := by
  classical
  rw [tree_gibbs_expectation_eq_sum_mass, tree_gibbs_expectation_eq_sum_mass]
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        GibbsLeaf.mass beta h D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) * f z.1 := by
      rw [← (finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta : D → IsingSpin => GibbsLeaf.mass beta h D (extendFiniteSpin D eta) *
          f ((finiteSpinEraseEquiv hv eta).1))]
      simp only [Equiv.apply_symm_apply]
    _ = ∑ eta : D.erase v → IsingSpin,
        (∑ s : IsingSpin, GibbsLeaf.mass beta h D
          (Function.update (extendFiniteSpin (D.erase v) eta) v s)) * f eta := by
      rw [Fintype.sum_prod_type]
      simp only [extendFiniteSpin_eraseEquiv_symm, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [GibbsLeaf.sum_mass_update_eq_cavity beta h hv hp hedges]

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

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

theorem ConnectedFinset.prefix_mem_of_min_length_le {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {u v : TreeVertex d} (hv : v ∈ D) (huv : u.1 <+: v.1)
    (hru : r.1.length ≤ u.1.length) : u ∈ D := by
  have aux : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ D →
      u.1 <+: v.1 → u ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv huv
      by_cases huv_eq : u = v
      · exact huv_eq.symm ▸ hv
      · have hvne : v ≠ r := by
          intro heq
          subst v
          exact huv_eq (Subtype.ext (huv.eq_of_length_le hru))
        have hp := hD.parent_mem_of_ne_min hr hmin hv hvne
        have hvnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hvne
        have hpos : 0 < v.1.length := List.length_pos_iff.mpr hvnil
        have hplen : (parentVertex v).1.length < n := by
          rw [parentVertex_length]
          omega
        have hup : u.1 <+: (parentVertex v).1 := by
          apply List.prefix_of_prefix_length_le huv (List.dropLast_prefix v.1)
          have hle := huv.length_le
          have hneq : u.1.length ≠ v.1.length := by
            intro heq
            exact huv_eq (Subtype.ext (huv.eq_of_length heq))
          change u.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        exact ih _ hplen _ rfl hp hup
  exact aux _ v rfl hv huv

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedProjectivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.exists_prunable_vertex_of_shared_min
    {d : ℕ} {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hE : ConnectedFinset E) (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (hne : D ≠ E) :
    ∃ v p : TreeVertex d, v ∈ E ∧ v ∉ D ∧ p ∈ E ∧ p ≠ v ∧
      ConnectedFinset (E.erase v) ∧ D ⊆ E.erase v ∧
      inducedEdges E = insert (p, v) (inducedEdges (E.erase v)) := by
  classical
  have hdiff : (E \ D).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hED
    exact hne (Finset.Subset.antisymm hDE hED))
  obtain ⟨v, hvdiff, hmax⟩ := Finset.exists_max_image (E \ D) (fun x => x.1.length) hdiff
  obtain ⟨hvE, hvD⟩ := Finset.mem_sdiff.mp hvdiff
  have hvr : v ≠ r := by
    intro h
    exact hvD (h ▸ hr)
  have hpE : parentVertex v ∈ E :=
    hE.parent_mem_of_ne_min (hDE hr) hmin hvE hvr
  have hvnil : v.1 ≠ [] := ConnectedFinset.ne_nil_of_ne_min hmin hvE hvr
  have hpv : treeAdj (parentVertex v) v := treeAdj_parentVertex hvnil
  have hplen : (parentVertex v).1.length < v.1.length := by
    rw [parentVertex_length]
    have : 0 < v.1.length := List.length_pos_iff.mpr hvnil
    omega
  have hleaf : ∀ x ∈ E, treeAdj v x → x = parentVertex v := by
    intro x hx hadj
    rcases treeAdj_length hadj with hlen | hlen
    · have hxD : x ∈ D := by
        by_contra hxD
        have hbound := hmax x (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
        omega
      have hxr : x ≠ r := by
        intro h
        subst x
        have := hmin v hvE
        omega
      have hpD := hD.parent_mem_of_ne_min hr (fun y hy => hmin y (hDE hy)) hxD hxr
      have hparent : parentVertex x = v := treeAdj_parent_of_length_lt hadj (by omega)
      exact False.elim (hvD (hparent ▸ hpD))
    · exact (treeAdj_parent_of_length_lt (hadj.elim Or.inr Or.inl) (by omega)).symm
  have hDEerase : D ⊆ E.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; exact hvD (h ▸ hx), hDE hx⟩
  have hconn : ConnectedFinset (E.erase v) :=
    connectedFinset_erase_of_leaf hE hvE ⟨r, hDEerase hr⟩
      (fun x hx y hy hvx hvy => (hleaf x hx hvx).trans (hleaf y hy hvy).symm)
  refine ⟨v, parentVertex v, hvE, hvD, hpE, ?_, hconn, hDEerase, ?_⟩
  · intro h
    have := congrArg (fun x : TreeVertex d => x.1.length) h
    omega
  · exact inducedEdges_eq_insert_erase_of_unique_lower_neighbor hvE hpE hpv hplen hleaf

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsMarginal
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_marginal_of_shared_min
    {d : ℕ} (beta : ℝ) {D E : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hE : ConnectedFinset E) (hDE : D ⊆ E)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (h : TreeVertex d → ℝ) :
    ∃ h' : TreeVertex d → ℝ, ∀ f : (D → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDE eta)) =
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' D (extendFiniteSpin D eta)) f := by
  classical
  revert hE hDE hmin h
  refine Finset.strongInductionOn E ?_
  intro E ih hE hDE hmin h
  by_cases heq : D = E
  · subst E
    exact ⟨h, fun _ => rfl⟩
  · obtain ⟨v, p, hvE, _, hpE, hpne, hEr, hDEr, hedges⟩ :=
      hD.exists_prunable_vertex_of_shared_min hE hDE hr hmin heq
    have hpEr : p ∈ E.erase v := Finset.mem_erase.mpr ⟨hpne, hpE⟩
    have hErE : E.erase v ⊆ E := Finset.erase_subset _ _
    obtain ⟨h', hh'⟩ := ih (E.erase v) (Finset.erase_ssubset hvE) hEr hDEr
      (fun x hx => hmin x (hErE hx))
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
    refine ⟨h', fun f => ?_⟩
    calc
      _ = LeafGibbs.expectation
          (fun eta => GibbsLeaf.energy beta
            (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (E.erase v) (extendFiniteSpin (E.erase v) eta))
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta)) := by
        exact tree_gibbs_expectation_erase beta h hvE hpEr hedges
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta))
      _ = _ := hh' f

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FinitePathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePathGibbs

theorem rawKernel_pos (beta : ℝ) (h : ℕ → ℝ) (i : ℕ) (a b : IsingSpin) :
    0 < rawKernel beta h i a b := Real.exp_pos _

theorem tailPartition_pos (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    0 < tailPartition beta h n a := by
  let : Nonempty (Fin n → IsingSpin) := ⟨fun _ => .pos⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  rw [InhomogeneousChain.weight_eq_prod]
  exact Finset.prod_pos fun i _ => rawKernel_pos beta h i _ _

theorem tailPartition_succ (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    tailPartition beta h (n + 1) a =
      ∑ b, rawKernel beta h 0 a b *
        tailPartition beta (fun i => h (i + 1)) n b := by
  unfold tailPartition
  rw [FiniteChain.sum_cons]
  simp only [InhomogeneousChain.weight_cons, ← Finset.mul_sum]
  rfl

theorem normalize_binary (w : IsingSpin → ℝ) (hw : ∀ a, 0 < w a) (b : IsingSpin) :
    w b / (∑ a, w a) =
      (1 + spinSign b * Real.tanh
        ((Real.log (w .pos) - Real.log (w .neg)) / 2)) / 2 := by
  rw [← binary_mean_eq_tanh_half_log (hw .pos) (hw .neg), sum_isingSpin]
  have hsum : w .pos + w .neg ≠ 0 := (add_pos (hw .pos) (hw .neg)).ne'
  have hsum' : w .neg + w .pos ≠ 0 := (add_pos (hw .neg) (hw .pos)).ne'
  cases b <;> simp only [spinSign_neg, spinSign_pos] <;>
    field_simp [hsum, hsum'] <;> ring

theorem normalized_head (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a b : IsingSpin) :
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b /
      tailPartition beta h (n + 1) a =
    PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a b := by
  let w : IsingSpin → ℝ := fun b =>
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b
  have hw : ∀ b, 0 < w b := fun b =>
    mul_pos (rawKernel_pos beta h 0 a b)
      (tailPartition_pos beta (fun i => h (i + 1)) n b)
  rw [tailPartition_succ]
  change w b / (∑ s, w s) = _
  rw [normalize_binary w hw]
  have hlog : (Real.log (w .pos) - Real.log (w .neg)) / 2 =
      backwardField beta h (n + 1) 0 + beta * spinSign a := by
    dsimp [w, rawKernel, backwardField]
    rw [Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_exp, Real.log_exp]
    ring
  rw [hlog]
  rfl

theorem normalized_path (beta : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (a : IsingSpin) (x : Fin n → IsingSpin) :
    InhomogeneousChain.weight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n a x =
    InhomogeneousChain.weight (rawKernel beta h) n a x / tailPartition beta h n a := by
  induction n generalizing h a with
  | zero => simp
  | succ n ih =>
    rw [InhomogeneousChain.weight, InhomogeneousChain.weight]
    change PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a (x 0) *
      InhomogeneousChain.weight
        (fun i => PosteriorChain.transition beta
          (backwardField beta (fun j => h (j + 1)) n i)) n (x 0) (Fin.tail x) = _
    rw [ih, ← normalized_head]
    have ht := (tailPartition_pos beta (fun i => h (i + 1)) n (x 0)).ne'
    have ht' := (tailPartition_pos beta h (n + 1) a).ne'
    change (rawKernel beta h 0 a (x 0) *
        tailPartition beta (fun i => h (i + 1)) n (x 0) /
        tailPartition beta h (n + 1) a) *
      (InhomogeneousChain.weight (rawKernel beta (fun i => h (i + 1))) n
        (x 0) (Fin.tail x) / tailPartition beta (fun i => h (i + 1)) n (x 0)) = _
    field_simp [ht, ht']
    rfl

theorem partition_pos (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    0 < partition beta root h n := by
  rw [partition, sum_isingSpin]
  exact add_pos (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))
    (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))

@[simp] theorem sum_rootLaw (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ a, rootLaw beta root h n a = 1 := by
  simp only [rootLaw, ← Finset.sum_div]
  exact div_self (partition_pos beta root h n).ne'

theorem mass_eq_jointWeight (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x =
    InhomogeneousChain.jointWeight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i))
      (rootLaw beta root h n) n x := by
  obtain ⟨a, x, rfl⟩ := Fin.exists_cons x
  rw [mass, InhomogeneousChain.jointWeight_cons,
    InhomogeneousChain.jointWeight_cons, normalized_path]
  unfold rootLaw
  field_simp [(partition_pos beta root h n).ne', (tailPartition_pos beta h n a).ne']

theorem mass_eq_exp_energy (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x = Real.exp (energy beta root h n x) /
      partition beta root h n := by
  simp only [mass, InhomogeneousChain.jointWeight, rawKernel,
    energy, Real.exp_add, Real.exp_sum]

@[simp] theorem sum_mass (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ x, mass beta root h n x = 1 := by
  simp_rw [mass_eq_jointWeight]
  exact InhomogeneousChain.sum_jointWeight _ _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i))
    (sum_rootLaw beta root h n) n

theorem partition_eq_sum_exp (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    partition beta root h n =
      ∑ x : Fin (n + 1) → IsingSpin, Real.exp (energy beta root h n x) := by
  have hm := sum_mass beta root h n
  simp_rw [mass_eq_exp_energy] at hm
  rw [← Finset.sum_div, div_eq_one_iff_eq (partition_pos beta root h n).ne'] at hm
  exact hm.symm

theorem mean_endpoints (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f g : IsingSpin → ℝ) :
    mean beta root h n (fun x => f (x 0) * g (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a * f a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n g a := by
  unfold mean
  simp_rw [mass_eq_jointWeight, ← mul_assoc]
  exact InhomogeneousChain.sum_jointWeight_endpoints _ _ _ _ _

theorem mean_first (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x 0)) =
      ∑ a, rootLaw beta root h n a * spinSign a := by
  have hm := mean_endpoints beta root h n spinSign (fun _ => 1)
  simp only [mul_one, InhomogeneousChain.expectation] at hm
  simp only [InhomogeneousChain.sum_weight _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i)), mul_one] at hm
  exact hm

theorem mean_last (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n spinSign a := by
  simpa only [one_mul, mul_one] using
    mean_endpoints beta root h n (fun _ => 1) spinSign

theorem endpointCovariance_eq (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    endpointCovariance beta root h n =
      (1 - mean beta root h n (fun x => spinSign (x 0)) ^ 2) * Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (backwardField beta h n i)) := by
  unfold endpointCovariance
  rw [mean_endpoints, mean_first, mean_last]
  exact PosteriorChain.covariance_eq_response_product beta (backwardField beta h n)
    (rootLaw beta root h n) (sum_rootLaw beta root h n) n

end Problem367.FinitePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PathPosteriorResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.PathPosterior

theorem energy_eq_fieldEnergy (beta : ℝ) (n : ℕ)
    (y : Fin (n + 1) → ℝ) (s : Fin (n + 1) → IsingSpin) :
    FinitePathGibbs.energy beta (y 0) (childFields y) n s =
      FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s := by
  unfold FinitePathGibbs.energy FinitePosterior.fieldEnergy interaction spin
  rw [Fin.sum_univ_succ]
  simp only [childFields_fin, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

theorem mean_eq_fieldMean (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    FinitePathGibbs.mean beta (y 0) (childFields y) n f =
      FinitePosterior.fieldMean (interaction beta n) (spin n) f y := by
  unfold FinitePathGibbs.mean FinitePosterior.fieldMean
  simp_rw [FinitePathGibbs.mass_eq_exp_energy]
  rw [FinitePathGibbs.partition_eq_sum_exp]
  simp_rw [energy_eq_fieldEnergy]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun a => a / ∑ s, Real.exp
    (FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s))
  apply Finset.sum_congr rfl
  intro s _
  ring

end Problem367.PathPosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathGibbs

theorem extend_assignment_path {d : ℕ} (v : TreeVertex d)
    (eta : ConnectedHull.vertices v → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.path v i) =
      assignmentEquiv v eta i := by
  exact extendFiniteSpin_apply (ConnectedHull.vertices v) eta (vertexEquiv v i)

theorem extend_assignment_symm_path {d : ℕ} (v : TreeVertex d)
    (s : Fin (v.1.length + 1) → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) ((assignmentEquiv v).symm s)
      (ConnectedHull.path v i) = s i := by
  rw [extend_assignment_path, Equiv.apply_symm_apply]

theorem energy_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta h (ConnectedHull.vertices v) eta =
      FinitePosterior.fieldEnergy (PathPosterior.interaction beta v.1.length)
        (PathPosterior.spin v.1.length) (fun i => h (ConnectedHull.path v i))
        (fun i => eta (ConnectedHull.path v i)) := by
  classical
  unfold GibbsLeaf.energy
  rw [ConnectedHull.inducedEdges_vertices, ConnectedHull.vertices_eq_image_path]
  rw [Finset.sum_image]
  · rw [Finset.sum_image]
    · unfold FinitePosterior.fieldEnergy PathPosterior.interaction PathPosterior.spin
      simp only [ConnectedHull.pathEdge]
      ring
    · exact fun _ _ _ _ he => ConnectedHull.pathEdge_injective v he
  · exact fun _ _ _ _ he => ConnectedHull.path_injective v he

theorem expectation_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (f : (Fin (v.1.length + 1) → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta))
      (fun eta => f (assignmentEquiv v eta)) =
    FinitePathGibbs.mean beta (h (ConnectedHull.path v 0))
      (PathPosterior.childFields (fun i => h (ConnectedHull.path v i))) v.1.length f := by
  rw [PathPosterior.mean_eq_fieldMean beta v.1.length
    (fun i => h (ConnectedHull.path v i)) f]
  unfold LeafGibbs.expectation FinitePosterior.fieldMean
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => f (assignmentEquiv v eta) *
      Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
      (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  simp only [Equiv.apply_symm_apply, energy_eq_path, extend_assignment_symm_path]

end Problem367.TreePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathResponse

theorem path_subset {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hr : ConnectedHull.root d ∈ D)
    {v : TreeVertex d} (hv : v ∈ D) : ConnectedHull.vertices v ⊆ D := by
  intro u hu
  obtain ⟨n, hn, rfl⟩ := ConnectedHull.mem_vertices.mp hu
  apply hD.prefix_mem_of_min_length_le hr (fun x _ => Nat.zero_le _) hv
  · exact List.take_prefix n v.1
  · exact Nat.zero_le _

theorem exists_path_fields {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ y : Fin (v.1.length + 1) → ℝ, ∀ f : (Fin (v.1.length + 1) → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f (fun i => extendFiniteSpin D eta (ConnectedHull.path v i))) =
      FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length f := by
  classical
  have hsub := path_subset hD hr hv
  have hrpath : ConnectedHull.root d ∈ ConnectedHull.vertices v := by
    simpa using ConnectedHull.prefix_mem_vertices v (Nat.zero_le v.1.length)
  obtain ⟨h', hh'⟩ := tree_gibbs_marginal_of_shared_min beta
    (ConnectedHull.connected_vertices v) hD hsub hrpath
    (fun x _ => Nat.zero_le _) h
  refine ⟨fun i => h' (ConnectedHull.path v i), fun f => ?_⟩
  have hrest (eta : D → IsingSpin) :
      TreePathGibbs.assignmentEquiv v (Finset.restrict₂ (π := fun _ => IsingSpin) hsub eta) =
        (fun i => extendFiniteSpin D eta (ConnectedHull.path v i)) := by
    funext i
    exact (extendFiniteSpin_apply D eta
      ⟨ConnectedHull.path v i, hsub (TreePathGibbs.vertexEquiv v i).property⟩).symm
  calc
    _ = LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' (ConnectedHull.vertices v)
          (extendFiniteSpin (ConnectedHull.vertices v) eta))
        (fun eta => f (TreePathGibbs.assignmentEquiv v eta)) := by
      simpa only [hrest] using hh' (fun eta => f (TreePathGibbs.assignmentEquiv v eta))
    _ = _ := TreePathGibbs.expectation_eq_path v beta h' f

theorem mean_mem_Ioo {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    mean beta h D v ∈ Set.Ioo (-1 : ℝ) 1 := by
  classical
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  rw [mean, LeafGibbs.expectation_eq_mean_zero]
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    cases extendFiniteSpin D eta v <;> simp [spinSign]
  · refine ⟨fun _ => .neg, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .neg) ⟨v, hv⟩]
    rfl
  · refine ⟨fun _ => .pos, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .pos) ⟨v, hv⟩]
    rfl

theorem variance_pos {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    0 < 1 - mean beta h D v ^ 2 := by
  have hm := mean_mem_Ioo beta h hv
  have hp : 0 < (1 - mean beta h D v) * (1 + mean beta h D v) :=
    mul_pos (by linarith [hm.2]) (by linarith [hm.1])
  nlinarith

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePosterior
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

open PlantedSymmetry

theorem GibbsLeaf.energy_eq_fieldEnergy {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta h D (extendFiniteSpin D eta) =
      FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) (D.restrict h) eta := by
  classical
  have hsum : (∑ x ∈ D, h x * spinSign (extendFiniteSpin D eta x)) =
      ∑ x : D, h x * spinSign (eta x) := by
    rw [← Finset.sum_coe_sort D (fun x => h x * spinSign (extendFiniteSpin D eta x))]
    apply Finset.sum_congr rfl
    intro x _
    rw [extendFiniteSpin_apply D eta x]
  unfold GibbsLeaf.energy FinitePosterior.fieldEnergy finiteIsingEnergy
  rw [hsum]
  exact add_comm _ _

theorem GibbsLeaf.expectation_eq_fieldMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ)
    (q : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) q =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (D.restrict h) := by
  simp only [LeafGibbs.expectation, FinitePosterior.fieldMean,
    GibbsLeaf.energy_eq_fieldEnergy]

theorem HasFreeIsingLaw.finiteObservation_condExp_treeMean {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => spinSign (p.1 v.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => TreePathResponse.mean beta (PlantedSymmetry.observation t p) D v.1 := by
  have heq := hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))
  filter_upwards [heq] with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  simp only [TreePathResponse.mean, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

theorem HasFreeIsingLaw.finiteObservation_normalizedResponse {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let m := MeasurableSpace.comap (finiteObservation D t) inferInstance
    (fun p => ((P[fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) | m]) p -
      (P[fun q => spinSign (q.1 u.1) | m]) p *
      (P[fun q => spinSign (q.1 v.1) | m]) p) /
      (1 - (P[fun q => spinSign (q.1 u.1) | m]) p ^ 2)) =ᵐ[P]
      fun p => GaussianTreeResponse.response beta D u.1 v.1
        (PlantedSymmetry.observation t p) := by
  dsimp only
  have hpair := hμ.finiteObservation_condExp D hD t
    (fun eta => spinSign (eta u) * spinSign (eta v))
  filter_upwards [hpair, hμ.finiteObservation_condExp_treeMean D hD t u,
    hμ.finiteObservation_condExp_treeMean D hD t v] with p hp hu hv
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp, hu, hv]
  unfold GaussianTreeResponse.response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ u, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean, TreePathResponse.mean]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.sum_mass _root_.OAI.Problem367.FinitePathGibbs.sum_rootLaw _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
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

theorem ae_initial_observation_eq (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      (fun v => q.2.1 v 0) = (fun v => q.2.2 v 0) := by
  filter_upwards [ae_all_innovation_identities hjoint] with q hq
  funext v
  have hl := (hq v 0).1
  have hr := (hq v 0).2
  simp only [nnrealTimePrimitive, NNReal.coe_zero,
    intervalIntegral.integral_same, add_zero] at hl hr
  exact hl.trans hr.symm

theorem ae_initial_fieldDifference_zero (hjoint : rho ⊗ₘ eta = graphLaw beta μ)
    (v : TreeVertex d) :
    fieldDifference beta v 0 =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] 0 := by
  filter_upwards [ae_initial_observation_eq hjoint] with q hq
  simp only [fieldDifference, IsingObservationInnovation.posterior, Pi.zero_apply]
  rw [hq, sub_self]

theorem initial_fieldDifference_secondMoment_zero
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v 0 q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) = 0 := by
  have hzero := ae_initial_fieldDifference_zero hjoint v
  have heq : (fun q => (fieldDifference beta v 0 q) ^ 2) =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      (fun _ => (0 : ℝ)) := hzero.mono (fun q hq => by simp [hq])
  rw [integral_congr_ae heq, integral_zero]

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.sum_mass _root_.OAI.Problem367.FinitePathGibbs.sum_rootLaw _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem observableDifference_ae {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    (observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      (fun q => f q.2.1 - f q.2.2) := by
  obtain ⟨hp, hq⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have h := CopyDifference.operator_ae hp hq (hf.toLp f)
  filter_upwards [h, hp.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hq.quasiMeasurePreserving.ae hf.coeFn_toLp] with q hq' hl hr
  exact hq'.trans (congrArg₂ (fun a b : ℝ => a - b) hl hr)

theorem norm_observableDifference_sq {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    ‖observableDifference (beta := beta) hf‖ ^ 2 =
      ∫ q, (f q.2.1 - f q.2.2) ^ 2 ∂copies beta μ := by
  change ‖(observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [observableDifference_ae (beta := beta) hf] with q hq
  simp [hq, pow_two]

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_NormalizedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gaussian

open PlantedSymmetry

theorem HasFreeIsingLaw.gaussian_posteriorResponse_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) atTop
        (𝓝 (gaussianPosteriorResponse μ t v w p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hi := (hμ.gaussian_posterior_field_bound hbeta t v).mono (fun _ h => h.1)
  have hi' : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) | ⨆ n, finiteObservationFiltration D hD t n] p ∈
        Set.Ioo (-1 : ℝ) 1 := by
    rw [finiteObservationFiltration_iSup D hD hex t]
    exact hi
  have h := tendsto_ae_posteriorResponse
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) hi'
  rw [finiteObservationFiltration_iSup D hD hex t] at h
  exact h

end Gaussian

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.FinitePathGibbs

theorem mean_eq_posterior_mean (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    mean beta root h n f =
      FinitePosterior.mean (energy beta root h n) (fun _ => 0) f 0 := by
  unfold mean FinitePosterior.mean FinitePosterior.partition
  simp only [FinitePosterior.weight, zero_mul, add_zero]
  simp_rw [mass_eq_exp_energy, partition_eq_sum_exp, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coordinate_mean_mem_Ioo (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    mean beta root h n (fun x => spinSign (x i)) ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [mean_eq_posterior_mean]
  let : Nonempty (Fin (n + 1) → IsingSpin) := ⟨fun _ => .pos⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro x
    cases x i <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

theorem coordinate_mean_affine (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin n) :
    mean beta root h n (fun x => spinSign (x i.succ)) =
      PosteriorChain.intercept beta (backwardField beta h n i) +
        PosteriorChain.slope beta (backwardField beta h n i) *
          mean beta root h n (fun x => spinSign (x i.castSucc)) := by
  have hh := InhomogeneousChain.coordinateMean_affine
    (fun j => PosteriorChain.transition beta (backwardField beta h n j))
    (rootLaw beta root h n) spinSign
    (fun j => PosteriorChain.intercept beta (backwardField beta h n j))
    (fun j => PosteriorChain.slope beta (backwardField beta h n j))
    (sum_rootLaw beta root h n)
    (fun j => PosteriorChain.transition_sum beta (backwardField beta h n j))
    (fun j => PosteriorChain.transition_spinMean_affine beta (backwardField beta h n j)) n i
  simpa only [InhomogeneousChain.coordinateMean, ← mass_eq_jointWeight, mean] using hh

theorem backwardField_eq_cavityFromSites {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    backwardField beta h n i =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))),
          Real.artanh (mean beta root h n (fun x => spinSign (x i.succ))))).2 := by
  have hh := PosteriorChain.cavityFromSites_affine_mean_snd hbeta
    (backwardField beta h n i)
    (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))))
  rw [Real.tanh_artanh (coordinate_mean_mem_Ioo beta root h n i.castSucc),
    ← coordinate_mean_affine beta root h n i] at hh
  exact hh.symm

end Problem367.FinitePathGibbs

namespace Problem367.TreePathResponse

theorem root_response_eq_canonical_product {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    response beta h D (ConnectedHull.root d) v =
      Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
  obtain ⟨y, hy⟩ := exists_path_fields beta h hD hr hv
  have hmean (i : Fin (v.1.length + 1)) :
      mean beta h D (ConnectedHull.path v i) =
        FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length
          (fun x => spinSign (x i)) :=
    hy (fun x => spinSign (x i))
  have hback (i : ℕ) (hi : i < v.1.length) :
      FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i =
        orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1)) := by
    have hh := FinitePathGibbs.backwardField_eq_cavityFromSites hbeta
      (y 0) (PathPosterior.childFields y) v.1.length ⟨i, hi⟩
    rw [← hmean (Fin.castSucc ⟨i, hi⟩), ← hmean (Fin.succ ⟨i, hi⟩)] at hh
    exact hh
  have hprod :
      (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i)) =
      ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1))) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hback i (Finset.mem_range.mp hi)]
  have hcov : covariance beta h D (ConnectedHull.root d) v =
      (1 - mean beta h D (ConnectedHull.root d) ^ 2) * Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
    rw [← hprod]
    have hm := hy (fun x => spinSign (x 0))
    have hn := hy (fun x => spinSign (x (Fin.last v.1.length)))
    have hp := hy (fun x => spinSign (x 0) * spinSign (x (Fin.last v.1.length)))
    simp only [ConnectedHull.path_zero, ConnectedHull.path_last] at hm hn hp
    unfold covariance LeafGibbs.covariance mean
    rw [hp, hm, hn]
    exact FinitePathGibbs.endpointCovariance_eq beta (y 0)
      (PathPosterior.childFields y) v.1.length
  rw [response, hcov]
  have hp := (variance_pos beta h hr).ne'
  field_simp

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InfiniteCanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

theorem finiteSiteField_eq_treeField {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = TreePathResponse.field beta y D v.1 := by
  unfold finiteSiteField TreePathResponse.field TreePathResponse.mean
  rw [GibbsLeaf.expectation_eq_fieldMean]
  simp only [extendFiniteSpin_apply D _ v]

theorem infiniteCavityField_eq_snd {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (u v : TreeVertex d) (y : TreeVertex d → ℝ) :
    infiniteCavityField hbeta v u y =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (infiniteGibbsSpinMean beta u y),
          Real.artanh (infiniteGibbsSpinMean beta v y))).2 :=
  CavityArray.field_reverse _ _ _ u v

theorem measurable_rootResponseProduct {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v : TreeVertex d) : Measurable (rootResponseProduct hbeta v) := by
  unfold rootResponseProduct
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i hi
  exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
    (measurable_infiniteCavityField hbeta _ _)

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.gaussian_rootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    gaussianPosteriorResponse μ t (ConnectedHull.root d) v =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  classical
  let D := connectedExhaustion v
  have hpath (i : ℕ) (hi : i ≤ v.1.length) (n : ℕ) :
      ConnectedHull.takeVertex v i ∈ D n := by
    exact ConnectedHull.prefix_mem_hull (Finset.mem_insert_self v (treeBallFinset d n)) hi
  have hr (n : ℕ) : ConnectedHull.root d ∈ D n := by
    simpa only [ConnectedHull.prefix_zero] using hpath 0 (Nat.zero_le _) n
  have hv (n : ℕ) : v ∈ D n := mem_connectedExhaustion v n
  have hconn (n : ℕ) : ConnectedFinset (D n) := connectedExhaustion_connected v n
  have hex (u : TreeVertex d) : ∃ n, u ∈ D n :=
    (eventually_mem_connectedExhaustion v u).exists
  have hfield (i : Fin (v.1.length + 1)) :
      ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
        Tendsto (fun n => TreePathResponse.field beta (observation t p) (D n)
          (ConnectedHull.takeVertex v i)) atTop
          (𝓝 (Real.artanh (infiniteGibbsSpinMean beta
            (ConnectedHull.takeVertex v i) (observation t p)))) := by
    have hh := hμ.exhaustionSiteField_tendsto_ae hbeta D
      (connectedExhaustion_monotone v) hconn hex (ConnectedHull.takeVertex v i)
      (hpath i (by omega)) t
    simpa only [finiteSiteField_eq_treeField] using hh
  have hprod : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (TreePathResponse.orientedCavity hbeta (observation t p) (D n)
            (ConnectedHull.takeVertex v i) (ConnectedHull.takeVertex v (i + 1))))
        atTop (𝓝 (rootResponseProduct hbeta v (observation t p))) := by
    filter_upwards [ae_all_iff.mpr hfield] with p hp
    apply Tendsto.const_mul
    apply tendsto_finsetProd
    intro i hi
    have hi' : i < v.1.length := Finset.mem_range.mp hi
    have hleft := hp ⟨i, by omega⟩
    have hright := hp ⟨i + 1, by omega⟩
    have hc := (continuous_snd.comp (continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hleft.prodMk_nhds hright)
    simp only [Function.comp_apply] at hc
    rw [← infiniteCavityField_eq_snd hbeta] at hc
    exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).continuousAt.tendsto.comp hc
  have hresponse := hμ.gaussian_posteriorResponse_tendsto_ae hbeta D
    (connectedExhaustion_monotone v) hex t (ConnectedHull.root d) v
  have hfinite (n : ℕ) := hμ.finiteObservation_normalizedResponse
    (D n) (hconn n) t ⟨ConnectedHull.root d, hr n⟩ ⟨v, hv n⟩
  filter_upwards [hresponse, hprod, ae_all_iff.mpr hfinite] with p hp hprod hfinite
  apply tendsto_nhds_unique hp
  apply hprod.congr'
  apply Eventually.of_forall
  intro n
  exact (hfinite n).trans
    (TreePathResponse.root_response_eq_canonical_product hbeta (observation t p)
      (hconn n) (hr n) (hv n)) |>.symm

theorem HasFreeIsingLaw.infiniteGibbsRootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta (ConnectedHull.root d) v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  filter_upwards [hμ.gaussian_rootResponse_eq_canonical_product hbeta t v,
    hμ.infiniteGibbsCovariance_eq_posterior t (ConnectedHull.root d) v,
    hμ.infiniteGibbsSpinMean_eq_posterior t (ConnectedHull.root d)] with p hp hc hm
  rw [infiniteGibbsResponse, hc, hm]
  exact hp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyResponseRowPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity ResponseRows PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem row_eq_product_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    row beta t v =ᵐ[observationLaw μ] fun x =>
      Real.tanh beta ^ v.1.length * pathProduct (Real.tanh beta)
        (Finset.range v.1.length) (pathCavity hb t v) x := by
  let f := infiniteGibbsResponse beta (ConnectedHull.root d) v
  let g := CavityFieldLimit.rootResponseProduct hb v
  have hm : MeasurableSet {y | f y = g y} := measurableSet_eq_fun
    (measurable_infiniteGibbsResponse beta _ _) (CavityFieldLimit.measurable_rootResponseProduct hb v)
  have hg : ∀ᵐ y ∂(μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (PlantedSymmetry.observation t),
      f y = g y :=
    (ae_map_iff (PlantedSymmetry.measurable_observation t).aemeasurable hm).mpr
      (hμ.infiniteGibbsRootResponse_eq_canonical_product hb t v)
  have heval : Measurable (fun x : Paths d => fun i => x i t) :=
    Measurable.of_eval (fun vertex => measurable_evaluation vertex t)
  have ho : ∀ᵐ x ∂observationLaw μ, f (fun i => x i t) = g (fun i => x i t) := by
    apply (ae_map_iff heval.aemeasurable hm).mp
    rw [(IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).map_eq]
    exact hg
  exact ho

theorem rows_eq_products_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (t : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      row beta t v q.2.1 = coefficient (Real.tanh beta)
        (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) (fun w i q => pathCavity hb t w i q.2.1) v q ∧
      row beta t v q.2.2 = coefficient (Real.tanh beta)
        (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) (fun w i q => pathCavity hb t w i q.2.2) v q := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  apply ae_all_iff.mpr
  intro v
  filter_upwards [hl.quasiMeasurePreserving.ae (row_eq_product_ae hμ hb t v),
    hr.quasiMeasurePreserving.ae (row_eq_product_ae hμ hb t v)] with q hql hqr
  exact ⟨hql, hqr⟩

end Problem367.IsingCopyResponseRowPaths

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

theorem initial_field_difference_energy (v : TreeVertex d) :
    (∫ p, (field beta v 0 p.2.1 - field beta v 0 p.2.2) ^ 2 ∂copies beta μ) = 0 := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact IsingConditionalCopyBounds.initial_fieldDifference_secondMoment_zero
    kernel_graphLaw v

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySpatialEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem actual_density_eq_path_density_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (t : ℝ≥0) :
    IsingCopyEnergy.density beta (root d) t =ᵐ[copies beta μ]
      DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
        (fun v q => row beta t v q.2.2) (fieldDifference beta (root d) t)
        (fun q => Real.tanh (field beta (root d) t q.2.1))
        (fun q => Real.tanh (field beta (root d) t q.2.2)) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have heq := tanh_field_eq_posterior_ae hμ hb (root d) t
  filter_upwards [hl.quasiMeasurePreserving.ae heq, hr.quasiMeasurePreserving.ae heq] with q hql hqr
  simp only [IsingCopyEnergy.density, IsingCopyEnergy.responseRow, Real.toNNReal_coe,
    DiscrepancyEnergy.density, row, fieldDifference, hql, hqr]
  rfl

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStrictComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity ResponseRows

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integral_density_le_subcritical
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (t : ℝ≥0) :
    let U := IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t
    let D := DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) U
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.1))
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.2))
    Integrable D (copies beta μ) ∧
      (∫ q, D q ∂copies beta μ) ≤
        subcriticalPathConstant d (Real.tanh beta)
          (2 * cavityLogVarianceCoefficient (Real.tanh beta)) *
            (∫ q, U q ^ 2 ∂copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  let X := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.1
  let Y := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.2
  let H := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.1
  let H' := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.2
  have hpath (v : TreeVertex d) (i : ℕ) : MemLp (pathCavity hb t v i) 2 (observationLaw μ) :=
    memLp_cavityObservable hμ hb t _ _
  have hXm (v : TreeVertex d) (i : ℕ) : Measurable (X v i) :=
    (measurable_cavityObservable hb t _ _).comp hl.measurable
  have hYm (v : TreeVertex d) (i : ℕ) : Measurable (Y v i) :=
    (measurable_cavityObservable hb t _ _).comp hr.measurable
  have hInt (v : TreeVertex d) (i : ℕ) :
      Integrable (fun q => (X v i q - Y v i q) ^ 2) (copies beta μ) :=
    ((hpath v i).comp_measurePreserving hl |>.sub
      ((hpath v i).comp_measurePreserving hr)).integrable_sq
  have hU : MemLp (fun q => H q - H' q) 2 (copies beta μ) :=
    ((memLp_field_at hμ hb t _).comp_measurePreserving hl).sub
      ((memLp_field_at hμ hb t _).comp_measurePreserving hr)
  have hlog (v : TreeVertex d) (i : ℕ) :
      (∫ q, (Real.log (responseAttenuation (Real.tanh beta) (X v i q)) -
        Real.log (responseAttenuation (Real.tanh beta) (Y v i q))) ^ 2 ∂copies beta μ) ≤
      cavityLogVarianceCoefficient (Real.tanh beta) *
        (∫ q, (H q - H' q) ^ 2 ∂copies beta μ) := by
    have h := norm_cavityLogDifference_sq_le hμ hb t (ConnectedHull.root d)
      (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i)
    rw [norm_observableDifference_sq] at h
    exact h
  have hmain := ResponseRows.integral_tree_density_le_subcritical
    (fun v : TreeVertex d => Finset.range v.1.length) (fun v => Finset.card_range _)
    (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_sq_lt_one beta).le hstrict
    (cavityLogVarianceCoefficient_nonneg (Real.tanh beta))
    (fun v i _ => hXm v i) (fun v i _ => hYm v i) (fun v i _ => hInt v i)
    ((measurable_field_at beta t _).comp hl.measurable)
    ((measurable_field_at beta t _).comp hr.measurable) hU (fun v i _ => hlog v i)
  have hd : DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) (fun q => H q - H' q)
      (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) =ᵐ[copies beta μ]
      DiscrepancyEnergy.density
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) X)
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) Y)
        (fun q => H q - H' q) (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) := by
    filter_upwards [rows_eq_products_ae hμ hb t] with q hq
    simp only [DiscrepancyEnergy.density, X, Y, (hq _).1, (hq _).2]
  exact ⟨hmain.1.congr hd.symm, (integral_congr_ae hd).trans_le hmain.2⟩

theorem root_variance_eq_zero_of_subcritical_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ)
    (hAC : AbsolutelyContinuousOnInterval
      (fun t : ℝ => ∫ q, (IsingConditionalCopyBounds.fieldDifference beta
        (ConnectedHull.root d) t.toNNReal q) ^ 2 ∂copies beta μ) 0 T)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv (fun s : ℝ => ∫ q, (IsingConditionalCopyBounds.fieldDifference beta
        (ConnectedHull.root d) s.toNNReal q) ^ 2 ∂copies beta μ) t =
      ∫ q, DiscrepancyEnergy.density (fun v q => row beta t.toNNReal v q.2.1)
        (fun v q => row beta t.toNNReal v q.2.2)
        (IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t.toNNReal)
        (fun q => Real.tanh (field beta (ConnectedHull.root d) t.toNNReal q.2.1))
        (fun q => Real.tanh (field beta (ConnectedHull.root d) t.toNNReal q.2.2)) q
          ∂copies beta μ) :
    ∀ t ∈ Icc 0 T, (∫ q, (IsingConditionalCopyBounds.fieldDifference beta
      (ConnectedHull.root d) t.toNNReal q) ^ 2 ∂copies beta μ) = 0 := by
  apply eq_zero_of_ae_deriv_le_mul_self
    (C := subcriticalPathConstant d (Real.tanh beta)
      (2 * cavityLogVarianceCoefficient (Real.tanh beta))) hAC
  · simpa only [Real.toNNReal_zero, IsingConditionalCopyBounds.fieldDifference, field] using
      (initial_field_difference_energy (beta := beta) (μ := μ) (ConnectedHull.root d))
  · exact fun t _ => integral_nonneg (fun q => sq_nonneg _)
  · filter_upwards [hderiv] with t ht hmem
    rw [ht hmem]
    exact (integral_density_le_subcritical hμ hb hstrict t.toNNReal).2

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

theorem siteVariance_eq_zero_of_subcritical_actual_variance_identity_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ≥0)
    (hAC : AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  have hrestricted := (ae_restrict_iff' measurableSet_Icc).mp hderiv
  have hpath : ∀ᵐ t : ℝ, t ∈ Icc 0 (T : ℝ) →
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, DiscrepancyEnergy.density
          (fun v q => row beta t.toNNReal v q.2.1)
          (fun v q => row beta t.toNNReal v q.2.2)
          (IsingConditionalCopyBounds.fieldDifference beta (root d) t.toNNReal)
          (fun q => Real.tanh (field beta (root d) t.toNNReal q.2.1))
          (fun q => Real.tanh (field beta (root d) t.toNNReal q.2.2)) q
            ∂copies beta μ := by
    filter_upwards [hrestricted] with t ht hmem
    rw [ht hmem]
    have he := actual_density_eq_path_density_ae hμ hb t.toNNReal
    rw [Real.coe_toNNReal t hmem.1] at he
    exact integral_congr_ae he
  have hzero := root_variance_eq_zero_of_subcritical_variance_identity
    hμ hb hstrict (T : ℝ) hAC hpath
  intro t ht
  simpa only [Real.toNNReal_coe, siteVariance] using
    hzero (t : ℝ) ⟨t.coe_nonneg, ht⟩

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity_oai := @OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity_oai
