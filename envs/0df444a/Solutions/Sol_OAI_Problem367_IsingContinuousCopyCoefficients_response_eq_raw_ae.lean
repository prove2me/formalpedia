-- Prove2me | solution 1 for OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:12.019089+00:00
-- url     : https://prove2.me/submissions/9209cae0-caa6-4333-a788-22a2d1d0d41f

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior

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

end Problem367.IsingObservationFactor

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

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousRootResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

theorem continuousRootResponse_eq_response_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    continuousRootResponse hb v t =ᵐ[observationLaw μ]
      fun x => infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => x i t) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he (i : TreeVertex d) := (continuousField_modification hd hμ hb hcrit i).2 t
  filter_upwards [ae_all_iff.mpr he,
    IsingCopyResponseRowPaths.row_eq_product_ae hμ hb t v] with x hx hr
  change siteRootResponse hb v (fun i => continuousField beta i t x) = _
  rw [show (fun i => continuousField beta i t x) = (fun i => field beta i t x)
    from funext hx]
  exact hr.symm

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCopyCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

lemma projection_preserving {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingCopyStationarity.measurePreserving_observations
    (beta := beta) (μ := μ)
  cases j
  · exact hr
  · exact hl

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma response_eq_raw_ae_oai (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) (t : ℝ≥0) :
    response hb j v t =ᵐ[copies beta μ] fun q =>
      infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => projection j q i t) :=
  (projection_preserving (beta := beta) (μ := μ) j).quasiMeasurePreserving.ae
    (continuousRootResponse_eq_response_ae hd hμ hb hcrit v t)

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae_oai := @OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae_oai
