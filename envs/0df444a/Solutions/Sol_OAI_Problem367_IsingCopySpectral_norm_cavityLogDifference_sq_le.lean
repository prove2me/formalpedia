-- Prove2me | solution 1 for OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:39.879187+00:00
-- url     : https://prove2.me/submissions/e0d46487-5023-457a-9fe0-7500f0930aff

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledAttenuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

theorem cavity_pair_sub_sq_le
    {theta x y x' y' H K H' K' : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K') :
    (x - x') ^ 2 ≤
      ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  have hsquare := (sq_le_sq₀ (abs_nonneg (x - x'))
    (show 0 ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) by positivity)).2 habs
  rw [sq_abs, div_pow] at hsquare
  have hweighted : (|H - H'| + theta * |K - K'|) ^ 2 ≤
      (1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
    have h := mul_nonneg hθ0 (sq_nonneg (|H - H'| - |K - K'|))
    nlinarith [sq_abs (H - H'), sq_abs (K - K')]
  calc
    (x - x') ^ 2 ≤ (|H - H'| + theta * |K - K'|) ^ 2 /
        (1 - theta ^ 2) ^ 2 := hsquare
    _ ≤ ((1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2)) /
        (1 - theta ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hweighted (sq_nonneg _)
    _ = _ := by ring

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem integrable_cavity_pair_sub_sq
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω) :
    Integrable (fun ω => (X ω - X' ω) ^ 2) μ := by
  apply ((hH.add (hK.const_mul theta)).const_mul
    ((1 + theta) / (1 - theta ^ 2) ^ 2)).mono'
    (((hX.sub hX').pow_const 2).aestronglyMeasurable)
  filter_upwards [heq] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2

theorem integral_cavity_pair_sub_sq_le
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V : ℝ}
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V) :
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤ V / (1 - theta) ^ 2 := by
  have hXint := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hcoef : 0 ≤ (1 + theta) / (1 - theta ^ 2) ^ 2 := by positivity
  calc
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤
        ∫ ω, ((1 + theta) / (1 - theta ^ 2) ^ 2) *
          ((H ω - H' ω) ^ 2 + theta * (K ω - K' ω) ^ 2) ∂μ := by
      apply integral_mono_ae hXint
        ((hH.add (hK.const_mul theta)).const_mul _)
      filter_upwards [heq] with ω hω
      exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2
    _ = ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((∫ ω, (H ω - H' ω) ^ 2 ∂μ) +
          theta * ∫ ω, (K ω - K' ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add hH (hK.const_mul theta), integral_const_mul]
    _ ≤ ((1 + theta) / (1 - theta ^ 2) ^ 2) * (V + theta * V) := by
      gcongr
    _ = V / (1 - theta) ^ 2 := by
      field_simp
      ring

theorem integral_cavity_log_discrepancy_sq_le
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V : ℝ}
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      4 / (1 - theta) ^ 2 * V := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hXint := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  calc
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
        ∫ ω, 4 * (X ω - X' ω) ^ 2 ∂μ :=
      integral_mono
        (integrable_log_responseAttenuation_sub_sq hθsq hX hX' hXint)
        (hXint.const_mul 4) (fun _ => log_responseAttenuation_sub_sq_le hθsq)
    _ = 4 * ∫ ω, (X ω - X' ω) ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ 4 * (V / (1 - theta) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (integral_cavity_pair_sub_sq_le hθ0 hθ1 hX hX' hH hK heq hHV hKV)
        (by norm_num)
    _ = 4 / (1 - theta) ^ 2 * V := by ring

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
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

theorem field_spec (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H v w + cavityMessage theta (field h0 h1 H w v) = H v := by
  rw [field_reverse h0 h1 H v w]
  exact (cavityFromSites_spec h0 h1 (H v, H w)).1

section Joining

theorem measurable_pairRelabel (g : TreeAut d) : Measurable (pairRelabel g) :=
  (measurable_relabel g).prodMap (measurable_relabel g)

theorem site_sub_identDistrib {ν : Measure (SitePair d)}
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (u v : TreeVertex d) :
    IdentDistrib (fun p : SitePair d => p.1 u - p.2 u)
      (fun p : SitePair d => p.1 v - p.2 v) ν ν := by
  obtain ⟨g, hg⟩ := exists_treeAut_map u v
  have hm (w : TreeVertex d) : Measurable (fun p : SitePair d => p.1 w - p.2 w) :=
    ((measurable_pi_apply w).comp measurable_fst).sub
      ((measurable_pi_apply w).comp measurable_snd)
  refine ⟨(hm u).aemeasurable, (hm v).aemeasurable, ?_⟩
  calc
    ν.map (fun p : SitePair d => p.1 u - p.2 u) =
        ν.map ((fun p : SitePair d => p.1 v - p.2 v) ∘ pairRelabel g) := by
      congr 1
      funext p
      simp [pairRelabel, relabel, ← hg]
    _ = (ν.map (pairRelabel g)).map (fun p : SitePair d => p.1 v - p.2 v) :=
      (Measure.map_map (hm v) (measurable_pairRelabel g)).symm
    _ = ν.map (fun p : SitePair d => p.1 v - p.2 v) := by rw [(hinv g).map_eq]

end Joining

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_ArraySmallLogLoss
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem integral_log_field_sub_sq_le
    {ν : Measure (SitePair d)}
    (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (o v w : TreeVertex d)
    (hInt : Integrable (fun p : SitePair d => (p.1 o - p.2 o) ^ 2) ν) :
    (∫ p, (Real.log (responseAttenuation theta (field h0 h1 p.1 v w)) -
        Real.log (responseAttenuation theta (field h0 h1 p.2 v w))) ^ 2 ∂ν) ≤
      cavityLogVarianceCoefficient theta *
        (∫ p : SitePair d, (p.1 o - p.2 o) ^ 2 ∂ν) := by
  have hv := (site_sub_identDistrib hinv o v).sq
  have hw := (site_sub_identDistrib hinv o w).sq
  exact integral_cavity_log_discrepancy_sq_le h0 h1
    ((measurable_field_apply h0 h1 v w).comp measurable_fst)
    ((measurable_field_apply h0 h1 v w).comp measurable_snd)
    (hv.integrable_snd hInt) (hw.integrable_snd hInt)
    (Filter.Eventually.of_forall (fun p =>
      ⟨field_spec h0 h1 p.1 v w, field_spec h0 h1 p.1 w v,
        field_spec h0 h1 p.2 v w, field_spec h0 h1 p.2 w v⟩))
    hv.integral_eq.symm.le hw.integral_eq.symm.le

end Problem367.CavityArray

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem posterior_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => posterior beta v t (relabel g x)) =ᵐ[observationLaw μ]
      posterior beta (g.toEquiv.symm v) t := by
  have hm (w : TreeVertex d) : Measurable (posterior beta w t) :=
    (measurable_infiniteGibbsSpinMean beta w).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun ((hm v).comp (measurable_relabel g))
      (hm (g.toEquiv.symm v)))).mpr
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have h := ArrayPosteriorStationarity.posterior_version_relabel_ae hμ uniform01
    (fun s u => WienerSampler.sample u s) hmB
    (fun s w => IsingInnovation.posterior_eq_condExp hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB s w) g t v
  exact h

omit [IsProbabilityMeasure μ] in
theorem field_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) (t : ℝ≥0) :
    (fun x v => field beta v t (relabel g x)) =ᵐ[observationLaw μ]
      (fun x => relabel g (fun v => field beta v t x)) := by
  filter_upwards [ae_all_iff.mpr (fun v => posterior_relabel_ae hμ g t v)] with x hx
  funext v
  exact congrArg Real.artanh (hx v)

theorem measurable_sitePair (beta : ℝ) (t : ℝ≥0) :
    Measurable (sitePair (d := d) beta t) := by
  have hm (v : TreeVertex d) : Measurable (field beta v t) := by
    have hp : Measurable (posterior beta v t) :=
      (measurable_infiniteGibbsSpinMean beta v).comp
        (Measurable.of_eval (fun i => measurable_evaluation i t))
    unfold field Real.artanh
    exact ((measurable_const.add hp).div (measurable_const.sub hp)).sqrt.log
  exact (Measurable.of_eval (fun v => (hm v).comp (measurable_fst.comp measurable_snd))).prodMk
    (Measurable.of_eval (fun v => (hm v).comp (measurable_snd.comp measurable_snd)))

theorem measurePreserving_sitePair_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (g : TreeAut d) :
    MeasurePreserving (CavityArray.pairRelabel g)
      ((copies beta μ).map (sitePair beta t))
      ((copies beta μ).map (sitePair beta t)) := by
  refine ⟨CavityArray.measurable_pairRelabel g, ?_⟩
  apply FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_copies_relabel hμ g) (CavityArray.measurable_pairRelabel g)
    (measurable_sitePair beta t)
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t),
    hr.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t)] with q hq hq'
  exact Prod.ext hq hq'

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyCavityBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integrable_fieldDifference_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Integrable (fun q => (IsingConditionalCopyBounds.fieldDifference beta v t q) ^ 2)
      (copies beta μ) := by
  exact (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds hμ hbeta
    (ObservableDisintegration.compProd_kernel (observationLaw μ)
      (measurable_innovationMap beta)) t v).1.integrable_sq

theorem integrable_sitePair_sub_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Integrable (fun p : CavityArray.SitePair d => (p.1 v - p.2 v) ^ 2)
      ((copies beta μ).map (sitePair beta t)) := by
  have hm : Measurable (fun p : CavityArray.SitePair d => (p.1 v - p.2 v) ^ 2) :=
    (((measurable_pi_apply v).comp measurable_fst).sub
      ((measurable_pi_apply v).comp measurable_snd)).pow_const 2
  exact (integrable_map_measure hm.aestronglyMeasurable
    (measurable_sitePair beta t).aemeasurable).mpr
      (integrable_fieldDifference_sq hμ hbeta t v)

theorem integral_sitePair_log_cavity_sub_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    let h0 := tanh_nonneg_of_beta_nonneg hbeta
    let h1 := Real.tanh_lt_one beta
    let P := (copies beta μ).map (sitePair beta t)
    (∫ p, (Real.log (responseAttenuation (Real.tanh beta) (CavityArray.field h0 h1 p.1 v w)) -
      Real.log (responseAttenuation (Real.tanh beta) (CavityArray.field h0 h1 p.2 v w))) ^ 2 ∂P) ≤
        cavityLogVarianceCoefficient (Real.tanh beta) *
          (∫ p : CavityArray.SitePair d, (p.1 o - p.2 o) ^ 2 ∂P) := by
  exact CavityArray.integral_log_field_sub_sq_le
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (measurePreserving_sitePair_relabel hμ t) o v w
    (integrable_sitePair_sub_sq hμ hbeta t o)

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
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

theorem norm_cavityLogDifference_sq_le_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    ‖observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)‖ ^ 2 ≤
      cavityLogVarianceCoefficient (Real.tanh beta) *
        ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ := by
  rw [norm_observableDifference_sq]
  have h := integral_sitePair_log_cavity_sub_sq_le hμ hbeta t o v w
  have hm (a b : TreeVertex d) : Measurable (fun p : CavityArray.SitePair d =>
      (Real.log (responseAttenuation (Real.tanh beta)
        (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta) p.1 a b)) -
       Real.log (responseAttenuation (Real.tanh beta)
        (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta) p.2 a b))) ^ 2) := by
    have ht : (Real.tanh beta) ^ 2 ≤ 1 := by
      have h0 := tanh_nonneg_of_beta_nonneg hbeta
      have h1 := Real.tanh_lt_one beta
      nlinarith
    have hl := (lipschitzWith_log_responseAttenuation ht).continuous.measurable
    have hc := CavityArray.measurable_field_apply (tanh_nonneg_of_beta_nonneg hbeta)
      (Real.tanh_lt_one beta) a b
    exact ((hl.comp (hc.comp measurable_fst)).sub (hl.comp (hc.comp measurable_snd))).pow_const 2
  have hs : Measurable (fun p : CavityArray.SitePair d => (p.1 o - p.2 o) ^ 2) :=
    (((measurable_pi_apply o).comp measurable_fst).sub
      ((measurable_pi_apply o).comp measurable_snd)).pow_const 2
  dsimp only at h
  rw [integral_map (measurable_sitePair beta t).aemeasurable (hm v w).aestronglyMeasurable,
    integral_map (measurable_sitePair beta t).aemeasurable hs.aestronglyMeasurable] at h
  exact h

end Problem367.IsingCopySpectral

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le_oai := @OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le_oai
