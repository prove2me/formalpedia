-- Prove2me | solution 1 for OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:35.77055+00:00
-- url     : https://prove2.me/submissions/1c63853d-06a9-4fcf-baf5-426d196a0e36

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_integral_cutContinuationProduct_gaussianConeFactor_le
import Theorems.Thm_OAI_Problem367_measure_gaussian_inward_restricted_path_average_ge_le_double_exp

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem binaryFusion_abs_mul_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |u * v| < 1 := by
  rw [abs_mul]
  calc
    |u| * |v| ≤ |u| * 1 := mul_le_mul_of_nonneg_left hv.le (abs_nonneg u)
    _ < 1 := by simpa using hu

theorem binaryFusion_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 + u * v := by
  have h := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).1
  linarith

theorem one_sub_binaryFusion_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    1 - binaryFusion u v ^ 2 =
      (1 - u ^ 2) * (1 - v ^ 2) / (1 + u * v) ^ 2 := by
  have hd := ne_of_gt (binaryFusion_denominator_pos hu hv)
  unfold binaryFusion
  field_simp
  ring

theorem abs_binaryFusion_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |binaryFusion u v| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have hu' : 0 < 1 - u ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  have hv' : 0 < 1 - v ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one v).mpr hv
    linarith
  have hd := binaryFusion_denominator_pos hu hv
  have hpos : 0 < 1 - binaryFusion u v ^ 2 := by
    rw [one_sub_binaryFusion_sq hu hv]
    positivity
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_ArtanhFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tanh_add_eq_binaryFusion (a b : ℝ) :
    Real.tanh (a + b) = binaryFusion (Real.tanh a) (Real.tanh b) := by
  have ha : |Real.tanh a| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one a)
  have hb : |Real.tanh b| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one b)
  apply (eq_div_iff (binaryFusion_denominator_pos ha hb).ne').2
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  have hc : Real.cosh b * Real.cosh a + Real.sinh a * Real.sinh b ≠ 0 := by
    simpa only [Real.cosh_add, mul_comm] using (Real.cosh_pos (a + b)).ne'
  exact mul_div_cancel_right₀ _ hc

theorem artanh_binaryFusion {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh (binaryFusion x y) = Real.artanh x + Real.artanh y := by
  apply Real.tanh_injective
  rw [Real.tanh_artanh (abs_lt.mp (abs_binaryFusion_lt_one hx hy)),
    tanh_add_eq_binaryFusion, Real.tanh_artanh (abs_lt.mp hx),
    Real.tanh_artanh (abs_lt.mp hy)]

theorem artanh_binaryFusion_scaled {theta x y : ℝ}
    (hθ : |theta| < 1) (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) := by
  have hprod : |theta * y| < 1 := binaryFusion_abs_mul_lt_one hθ hy
  have h := artanh_binaryFusion hx hprod
  simpa only [binaryFusion, cavityMessage, Real.tanh_artanh (abs_lt.mp hy),
    mul_left_comm, mul_assoc] using h

theorem artanh_binaryFusion_scaled_of_mem {theta x y : ℝ}
    (hθ : theta ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) :=
  artanh_binaryFusion_scaled (abs_lt.mpr hθ) (abs_lt.mpr hx) (abs_lt.mpr hy)

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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

private theorem measurable_artanh_field : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem tendsto_integral_sq_sub_posterior_fields
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ m) (f X : Ω → ℝ) {K : ℝ}
    (hb : ∀ n, ∀ᵐ ω ∂μ,
      Real.tanh (X ω - K) ≤ (μ[f | F n]) ω ∧
        (μ[f | F n]) ω ≤ Real.tanh (X ω + K)) :
    Tendsto (fun n => ∫ ω,
      (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hs : (⨆ n, F n) ≤ m := iSup_le (fun n => F.le n)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono (F.le n)).measurable).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | ⨆ n, F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono hs).measurable).aestronglyMeasurable
  have hlim := tendsto_posterior_fields_ae μ F f X K hb
  have hbfield (n : ℕ) : ∀ᵐ ω ∂μ,
      |Real.artanh ((μ[f | F n]) ω) - X ω| ≤ K := by
    filter_upwards [hb n] with ω hω
    exact (posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => (μ[f | F n]) ω) tendsto_const_nhds
      (fun _ => hω)).2.1
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖(Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2‖ ≤ (2 * K) ^ 2 := by
    filter_upwards [hbfield n, hlim] with ω hn hω
    have hd : |Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)| ≤ 2 * K := by
      calc
        _ = |(Real.artanh ((μ[f | F n]) ω) - X ω) -
            (Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω)| := by congr 1; ring
        _ ≤ |Real.artanh ((μ[f | F n]) ω) - X ω| +
            |Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hω.2.1]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hzero : ∀ᵐ ω ∂μ, Tendsto
      (fun n => (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    simpa using (hω.2.2.sub_const (Real.artanh ((μ[f | ⨆ n, F n]) ω))).pow 2
  simpa using tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (2 * K) ^ 2) (fun n => ((hm n).sub hm').pow 2)
    (integrable_const _) hbound hzero

open PlantedSymmetry

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

theorem HasFreeIsingLaw.exhaustionCavityField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v w : TreeVertex d) (hv : ∀ n, v ∈ D n) (hw : ∀ n, w ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩
        (observation t p)) atTop (𝓝 (infiniteCavityField hbeta v w (observation t p))) := by
  filter_upwards [hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex v hv t,
    hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex w hw t] with p hp hq
  exact (continuous_fst.comp (continuous_cavityFromSites
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hp.prodMk_nhds hq)

end Problem367

end

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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BalancedLatentMean
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

private theorem integrable_of_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2)

theorem integral_binary_channel_le_two_integral
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (a : IsingSpin) :
    (∫ r, F (a, r) ∂ν) ≤
      2 * ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
  let : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
  let E : Set S := {s | b s = a}
  let q : S → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_eq_fun hb measurable_const
  have hq : Measurable q := measurable_const.indicator hE
  have hleft : Measurable (fun z : S × A => q z.1 * F (a, z.2)) :=
    (hq.comp measurable_fst).mul (hF.comp (measurable_const.prodMk measurable_snd))
  have hright : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hleftbound : ∀ z : S × A,
      0 ≤ q z.1 * F (a, z.2) ∧ q z.1 * F (a, z.2) ≤ 1 := by
    intro z
    by_cases hz : b z.1 = a
    · simpa [q, E, hz] using hbound (a, z.2)
    · simp [q, E, hz]
  have hmono := integral_mono
    (integrable_of_unit_bounds (ρ.prod ν) hleft hleftbound)
    (integrable_of_unit_bounds (ρ.prod ν) hright (fun z => hbound (b z.1, z.2)))
    (show ∀ z : S × A, q z.1 * F (a, z.2) ≤ F (b z.1, z.2) from by
      intro z
      by_cases hz : b z.1 = a
      · simp [q, E, hz]
      · simpa [q, E, hz] using (hbound (b z.1, z.2)).1)
  have hmass : (∫ s, q s ∂ρ) = (1 / 2 : ℝ) := by
    rw [show q = E.indicator (fun _ => 1) from rfl, integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one, Measure.real, E, hfair]
    norm_num
  rw [integral_prod_mul q (fun r => F (a, r)), hmass] at hmono
  linarith

theorem condExp_binary_channel_le_two_integral
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂ρ.prod ν,
      ((ρ.prod ν)[(fun z : S × A => F (b z.1, z.2)) | mS.comap Prod.fst]) z ≤
        2 * ∫ w : S × A, F (b w.1, w.2) ∂ρ.prod ν := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  filter_upwards [condExp_prod_fst ρ ν hm.stronglyMeasurable hi] with z hz
  rw [hz]
  exact integral_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound (b z.1)

theorem condExp_binary_channel_comp_le_two_integral
    {Ω S A : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace A]
    (μ : Measure Ω) (ρ : Measure S) (ν : Measure A)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (e : Ω → S × A) (he : MeasurePreserving e μ (ρ.prod ν))
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ ω ∂μ,
      (μ[(fun ω => F (b (e ω).1, (e ω).2)) |
        mS.comap (fun ω => (e ω).1)]) ω ≤
          2 * ∫ x, F (b (e x).1, (e x).2) ∂μ := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  have hpull := condExp_comp_measurePreserving μ (ρ.prod ν) e he
    (mS.comap Prod.fst) measurable_fst.comap_le hi
  have hboundpull := he.quasiMeasurePreserving.ae
    (condExp_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound)
  have hint : (∫ x, F (b (e x).1, (e x).2) ∂μ) =
      ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable
      (hm.aestronglyMeasurable)).symm
  rw [hint]
  filter_upwards [hpull, hboundpull] with ω hω hωb
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hω.trans_le hωb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_DiscreteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace Problem367

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => ∫ ω, f ω ∂μ[|S ⁻¹' {a}] := by
  let s := S ⁻¹' {a}
  have hs : MeasurableSet s := hS (measurableSet_singleton a)
  have hs' : MeasurableSet[MeasurableSpace.comap S inferInstance] s :=
    ⟨{a}, measurableSet_singleton a, rfl⟩
  by_cases hμs : μ s = 0
  · rw [show S ⁻¹' {a} = s from rfl, Measure.restrict_eq_zero.2 hμs]
    rfl
  have havg : (∫ ω, (∫ x, f x ∂μ[|s]) ∂μ.restrict s) =
      ∫ ω, f ω ∂μ.restrict s := by
    rw [integral_const, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨hμs, measure_ne_top _ _⟩), one_mul]
  refine (condExp_restrict_ae_eq_restrict hS.comap_le hs' hf).symm.trans ?_
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hf.restrict
  · intro t _ _
    exact (integrable_const _).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    rw [Measure.restrict_restrict (hS hu)]
    by_cases ha : a ∈ u
    · have heq : S ⁻¹' u ∩ s = s := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
      rw [heq]
      exact havg
    · have heq : S ⁻¹' u ∩ s = ∅ := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h hEq
        exact ha (hEq ▸ h)
      simp [heq]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem condExp_indicator_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {t : Set Ω} (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.comap S inferInstance⟧ =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => μ[|S ⁻¹' {a}].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_comap_eq_cond_on_fiber hS a ((integrable_const (1 : ℝ)).indicator ht)

theorem iIndepFun_cond_fiber_of_iCondIndepFun [StandardBorelSpace Ω]
    {ι : Type*} {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {S : Ω → A} {X : ∀ i, Ω → B i}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hXI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X μ)
    (a : A) (hμa : μ (S ⁻¹' {a}) ≠ 0) : iIndepFun X μ[|S ⁻¹' {a}] := by
  classical
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hsets
  have hcond := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB X hX).mp hXI I hsets
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hmeas : MeasurableSet (⋂ i ∈ I, X i ⁻¹' sets i) :=
    Finset.measurableSet_biInter I (fun i hi => hX i (hsets i hi))
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a hmeas
  have heach : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), ∀ i ∈ I,
      (μ⟦X i ⁻¹' sets i | MeasurableSpace.comap S inferInstance⟧) ω =
        μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    apply (Finset.eventually_all I).mpr
    intro i hi
    exact condExp_indicator_comap_eq_cond_on_fiber hS a (hX i (hsets i hi))
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (⋂ i ∈ I, X i ⁻¹' sets i) =
        ∏ i ∈ I, μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    filter_upwards [hcond', hleft, heach] with ω h h₁ h₂
    rw [h₁] at h
    simp only [Finset.prod_apply] at h
    exact h.trans (Finset.prod_congr rfl h₂)
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun i hi => measure_ne_top _ _))).mp
  simpa only [measureReal_def, ENNReal.toReal_prod] using hω

omit [IsFiniteMeasure μ] in

theorem ae_of_ae_restrict_fibers [Countable A] {S : Ω → A} (hS : Measurable S)
    {p : Ω → Prop} (h : ∀ a : A, ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} → p ω := by
    apply ae_all_iff.mpr
    intro a
    exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (h a)
  filter_upwards [hAll] with ω hω
  exact hω (S ω) rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DependentInfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace Problem367

variable {I : Type*} {A B : I → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

theorem measurePreserving_dependentPiPairEquiv [Fintype I]
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiPairEquiv (A := A) (B := B))
      (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := dependentPiPairEquiv.measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have heq : dependentPiPairEquiv ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          univ.pi (fun i => s i ×ˢ t i) := by
        ext x
        simp [dependentPiPairEquiv, mem_pi, forall_and]
      rw [heq]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

theorem infinitePi_map_pair_dependent_arrays
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      (fun p : (∀ i : s, A i) × (∀ i : s, B i) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_dependentPiPairEquiv
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

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
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

lemma factor_congr_prefix {d : ℕ} (theta : ℝ) (U V : TreeVertex d → ℝ)
    (v : TreeVertex d) (heq : ∀ w : TreeVertex d, w.val <+: v.val → U w = V w) :
    factor theta U v = factor theta V v := by
  apply ofNoise_congr_prefix
  intro w hw
  simp only [inputNoise, heq w hw]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem ofNoise_congr_cone {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (c : TreeVertex d) (hbase : ofNoise noise₁ c = ofNoise noise₂ c)
    (hedge : ∀ w : TreeVertex d, c.1 <+: w.1 → w ≠ c → noise₁ w = noise₂ w)
    (v : TreeVertex d) (hcv : c.1 <+: v.1) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → c.1 <+: v.1 →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hcv
      by_cases hvc : v = c
      · simpa only [hvc] using hbase
      · have hlt : c.1.length < v.1.length := by
          have hle := hcv.length_le
          have hne : c.1.length ≠ v.1.length := by
            intro heq
            exact hvc (Subtype.ext (hcv.eq_of_length heq).symm)
          omega
        have hnil : v.1 ≠ [] := by
          intro hh
          simp only [hh, List.length_nil] at hlt
          omega
        have hcp : c.1 <+: (parent v).1 := by
          apply List.prefix_of_prefix_length_le hcv (List.dropLast_prefix v.1)
          change c.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        have hp : (parent v).1.length < n := by
          change (parentVertex v).1.length < n
          rw [parentVertex_length]
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        exact congrArg₂ spinMul (hedge v hcv hvc) (ih _ hp _ rfl hcp)
  exact h _ v rfl hcv

theorem measurable_coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (fun p : IsingSpin × (StrictDescendantVertex c → ℝ) =>
      coneNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.1 = []
  · simpa only [coneNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst :
        IsingSpin × (StrictDescendantVertex c → ℝ) → IsingSpin))
  · by_cases hv : c.1 <+: v.1 ∧ v ≠ c
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : StrictDescendantVertex c => ℝ)
            ⟨v, hv⟩).comp measurable_snd)
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ :
          IsingSpin × (StrictDescendantVertex c → ℝ) => IsingSpin.pos))

theorem ofNoise_coneNoise_at_root {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) :
    ofNoise (coneNoise theta c s Y) c = s := by
  calc
    ofNoise (coneNoise theta c s Y) c =
        ofNoise (noiseFromSpins (fun _ : TreeVertex d => s)) c := by
      apply ofNoise_congr_prefix
      intro w hw
      have hnot : ¬ (c.1 <+: w.1 ∧ w ≠ c) := by
        rintro ⟨hcw, hne⟩
        exact hne (Subtype.ext (hw.eq_of_length_le hcw.length_le))
      by_cases hnil : w.1 = [] <;>
        simp [coneNoise, noiseFromSpins, hnil, hnot]
    _ = s := congrFun (ofNoise_noiseFromSpins (fun _ : TreeVertex d => s)) c

theorem measurable_coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (coneFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.1).comp (measurable_coneNoise theta c)

theorem factor_cone_representation {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (U : TreeVertex d → ℝ) :
    (fun v : DescendantVertex c => factor theta U v.1) =
      coneFactor theta c (factor theta U c,
        fun w : StrictDescendantVertex c => U w.1) := by
  funext v
  apply ofNoise_congr_cone (inputNoise theta U) _ c
  · exact (ofNoise_coneNoise_at_root theta c (factor theta U c) _).symm
  · intro w hcw hne
    have hnil : w.1 ≠ [] := by
      intro hw
      have hc : c.1 = [] := by simpa only [hw, List.prefix_nil] using hcw
      exact hne (Subtype.ext (hw.trans hc.symm))
    simp [inputNoise, coneNoise, hnil, hcw, hne]
  · exact v.2

end Problem367.RootedBroadcast

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

theorem indepFun_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T) :
    IndepFun (fun ω (i : S) => f i ω) (fun ω (i : T) => f i ω) μ := by
  change Indep (MeasurableSpace.comap (fun ω (i : S) => f i ω) inferInstance)
    (MeasurableSpace.comap (fun ω (i : T) => f i ω) inferInstance) μ
  simp only [MeasurableSpace.comap_process_pi, iSup_subtype]
  exact indep_iSup_of_disjoint (fun i => (hm i).comap_le) hf hst

theorem indepFun_of_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω => F (fun i => f i ω))
      (fun ω => G (fun i => f i ω)) μ :=
  (indepFun_disjoint_blocks hf hm S T hst).comp hF hG

theorem indepFun_infinitePi_disjoint_blocks
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun U : ∀ i, X i => F (fun i => U i))
      (fun U : ∀ i, X i => G (fun i => U i)) (Measure.infinitePi ν) :=
  indepFun_of_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S T hst F G hF hG

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

local instance localInst_r8629fa_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutLevelBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

theorem strictDescendant_length_gt {d n : ℕ} (c : TreeShell d n)
    (v : StrictDescendantVertex c.1) : n < v.1.1.length := by
  have hle := v.2.1.length_le
  have hne : c.1.1.length ≠ v.1.1.length := by
    intro h
    exact v.2.2 (Subtype.ext (v.2.1.eq_of_length h).symm)
  rw [c.2] at hle hne
  omega

theorem cutLevel_descendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1}
        {v : TreeVertex d | e.1.1 <+: v.1}) := by
  intro c e hce
  apply Set.disjoint_left.mpr
  intro v hc he
  have hpre : c.1.1 <+: e.1.1 :=
    List.prefix_of_prefix_length_le hc he (by simp only [c.2, e.2, le_refl])
  exact hce (Subtype.ext (Subtype.ext (hpre.eq_of_length (c.2.trans e.2.symm))))

theorem cutLevel_strictDescendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1}
        {v : TreeVertex d | e.1.1 <+: v.1 ∧ v ≠ e.1}) := by
  intro c e hce
  exact (cutLevel_descendants_disjoint hce).mono
    (fun _ h => h.1) (fun _ h => h.1)

theorem measurable_cutUpperExtension (d n : ℕ) :
    Measurable (@cutUpperExtension d n) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.1.length ≤ n
  · simpa only [cutUpperExtension, dite_eq_left hv] using
      (measurable_pi_apply (X := fun _ : TreeBall d n => ℝ) ⟨v, hv⟩)
  · simpa only [cutUpperExtension, dite_eq_right hv] using
      (measurable_const : Measurable (fun _ : TreeBall d n → ℝ => (0 : ℝ)))

theorem cutSpins_upper_extension {d : ℕ} (theta : ℝ) (n : ℕ)
    (U : TreeVertex d → ℝ) :
    cutSpins theta n (cutUpperExtension (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n U := by
  funext c
  apply factor_congr_prefix
  intro w hw
  have hlen : w.1.length ≤ n := hw.length_le.trans_eq c.2
  simp only [cutUpperExtension, dite_eq_left hlen]

theorem measurable_cutLabels (d n : ℕ) : Measurable (@cutLabels d n) := by
  unfold cutLabels
  fun_prop

theorem indepFun_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    IndepFun (cutSpins theta n) (@cutLabels d n) (labelMeasure d) := by
  let F : (TreeBall d n → ℝ) → (TreeShell d n → IsingSpin) :=
    fun U => cutSpins theta n (cutUpperExtension U)
  let G : ({v : TreeVertex d // n < v.1.length} → ℝ) →
      ((c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ) :=
    fun U c v => U ⟨v.1, strictDescendant_length_gt c v⟩
  have hF : Measurable F :=
    (measurable_cutSpins d theta n).comp (measurable_cutUpperExtension d n)
  have hG : Measurable G := by fun_prop
  have hdisj : Disjoint {v : TreeVertex d | v.1.length ≤ n}
      {v : TreeVertex d | n < v.1.length} := by
    apply Set.disjoint_left.mpr
    intro v hle hlt
    exact (not_lt_of_ge (show v.1.length ≤ n from hle))
      (show n < v.1.length from hlt)
  have h := indepFun_infinitePi_disjoint_blocks (fun _ : TreeVertex d => uniform01)
    {v : TreeVertex d | v.1.length ≤ n} {v : TreeVertex d | n < v.1.length}
    hdisj F G hF hG
  have heq : (fun U : TreeVertex d → ℝ => F (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n := by
    funext U
    exact cutSpins_upper_extension theta n U
  change IndepFun (fun U => F (fun v : TreeBall d n => U v.1))
    (@cutLabels d n) (labelMeasure d) at h
  rw [heq] at h
  exact h

local instance localInst_r8629fa_2 (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem map_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    (labelMeasure d).map (fun U => (cutSpins theta n U, cutLabels U)) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))) := by
  rw [(indepFun_cutSpins_cutLabels d theta n).map_prod_eq_prod_map_map
    (measurable_cutSpins d theta n).aemeasurable (measurable_cutLabels d n).aemeasurable]
  congr 1
  exact infinitePi_map_disjoint_family (fun _ : TreeVertex d => uniform01)
    (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1})
    cutLevel_strictDescendants_disjoint

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyCutLevelIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance noisyCutLevelMeasurableSingletonIsingSpin_r8629fa_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
attribute [local instance] OAI.Problem367.RootedBroadcast.noisyCutLevelIsProbabilityLabelMeasure
theorem map_cutSpins_cutLabels_noises {d : ℕ} {A : Type*}
    [MeasurableSpace A] (theta : ℝ) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    ((labelMeasure d).prod (Measure.infinitePi ν)).map
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        (cutSpins theta n z.1, fun c : TreeShell d n =>
          (cutLabels z.1 c, fun v : DescendantVertex c.1 => z.2 v.1))) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
            (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ
  let N := (c : TreeShell d n) → DescendantVertex c.1 → A
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muR := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))
  let muN := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let f : (TreeVertex d → ℝ) → S × R := fun U => (cutSpins theta n U, cutLabels U)
  let g : (TreeVertex d → A) → N := fun W _ v => W v.1
  let p : R × N → ((c : TreeShell d n) →
      (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)) :=
    fun z c => (z.1 c, z.2 c)
  have hf : MeasurePreserving f (labelMeasure d) (rho.prod muR) :=
    ⟨(measurable_cutSpins d theta n).prodMk (measurable_cutLabels d n),
      map_cutSpins_cutLabels d theta n⟩
  have hg : MeasurePreserving g (Measure.infinitePi ν) muN := by
    refine ⟨by fun_prop, ?_⟩
    exact infinitePi_map_disjoint_family ν
      (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1})
      cutLevel_descendants_disjoint
  have hp : MeasurePreserving p (muR.prod muN) muP :=
    ⟨by fun_prop, infinitePi_map_pair_dependent_arrays
      (fun c : TreeShell d n => Measure.infinitePi
        (fun _ : StrictDescendantVertex c.1 => uniform01))
      (fun c : TreeShell d n => Measure.infinitePi
        (fun v : DescendantVertex c.1 => ν v.1))⟩
  have h := ((MeasurePreserving.id rho).prod hp).comp
    ((measurePreserving_prodAssoc rho muR muN).comp (hf.prod hg))
  exact h.map_eq

theorem iCondIndepFun_noisy_factor_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) => cutSpins theta n z.1))
      ((measurable_cutSpins d theta n).comp measurable_fst).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1))
      ((labelMeasure d).prod (Measure.infinitePi ν)) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) →
    (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muP) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop),
      map_cutSpins_cutLabels_noises theta n ν⟩
  let F := fun (c : TreeShell d n)
      (p : S × ((StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A))) =>
    (coneFactor theta c.1 (p.1 c, p.2.1), p.2.2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_coneFactor theta c.1).comp
      (((measurable_pi_apply c).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hbase := iCondIndepFun_latent_infinitePi rho
    (fun c : TreeShell d n =>
      (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
        (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))) F hF
  have hpull := iCondIndepFun_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν)) (rho.prod muP) e he
    ((inferInstance : MeasurableSpace S).comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun p : S × R => F c (p.1, p.2 c)) from
      (hF c).comp (measurable_fst.prodMk
        ((measurable_pi_apply c).comp measurable_snd))) hbase
  have hfun : (fun c => (fun p : S × R => F c (p.1, p.2 c)) ∘ e) =
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1)) := by
    funext c z
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at hpull
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

end Problem367.RootedBroadcast

namespace Problem367

local instance noisyCutLevelFreeIsingMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_iCondIndepFun_noisy_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  apply iCondIndepFun_of_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν))
    (Prod.map (RootedBroadcast.factor theta) id) he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1))
    (by fun_prop : Measurable
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1)).comap_le
    (fun _ => by fun_prop)
  simp only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map_fst, Prod.map_snd,
    id_eq]
  exact RootedBroadcast.iCondIndepFun_noisy_factor_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_cutLevel {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_cutLevel_observables {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) :=
  (hμ.iCondIndepFun_noisy_cutLevel h0 h1 n ν).comp F hF

theorem HasFreeIsingLaw.iIndepFun_cutLevel_observables_cond {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    iIndepFun
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}] := by
  exact iIndepFun_cond_fiber_of_iCondIndepFun
    (by fun_prop) (fun c => (hF c).comp (by fun_prop))
    (hμ.iCondIndepFun_cutLevel_observables h0 h1 n ν F hF) s hs

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CutLevelConditionalMean
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.appendCutContinuation_prefix_suffix _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_avoidingTreeCut _root_.OAI.Problem367.card_restrictedTreeCut _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_cutDescendants _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.RootedBroadcast

local instance cutLevelConditionalMeanIsProbabilityLabelMeasure (d : ℕ) :
    IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

local instance cutLevelConditionalMeanMeasurableSingletonIsingSpin_r8629fa_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem cutSpins_coordinate_fair {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) (c : TreeShell d n) (a : IsingSpin) :
    ((labelMeasure d).map (cutSpins theta n)) {s | s c = a} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (measurable_cutSpins d theta n)
    (measurableSet_eq_fun (measurable_pi_apply c) measurable_const)]
  have h := (freeIsingMeasure_hasFreeIsingLaw d h0 h1).marginal c.1 a
  rw [freeIsingMeasure, Measure.map_apply (measurable_factor d theta)
    (measurableSet_eq_fun (measurable_pi_apply c.1) measurable_const)] at h
  change (labelMeasure d) {U | factor theta U c.1 = a} = _
  change (labelMeasure d) {U | factor theta U c.1 = a} = _ at h
  simpa using h

theorem condExp_noisy_factor_cone_le_two_integral {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (DescendantVertex c.1 → IsingSpin) × (DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(labelMeasure d).prod (Measure.infinitePi ν),
      (((labelMeasure d).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
          F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => cutSpins theta n z.1)]) z ≤
      2 * ∫ w : (TreeVertex d → ℝ) × (TreeVertex d → A),
        F ((fun v => factor theta w.1 v.1), fun v => w.2 v.1)
          ∂(labelMeasure d).prod (Measure.infinitePi ν) := by
  let S := TreeShell d n → IsingSpin
  let R := (e : TreeShell d n) →
    (StrictDescendantVertex e.1 → ℝ) × (DescendantVertex e.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  haveI : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map (measurable_cutSpins d theta n).aemeasurable
  let muR := Measure.infinitePi (fun e : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex e.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex e.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muR) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop), map_cutSpins_cutLabels_noises theta n ν⟩
  let G : IsingSpin × R → ℝ := fun p =>
    F (coneFactor theta c.1 (p.1, (p.2 c).1), (p.2 c).2)
  have hG : Measurable G :=
    hF.comp (((measurable_coneFactor theta c.1).comp
      (measurable_fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply c).comp measurable_snd)))).prodMk
      (measurable_snd.comp ((measurable_pi_apply c).comp measurable_snd)))
  have h := condExp_binary_channel_comp_le_two_integral
    ((labelMeasure d).prod (Measure.infinitePi ν)) rho muR e he
    (fun s : S => s c) (measurable_pi_apply c)
    (cutSpins_coordinate_fair h0 h1 n c) G hG (fun p => hbound _)
  have hfun : (fun z => G ((e z).1 c, (e z).2)) =
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) := by
    funext z
    apply congrArg F
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at h
  exact h

end Problem367.RootedBroadcast

namespace Problem367

local instance cutLevelConditionalMeanFreeIsingMeasurableSingletonIsingSpin_r8629fa_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν),
      (((freeIsingMeasure d theta).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1)
          ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let P := (freeIsingMeasure d theta).prod (Measure.infinitePi ν)
  let Q := (labelMeasure d).prod (Measure.infinitePi ν)
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    Prod.map (RootedBroadcast.factor theta) id
  let H : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → ℝ :=
    fun z => F ((fun v => z.1 v.1), fun v => z.2 v.1)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) →
      TreeShell d n → IsingSpin := fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hH : Measurable H := hF.comp (by fun_prop)
  have hInt : Integrable H P := by
    apply Integrable.of_bound hH.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
      exact (hbound _).2)
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he : MeasurePreserving e Q P := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  have hpull := condExp_comp_measurePreserving Q P e he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap S)
    hS.comap_le hInt
  have hMean : (∫ x, H (e x) ∂Q) = ∫ z, H z ∂P := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable hH.aestronglyMeasurable).symm
  have hsource := RootedBroadcast.condExp_noisy_factor_cone_le_two_integral
    h0 h1 n ν c F hF hbound
  change ∀ᵐ z ∂P, (P[H | MeasurableSpace.comap S inferInstance]) z ≤
    2 * ∫ w, H w ∂P
  have hgoal : ∀ᵐ z ∂Q.map e,
      (P[H | MeasurableSpace.comap S inferInstance]) z ≤ 2 * ∫ w, H w ∂P := by
    apply (ae_map_iff he.measurable.aemeasurable
      (measurableSet_le (stronglyMeasurable_condExp.mono hS.comap_le).measurable
        measurable_const)).mpr
    filter_upwards [hpull, hsource] with z hz hzbound
    have hmeanbound : (Q[H ∘ e | (MeasurableSpace.comap S inferInstance).comap e]) z ≤
        2 * ∫ x, H (e x) ∂Q := by
      simp only [MeasurableSpace.comap_comp, Function.comp_def, S, H, e,
        Prod.map_fst, Prod.map_snd, id_eq]
      exact hzbound
    rw [hz, hMean] at hmeanbound
    exact hmeanbound
  simpa only [he.map_eq] using hgoal

theorem HasFreeIsingLaw.condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂μ.prod (Measure.infinitePi ν),
      ((μ.prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1) ∂μ.prod (Measure.infinitePi ν) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_condExp_cutLevel_observable_le_two_integral h0 h1 n ν c F hF hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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

end Problem367.PlantedInformation

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BoundedAverageConcentration
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
namespace BoundedAverageConcentration

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measureReal_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ.real {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      Real.exp (-(s.card : ℝ) * τ ^ 2 / 2) := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hcenter : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ := by
    exact h_indep.comp (fun i x => x - ∫ ω, X i ω ∂μ)
      (fun _ => measurable_id.sub_const _)
  have hsub : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (1 / 4 : ℝ≥0) μ := by
    intro i hi
    convert hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bdd i hi) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hsum_mean : (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ (s.card : ℝ) * τ / 2 := by
    calc
      (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ ∑ _i ∈ s, τ / 2 :=
        Finset.sum_le_sum h_mean
      _ = (s.card : ℝ) * τ / 2 := by simp [mul_div_assoc]
  have hsubset : {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ⊆
      {ω | (s.card : ℝ) * τ / 2 ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} := by
    intro ω hω
    have hw : τ * (s.card : ℝ) ≤ ∑ i ∈ s, X i ω :=
      (le_div_iff₀ hcard).mp hω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
    nlinarith
  have hhoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenter hsub
    (show 0 ≤ (s.card : ℝ) * τ / 2 by positivity)
  have hexp :
      -((s.card : ℝ) * τ / 2) ^ 2 /
          (2 * ((∑ _i ∈ s, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ)) =
        -(s.card : ℝ) * τ ^ 2 / 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast
    field_simp [ne_of_gt hcard]
    ring
  exact (measureReal_mono hsubset).trans (hexp ▸ hhoeff)

theorem measure_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_average_ge_le h_indep s hs hτ h_meas h_bdd h_mean)

theorem exponential_card_bound
    {N b ℓ q : ℝ} (hb : 0 < b) (hℓ : 0 ≤ ℓ)
    (hq : q ≤ Real.log b / 8)
    (hN : b ^ (ℓ / 2 - 1) ≤ N) :
    Real.exp (-N * (Real.exp (-q * ℓ)) ^ 2 / 2) ≤
      Real.exp (-(b ^ (ℓ / 4)) / (2 * b)) := by
  have hpow : 0 < b ^ (ℓ / 2 - 1) := Real.rpow_pos_of_pos hb _
  have hexp : Real.exp (-(Real.log b) * ℓ / 4) ≤ (Real.exp (-q * ℓ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hq hℓ]
  have hprod : b ^ (ℓ / 4) / b ≤ N * (Real.exp (-q * ℓ)) ^ 2 := by
    calc
      b ^ (ℓ / 4) / b =
          b ^ (ℓ / 2 - 1) * Real.exp (-(Real.log b) * ℓ / 4) := by
        rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb,
          ← Real.exp_log hb, ← Real.exp_sub, ← Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        ring
      _ ≤ N * (Real.exp (-q * ℓ)) ^ 2 :=
        mul_le_mul hN hexp (Real.exp_pos _).le (hpow.le.trans hN)
  apply Real.exp_le_exp.mpr
  have := div_le_div_of_nonneg_right hprod (show (0 : ℝ) ≤ 2 by norm_num)
  simpa [div_div, neg_div, mul_comm] using neg_le_neg this

end BoundedAverageConcentration
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentGeometry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.prefix_mem_of_root_mem {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) {u v : TreeVertex d}
    (hv : v ∈ D) (huv : u.1 <+: v.1) : u ∈ D :=
  hD.prefix_mem_of_min_length_le hroot (fun _ _ => Nat.zero_le _) hv huv (Nat.zero_le _)

theorem ConnectedFinset.filter_prefix_connected {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) (r : TreeVertex d) (hr : r ∈ D) :
    ConnectedFinset (D.filter (fun v => r.1 <+: v.1)) := by
  classical
  let E := D.filter (fun v => r.1 <+: v.1)
  have hrE : r ∈ E := Finset.mem_filter.mpr ⟨hr, List.prefix_refl _⟩
  let R := fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y
  have paths : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ E →
      Relation.ReflTransGen R r v ∧ Relation.ReflTransGen R v r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv
      by_cases heq : v = r
      · subst v
        exact ⟨.refl, .refl⟩
      have hv' := Finset.mem_filter.mp hv
      have hnil : v.1 ≠ [] := by
        intro he
        have hre : r.1 = [] := by
          have hlen : r.1.length ≤ 0 := by simpa only [he, List.length_nil] using hv'.2.length_le
          exact List.length_eq_zero_iff.mp (by omega)
        exact heq (Subtype.ext (he.trans hre.symm))
      have hadj := treeAdj_parentVertex hnil
      have hpD : parentVertex v ∈ D :=
        hD.prefix_mem_of_root_mem hroot hv'.1 (List.dropLast_prefix v.1)
      have hpE : parentVertex v ∈ E := Finset.mem_filter.mpr
        ⟨hpD, treeAdj_preserves_prefix hv'.2 hadj.symm heq⟩
      have hlt : (parentVertex v).1.length < n := by
        have hpos := List.length_pos_iff.mpr hnil
        rw [parentVertex_length]
        omega
      obtain ⟨hforward, hbackward⟩ := ih _ hlt _ rfl hpE
      exact ⟨hforward.trans (.single ⟨hpE, hv, hadj⟩),
        (Relation.ReflTransGen.single ⟨hv, hpE, hadj.symm⟩).trans hbackward⟩
  refine ⟨⟨r, hrE⟩, ?_⟩
  intro u hu v hv
  exact (paths _ u rfl hu).2.trans (paths _ v rfl hv).1

theorem rootComponentFinset_connected {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    ConnectedFinset (rootComponentFinset D c) :=
  hD.filter_prefix_connected hroot ⟨[c], List.IsChain.singleton c⟩ hc

theorem rootComponentFinset_union_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : rootComponentFinset D c ∪ rootComplementFinset D c = D := by
  classical
  ext v
  simp only [Finset.mem_union, mem_rootComponentFinset, mem_rootComplementFinset]
  tauto

theorem rootComponentFinset_disjoint_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : Disjoint (rootComponentFinset D c) (rootComplementFinset D c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (mem_rootComplementFinset.mp hw).2 (mem_rootComponentFinset.mp hv).2

theorem root_component_crossing_edge {d : ℕ} {c : Fin d} {u v : TreeVertex d}
    (hu : [c] <+: u.1) (hv : ¬ [c] <+: v.1) (hadj : treeAdj u v) :
    u = ⟨[c], List.IsChain.singleton c⟩ ∧ v = ConnectedHull.root d := by
  have hueq : u = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := by
    by_contra hne
    exact hv (treeAdj_preserves_prefix (r := ⟨[c], List.IsChain.singleton c⟩) hu hadj hne)
  refine ⟨hueq, ?_⟩
  subst u
  rcases hadj with ⟨a, ha⟩ | ⟨a, ha⟩
  · exfalso
    apply hv
    rw [ha]
    exact List.prefix_append _ _
  · apply Subtype.ext
    change v.1 = []
    have hlen := congrArg List.length ha
    simp only [List.length_singleton, List.length_append] at hlen
    exact List.length_eq_zero_iff.mp (by omega)

theorem singleton_prefix_iff_cons {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    [c] <+: v.1 ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩

private theorem mem_inducedEdges_cut {d : ℕ} {D : Finset (TreeVertex d)}
    {u v : TreeVertex d} : (u, v) ∈ inducedEdges D ↔
      u ∈ D ∧ v ∈ D ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  simp [inducedEdges, and_assoc]

theorem inducedEdges_rootComponent_split {d : ℕ} {D : Finset (TreeVertex d)}
    (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    inducedEdges D = insert (ConnectedHull.root d, ⟨[c], List.IsChain.singleton c⟩)
      (inducedEdges (rootComponentFinset D c) ∪ inducedEdges (rootComplementFinset D c)) := by
  classical
  ext ⟨u, v⟩
  constructor
  · intro he
    obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
    by_cases hcu : [c] <+: u.1
    · by_cases hcv : [c] <+: v.1
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inl (mem_inducedEdges_cut.mpr
          ⟨mem_rootComponentFinset.mpr ⟨hu, hcu⟩,
            mem_rootComponentFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcu hcv hadj
        change 1 < 0 at hlen
        omega
    · by_cases hcv : [c] <+: v.1
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcv hcu hadj.symm
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inr (mem_inducedEdges_cut.mpr
          ⟨mem_rootComplementFinset.mpr ⟨hu, hcu⟩,
            mem_rootComplementFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
  · intro he
    rcases Finset.mem_insert.mp he with heq | he
    · have hu : u = ConnectedHull.root d := congrArg Prod.fst heq
      have hv : v = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := congrArg Prod.snd heq
      subst u
      subst v
      exact mem_inducedEdges_cut.mpr ⟨hroot, hc, Or.inl ⟨c, rfl⟩, by change 0 < 1; omega⟩
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComponentFinset.mp hu).1,
          (mem_rootComponentFinset.mp hv).1, hadj, hlen⟩
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComplementFinset.mp hu).1,
          (mem_rootComplementFinset.mp hv).1, hadj, hlen⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteSpinCoupling
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteSpinCoupling

variable {A B : Type*} [Fintype A] [Fintype B]

lemma mean_eq (E : A → ℝ) (a : A → IsingSpin) :
    mean E a = numerator E a / partition E := by
  simp [mean, numerator, partition, FinitePosterior.mean,
    FinitePosterior.partition, FinitePosterior.weight]

lemma partition_pos [Nonempty A] (E : A → ℝ) : 0 < partition E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype A] [Fintype B] in
lemma exp_interaction (beta : ℝ) (a b : IsingSpin) :
    Real.exp (beta * spinSign a * spinSign b) =
      Real.cosh beta + Real.sinh beta * spinSign a * spinSign b := by
  cases a <;> cases b <;>
    simp [spinSign, ← sub_eq_add_neg, Real.cosh_add_sinh, Real.cosh_sub_sinh]

omit [Fintype A] [Fintype B] in
lemma exp_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) (x : A × B) :
    Real.exp (energy beta EA EB a b x) =
      Real.cosh beta * Real.exp (EA x.1) * Real.exp (EB x.2) +
      Real.sinh beta * (spinSign (a x.1) * Real.exp (EA x.1)) *
        (spinSign (b x.2) * Real.exp (EB x.2)) := by
  rw [energy, Real.exp_add, Real.exp_add, exp_interaction]
  ring

theorem partition_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    partition (energy beta EA EB a b) =
      Real.cosh beta * partition EA * partition EB +
      Real.sinh beta * numerator EA a * numerator EB b := by
  simp only [partition, Fintype.sum_prod_type, exp_energy,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, numerator]

theorem numerator_energy_fst (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    numerator (energy beta EA EB a b) (fun x => a x.1) =
      Real.cosh beta * numerator EA a * partition EB +
      Real.sinh beta * partition EA * numerator EB b := by
  have heq (x : A × B) :
      spinSign (a x.1) * Real.exp (energy beta EA EB a b x) =
        Real.cosh beta * (spinSign (a x.1) * Real.exp (EA x.1)) * Real.exp (EB x.2) +
        Real.sinh beta * Real.exp (EA x.1) *
          (spinSign (b x.2) * Real.exp (EB x.2)) := by
    rw [exp_energy]
    cases a x.1 <;> simp only [spinSign_neg, spinSign_pos] <;> ring
  simp only [numerator, Fintype.sum_prod_type, heq,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, partition]

theorem mean_energy_fst [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => a x.1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  rw [mean_eq, numerator_energy_fst, partition_energy, mean_eq, mean_eq]
  rw [Real.tanh_eq_sinh_div_cosh]
  have hA := (partition_pos EA).ne'
  have hB := (partition_pos EB).ne'
  have hC := (Real.cosh_pos beta).ne'
  field_simp

theorem mean_equiv {S : Type*} [Fintype S] (e : S ≃ A)
    (E : A → ℝ) (a : A → IsingSpin) :
    mean (E ∘ e) (a ∘ e) = mean E a := by
  simp only [mean_eq, numerator, partition, Function.comp_apply]
  rw [e.sum_comp (fun x => spinSign (a x) * Real.exp (E x)),
    e.sum_comp (fun x => Real.exp (E x))]

theorem mean_energy_snd [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => b x.2) =
      (mean EB b + Real.tanh beta * mean EA a) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : energy beta EA EB a b =
      energy beta EB EA b a ∘ Equiv.prodComm A B := by
    funext x
    simp only [energy, Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [he]
  change mean (energy beta EB EA b a ∘ Equiv.prodComm A B)
    ((fun x : B × A => b x.1) ∘ Equiv.prodComm A B) = _
  rw [mean_equiv, mean_energy_fst]
  congr 1; ring

theorem mean_of_energy_split {S : Type*} [Fintype S]
    [Nonempty A] [Nonempty B] (e : S ≃ A × B)
    (E : S → ℝ) (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin)
    (hE : ∀ x, E x = energy beta EA EB a b (e x)) :
    mean E (fun x => a (e x).1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : E = energy beta EA EB a b ∘ e := funext hE
  rw [he]
  change mean (energy beta EA EB a b ∘ e) ((fun x : A × B => a x.1) ∘ e) = _
  rw [mean_equiv, mean_energy_fst]

end Problem367.FiniteSpinCoupling

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingSplit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteIsingSplit

variable {V : Type*} [DecidableEq V]

variable {d : ℕ}

lemma inducedEdges_endpoints {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    e.1 ∈ D ∧ e.2 ∈ D := by
  classical
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1

lemma observedEnergy_restrict (beta : ℝ) (D : Finset (TreeVertex d))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta D y (D.restrict eta) =
      beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2) +
        ∑ v ∈ D, y v * spinSign (eta v) := by
  classical
  unfold observedEnergy FinitePosterior.fieldEnergy finiteIsingEnergy
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have he' := inducedEdges_endpoints he
    simp [extendFiniteSpin, he'.1, he'.2]
  · exact Finset.sum_coe_sort D (fun v => y v * spinSign (eta v))

theorem observedEnergy_split_restrict (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta (A ∪ B) y ((A ∪ B).restrict eta) =
      observedEnergy beta A y (A.restrict eta) +
      observedEnergy beta B y (B.restrict eta) +
        beta * spinSign (eta u) * spinSign (eta v) := by
  classical
  have hdis : Disjoint (inducedEdges A) (inducedEdges B) := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact Finset.disjoint_left.mp hAB
      (inducedEdges_endpoints heA).1 (inducedEdges_endpoints heB).1
  have hnot : (u.1, v.1) ∉ inducedEdges A ∪ inducedEdges B := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.disjoint_left.mp hAB (inducedEdges_endpoints he).2 v.property
    · exact Finset.disjoint_left.mp hAB u.property (inducedEdges_endpoints he).1
  rw [observedEnergy_restrict, observedEnergy_restrict, observedEnergy_restrict,
    hEdges, Finset.sum_insert hnot, Finset.sum_union hdis, Finset.sum_union hAB]
  ring

theorem observedEnergy_split (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : ↥(A ∪ B) → IsingSpin) :
    observedEnergy beta (A ∪ B) y eta =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) (splitEquiv A B hAB eta) := by
  classical
  let sigma := extendFiniteSpin (A ∪ B) eta
  have hU : (A ∪ B).restrict sigma = eta := restrict_extendFiniteSpin _ _
  have hA : A.restrict sigma = (splitEquiv A B hAB eta).1 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_left B w.property⟩
  have hB : B.restrict sigma = (splitEquiv A B hAB eta).2 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_right A w.property⟩
  have hu : sigma u = (splitEquiv A B hAB eta).1 u := congrFun hA u
  have hv : sigma v = (splitEquiv A B hAB eta).2 v := congrFun hB v
  have h := observedEnergy_split_restrict beta A B hAB u v hEdges y sigma
  simpa only [hU, hA, hB, hu, hv, FiniteSpinCoupling.energy] using h

lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) :
    mean beta D v y = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) (D.restrict y) := by
  simp only [mean, FiniteSpinCoupling.mean_eq, FiniteSpinCoupling.numerator,
    FiniteSpinCoupling.partition, observedEnergy, FinitePosterior.fieldMean]

theorem mean_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      (mean beta A u y + Real.tanh beta * mean beta B v y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  exact FiniteSpinCoupling.mean_of_energy_split (splitEquiv A B hAB)
    (observedEnergy beta (A ∪ B) y) beta (observedEnergy beta A y)
    (observedEnergy beta B y) (fun s => s u) (fun s => s v)
    (observedEnergy_split beta A B hAB u v hEdges y)

theorem mean_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      (mean beta B v y + Real.tanh beta * mean beta A u y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  have hE : observedEnergy beta (A ∪ B) y =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) ∘ splitEquiv A B hAB :=
    funext (observedEnergy_split beta A B hAB u v hEdges y)
  unfold mean
  rw [hE]
  change FiniteSpinCoupling.mean (_ ∘ splitEquiv A B hAB)
    ((fun s : (A → IsingSpin) × (B → IsingSpin) => s.2 v) ∘ splitEquiv A B hAB) = _
  rw [FiniteSpinCoupling.mean_equiv, FiniteSpinCoupling.mean_energy_snd]

lemma mean_mem_Ioo (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : mean beta D v y ∈ Set.Ioo (-1 : ℝ) 1 := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    change spinSign (eta v) = -1 ∨ spinSign (eta v) = 1
    cases eta v <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

theorem field_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      field beta A u y + cavityMessage (Real.tanh beta) (field beta B v y) := by
  unfold field
  rw [mean_union_fst beta A B hAB u v hEdges y]
  exact artanh_binaryFusion_scaled_of_mem ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta A u y) (mean_mem_Ioo beta B v y)

theorem field_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      field beta B v y + cavityMessage (Real.tanh beta) (field beta A u y) := by
  unfold field
  rw [mean_union_snd beta A B hAB u v hEdges y]
  rw [show 1 + Real.tanh beta * mean beta A u y * mean beta B v y =
      1 + Real.tanh beta * mean beta B v y * mean beta A u y by ring]
  exact artanh_binaryFusion_scaled_of_mem
    ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta B v y) (mean_mem_Ioo beta A u y)

theorem cavityFromSites_eq_component_fields {beta : ℝ} (hbeta : 0 ≤ beta)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y,
        field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y) =
      (field beta A u y, field beta B v y) := by
  apply cavityFromSites_eq
  exact ⟨(field_union_fst beta A B hAB u v hEdges y).symm,
    (field_union_snd beta A B hAB u v hEdges y).symm⟩

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem mem_range_componentIndexVertex {d : ℕ} {c : Fin d} {v : TreeVertex d} :
    v ∈ Set.range (componentIndexVertex (c := c)) ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, hw⟩
    have hchain : (c :: w).IsChain (fun a b : Fin d => a ≠ b) := by
      rw [← hw]
      exact v.2
    refine ⟨⟨w.length, ⟨w, rfl, hchain⟩⟩, ?_⟩
    exact Subtype.ext hw.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem condExp_tanh_bounds_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₁]) ω ∧
      (μ[f | m₁]) ω ≤ Real.tanh (X ω + K) := by
  have h₁ : m₁ ≤ m := h₁₂.trans h₂
  have hL : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω - K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.sub stronglyMeasurable_const)
  have hU : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω + K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.add stronglyMeasurable_const)
  have iL : Integrable (fun ω => Real.tanh (X ω - K)) μ := by
    apply Integrable.of_bound (hL.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω - K)).le
  have iU : Integrable (fun ω => Real.tanh (X ω + K)) μ := by
    apply Integrable.of_bound (hU.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω + K)).le
  have hlo := condExp_mono (m := m₁) iL integrable_condExp
    (hb.mono fun ω hω => hω.1)
  have hhi := condExp_mono (m := m₁) integrable_condExp iU
    (hb.mono fun ω hω => hω.2)
  rw [condExp_of_stronglyMeasurable h₁ hL iL] at hlo
  rw [condExp_of_stronglyMeasurable h₁ hU iU] at hhi
  filter_upwards [hlo, hhi, condExp_condExp_of_le (f := f) h₁₂ h₂] with ω hLω hUω hTω
  rw [hTω] at hLω hUω
  exact ⟨hLω, hUω⟩

theorem condExp_field_bound_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, (μ[f | m₂]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₂]) ω) - X ω| ≤ K) :
    ∀ᵐ ω ∂μ, (μ[f | m₁]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₁]) ω) - X ω| ≤ K := by
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hs : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K) := by
    filter_upwards [hb] with ω hω
    have hlo := hmono (show X ω - K ≤ Real.artanh ((μ[f | m₂]) ω) by
      linarith [(abs_le.mp hω.2).1])
    have hhi := hmono (show Real.artanh ((μ[f | m₂]) ω) ≤ X ω + K by
      linarith [(abs_le.mp hω.2).2])
    rw [Real.tanh_artanh hω.1] at hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [condExp_tanh_bounds_of_le (m := m) μ h₁₂ h₂ hX hs] with ω hω
  have h := posterior_field_limit_of_tanh_bounds
    (u := fun _ : ℕ => (μ[f | m₁]) ω) tendsto_const_nhds (fun _ => hω)
  exact ⟨h.1, h.2.1⟩

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_bound
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) :
    ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p) -
          PlantedSymmetry.observation t p r| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hsub : selectedObservationField F v ≤
      PlantedSymmetry.observationSigma (TreeVertex d) t := by
    change selectedObservationField F v ≤ selectedObservationField F id
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => PlantedSymmetry.observation t p r) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply i).comp (comap_measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun j => F (p.1 (v j)) (p.2 (v j))))).stronglyMeasurable
  exact condExp_field_bound_of_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hsub
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t) hX
    (hμ.gaussian_posterior_field_bound hβ t r)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorLimit
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

theorem selectedObservationExhaustion_iSup {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (D : ℕ → Finset ι) (hD : Monotone D)
    (hex : ∀ i, ∃ n, i ∈ D n) :
    (⨆ n, selectedObservationExhaustion F hF v D hD n) =
      selectedObservationField F v := by
  change (⨆ n, selectedObservationField F (fun i : D n => v i.1)) = _
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup_of_le i.1 le_rfl
  · apply iSup_le
    intro i
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le (⟨i, hn⟩ : D n) le_rfl)

private theorem tanh_bounds_of_interior_field_bound {z x K : ℝ}
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) (h : |Real.artanh z - x| ≤ K) :
    Real.tanh (x - K) ≤ z ∧ z ≤ Real.tanh (x + K) := by
  constructor
  · apply (Real.artanh_le_artanh_iff
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hz).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).1]
  · apply (Real.artanh_le_artanh_iff hz
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).2]

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_limit
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (D : ℕ → Finset ι) (hD : Monotone D) (hex : ∀ i, ∃ n, i ∈ D n)
    (hr : ∀ n, r ∈ Set.range (fun i : D n => v i.1)) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (∀ᵐ p ∂ρ, Tendsto
      (fun n => Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p))
      atTop (𝓝 (Real.artanh (selectedPosterior ρ F v r p)))) ∧
    Tendsto (fun n => ∫ p,
      (Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p) -
        Real.artanh (selectedPosterior ρ F v r p)) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  let ℱ := selectedObservationExhaustion F hF v D hD
  have hsup : (⨆ n, ℱ n) = selectedObservationField F v :=
    selectedObservationExhaustion_iSup F hF v D hD hex
  have hb (n : ℕ) : ∀ᵐ p ∂ρ,
      Real.tanh (PlantedSymmetry.observation t p r - (d : ℝ) * β) ≤
        (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ∧
      (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ≤
        Real.tanh (PlantedSymmetry.observation t p r + (d : ℝ) * β) := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hβ t
      (fun i : D n => v i.1) r (hr n)] with p hp
    exact tanh_bounds_of_interior_field_bound hp.1 hp.2
  have hae := tendsto_posterior_fields_ae ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r)
    ((d : ℝ) * β) hb
  have hL2 := tendsto_integral_sq_sub_posterior_fields ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r) hb
  rw [hsup] at hae hL2
  exact ⟨hae.mono (fun p hp => hp.2.2), hL2⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentGibbsLimit
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

theorem rootComponentIndices_monotone {d : ℕ} (c : Fin d) :
    Monotone (fun D : Finset (TreeVertex d) => rootComponentIndices D c) := by
  intro D E hDE u hu
  exact mem_rootComponentIndices.mpr (hDE (mem_rootComponentIndices.mp hu))

theorem selectedObservationField_rootComponentIndices {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (D : Finset (TreeVertex d)) (c : Fin d) :
    selectedObservationField F (fun u : rootComponentIndices D c => componentIndexVertex u.1) =
      selectedObservationField F (fun v : rootComponentFinset D c => v.1) := by
  apply selectedObservationField_eq_of_range_eq
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨componentIndexVertex u.1, mem_rootComponentFinset.mpr
      ⟨mem_rootComponentIndices.mp u.2, ?_⟩⟩, rfl⟩
    apply (singleton_prefix_iff_cons c _).mpr
    exact ⟨u.1.2.1, rfl⟩
  · rintro ⟨v, rfl⟩
    have hv := mem_rootComponentFinset.mp v.2
    obtain ⟨u, hu⟩ := mem_range_componentIndexVertex.mpr
      ((singleton_prefix_iff_cons c v.1).mp hv.2)
    refine ⟨⟨u, mem_rootComponentIndices.mpr ?_⟩, hu⟩
    exact hu.symm ▸ hv.1

theorem HasFreeIsingLaw.rootComponent_gibbsMean_eq_selectedPosterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) (t : ℝ≥0) :
    (fun p => FiniteIsingSplit.mean β (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
      (PlantedSymmetry.observation t p)) =ᵐ[μ.prod
        (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)]
    selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z)
      (fun u : rootComponentIndices D c => componentIndexVertex u.1)
      ⟨[c], List.IsChain.singleton c⟩ := by
  let E := rootComponentFinset D c
  let r : E := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hce := hμ.finiteObservation_condExp E
    (rootComponentFinset_connected hD hroot c hc) t (fun eta => spinSign (eta r))
  simp only [selectedPosterior, selectedObservationField_rootComponentIndices]
  have hsigma : selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
      (fun v : E => v.1) = MeasurableSpace.comap (finiteObservation E t) inferInstance := rfl
  rw [hsigma]
  simp only [FiniteIsingSplit.mean_eq_fieldMean]
  convert hce.symm using 1 <;> rfl

theorem HasFreeIsingLaw.rootComponent_gibbsField_limit
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hmono : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let H : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
      fun n p => Real.artanh (FiniteIsingSplit.mean β (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (PlantedSymmetry.observation t p))
    let Z := fun p => Real.artanh (selectedPosterior ρ
      (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p)
    (∀ᵐ p ∂ρ, Tendsto (fun n => H n p) atTop (𝓝 (Z p))) ∧
      Tendsto (fun n => ∫ p, (H n p - Z p) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  let I := fun n => rootComponentIndices (D n) c
  have hI : Monotone I := fun _ _ hnm => rootComponentIndices_monotone c (hmono hnm)
  have hexI : ∀ u : ComponentIndex c, ∃ n, u ∈ I n := by
    intro u
    obtain ⟨n, hn⟩ := hex (componentIndexVertex u)
    exact ⟨n, mem_rootComponentIndices.mpr hn⟩
  have hrI : ∀ n, r ∈ Set.range (fun u : I n => componentIndexVertex u.1) := by
    intro n
    let u : ComponentIndex c := ⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩
    exact ⟨⟨u, mem_rootComponentIndices.mpr (hc n)⟩, rfl⟩
  have hlim := hμ.selected_gaussian_posterior_field_limit hβ t
    (componentIndexVertex (c := c)) r I hI hexI hrI
  have hce (n : ℕ) := hμ.rootComponent_gibbsMean_eq_selectedPosterior
    (D n) (hconn n) (hroot n) c (hc n) t
  constructor
  · filter_upwards [hlim.1, ae_all_iff.mpr hce] with p hp hce
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact congrArg Real.artanh (hce n)
  · convert hlim.2 using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply integral_congr_ae
    filter_upwards [hce n] with p hp
    rw [hp]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentFields
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.FiniteIsingSplit

variable {d : ℕ}

lemma field_congr_domain (beta : ℝ) {D E : Finset (TreeVertex d)}
    (h : D = E) (v : D) (w : E) (hv : v.1 = w.1)
    (y : TreeVertex d → ℝ) : field beta D v y = field beta E w y := by
  subst E
  have hw : v = w := Subtype.ext hv
  subst w
  rfl

theorem cavityFromSites_root_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta D ⟨ConnectedHull.root d, hroot⟩ y,
        field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y) =
      (field beta (rootComplementFinset D c)
          ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩ y,
        field beta (rootComponentFinset D c)
          ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y) := by
  classical
  let A := rootComplementFinset D c
  let B := rootComponentFinset D c
  let u : A := ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩
  let v : B := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hAB : Disjoint A B := (rootComponentFinset_disjoint_complement D c).symm
  have hUnion : A ∪ B = D := by
    rw [Finset.union_comm]
    exact rootComponentFinset_union_complement D c
  have hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B) := by
    rw [hUnion, inducedEdges_rootComponent_split hroot c hc]
    congr 1
    exact Finset.union_comm _ _
  have h := cavityFromSites_eq_component_fields hbeta A B hAB u v hEdges y
  have hu := field_congr_domain beta hUnion
    (⟨u, Finset.mem_union_left B u.property⟩ : ↥(A ∪ B))
    ⟨ConnectedHull.root d, hroot⟩ rfl y
  have hv := field_congr_domain beta hUnion
    (⟨v, Finset.mem_union_right A v.property⟩ : ↥(A ∪ B))
    ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ rfl y
  rw [hu, hv] at h
  exact h

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteCavityComponents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.CavityFieldLimit

variable {d : ℕ}

lemma finiteSiteField_eq_component_field (beta : ℝ) (D : Finset (TreeVertex d))
    (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = FiniteIsingSplit.field beta D v y := by
  simp only [finiteSiteField, FiniteIsingSplit.field, FiniteIsingSplit.mean_eq_fieldMean]

theorem finiteCavityField_child_eq_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    finiteCavityField hbeta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩
      ⟨ConnectedHull.root d, hroot⟩ y =
    finiteSiteField beta (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y := by
  simp only [finiteCavityField, finiteSiteField_eq_component_field]
  have hswap := cavityFromSites_swap (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta)
    (FiniteIsingSplit.field beta D ⟨ConnectedHull.root d, hroot⟩ y,
      FiniteIsingSplit.field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y)
  rw [FiniteIsingSplit.cavityFromSites_root_component hbeta D hroot c hc y] at hswap
  exact congrArg Prod.fst hswap

end Problem367.CavityFieldLimit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteComponentCavity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open CavityFieldLimit PlantedSymmetry

theorem HasFreeIsingLaw.infiniteCavityField_eq_component_of_exhaustion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  have hfull := hμ.exhaustionCavityField_tendsto_ae hbeta D hD hconn hex
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d) hc hroot t
  have hpart := (hμ.rootComponent_gibbsField_limit hbeta t c D hD hconn hex hroot hc).1
  filter_upwards [hfull, hpart] with p hp hpart
  have hseq (n : ℕ) :
      finiteCavityField hbeta (D n) ⟨⟨[c], List.IsChain.singleton c⟩, hc n⟩
        ⟨ConnectedHull.root d, hroot n⟩ (observation t p) =
      Real.artanh (FiniteIsingSplit.mean beta (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (observation t p)) := by
    rw [finiteCavityField_child_eq_component hbeta (D n) (hroot n) c (hc n)]
    exact finiteSiteField_eq_component_field _ _ _ _
  exact tendsto_nhds_unique ((tendsto_congr hseq).mp hp) hpart

theorem HasFreeIsingLaw.infiniteCavityField_eq_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  apply hμ.infiniteCavityField_eq_component_of_exhaustion hbeta t c
    (connectedExhaustion r) (connectedExhaustion_monotone r)
    (connectedExhaustion_connected r)
    (fun v => (eventually_mem_connectedExhaustion r v).exists)
    _ (mem_connectedExhaustion r)
  intro n
  classical
  simp [connectedExhaustion, ConnectedHull.hull]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_InfiniteCavityNaturality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry CavityFieldLimit

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_gaussian_relabel
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (t : ℝ≥0)
    (g : TreeAut d) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteGibbsSpinMean β v (relabel g (observation t p)) =
      infiniteGibbsSpinMean β (g.toEquiv.symm v) (observation t p) := by
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  have hfield : selectedObservationField F (fun i => g.toEquiv.symm i) =
      selectedObservationField F id := by
    apply selectedObservationField_eq_of_range_eq
    simp only [Equiv.range_eq_univ, Set.range_id]
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hF id v g
  simp only [id_eq, selectedPosterior, hfield] at hpost
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ
    (gaussianReal 0 t) g
  have hleft := hmp.quasiMeasurePreserving.ae
    (hμ.infiniteGibbsSpinMean_eq_posterior t v)
  filter_upwards [hleft, hpost,
    hμ.infiniteGibbsSpinMean_eq_posterior t (g.toEquiv.symm v)] with p hl hp hr
  exact hl.trans (hp.trans hr.symm)

theorem HasFreeIsingLaw.infiniteCavityField_gaussian_relabel
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0)
    (g : TreeAut d) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ v w (relabel g (observation t p)) =
      infiniteCavityField hβ (g.toEquiv.symm v) (g.toEquiv.symm w)
        (observation t p) := by
  filter_upwards [hμ.infiniteGibbsSpinMean_gaussian_relabel t g v,
    hμ.infiniteGibbsSpinMean_gaussian_relabel t g w] with p hv hw
  simp only [infiniteCavityField, CavityArray.field, hv, hw]

theorem HasFreeIsingLaw.infiniteCavityField_eq_relabelled_component
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0)
    (g : TreeAut d) (c : Fin d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩)
        (g.toEquiv.symm (ConnectedHull.root d)) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i))
        (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩) p) := by
  have hs : Measurable spinSign := by intro s hs; trivial
  have hF : Measurable (Function.uncurry
      (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z)) :=
    ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ
    (gaussianReal 0 t) g
  have hroot := hmp.quasiMeasurePreserving.ae
    (hμ.infiniteCavityField_eq_component hβ t c)
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hF
    (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩ g
  filter_upwards [hroot, hpost, hμ.infiniteCavityField_gaussian_relabel hβ t g
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)] with p hr hp hn
  exact hn.symm.trans (hr.trans (congrArg Real.artanh hp))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem lossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < lossCoefficient theta :=
  lt_min (div_pos (sideSignalLossCoefficient_pos hθ0 hθ1) (by norm_num)) (by norm_num)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_selectedPosterior_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      ∀ p, selectedPosterior rho F v r p =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  have hm : Measurable[selectedObservationField F v]
      (selectedPosterior rho F v r) := stronglyMeasurable_condExp.measurable
  obtain ⟨g, hg, heq⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg, fun p => congrFun heq p⟩

theorem exists_selectedAttenuation_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta (Real.artanh (selectedPosterior rho F v r p)) ^ 2 =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  obtain ⟨f, hf, heq⟩ := exists_selectedPosterior_channel rho F v r
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hat : Measurable (responseAttenuation theta) := by
    unfold responseAttenuation
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  refine ⟨fun x => responseAttenuation theta (Real.artanh (f x)) ^ 2,
    ((hat.comp (ha.comp hf)).pow_const 2),
    ?_, ?_⟩
  · intro x
    refine ⟨sq_nonneg _, ?_⟩
    have hpos := responseAttenuation_pos hθ (Real.artanh (f x))
    have hone := responseAttenuation_le_one hθ (Real.artanh (f x))
    nlinarith
  · intro p
    rw [heq p]

theorem exists_selectedAttenuation_local_channel
    {d : ℕ} {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : κ → TreeVertex d) (j : ι → κ) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : ((κ → IsingSpin) × (κ → A)) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta
          (Real.artanh (selectedPosterior rho F (v ∘ j) r p)) ^ 2 =
        g (fun k => p.1 (v k), fun k => p.2 (v k)) := by
  obtain ⟨f, hf, hbound, heq⟩ := exists_selectedAttenuation_channel rho F (v ∘ j) r hθ
  let obs : ((κ → IsingSpin) × (κ → A)) → (ι → B) :=
    fun x i => F (x.1 (j i)) (x.2 (j i))
  have hobs : Measurable obs := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun x : (κ → IsingSpin) × (κ → A) =>
      (x.1 (j i), x.2 (j i))) by fun_prop)
  refine ⟨f ∘ obs, hf.comp hobs, fun x => hbound (obs x), ?_⟩
  intro p
  exact heq p

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RestrictedCutCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem pow_le_card_avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d))
    (hF : forbidden.card ≤ 1) (k : ℕ) :
    (d - 1) ^ (k + 1) ≤ (avoidingTreeCut forbidden k).card := by
  rw [card_avoidingTreeCut, pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

theorem avoidingTreeCut_nonempty {d : ℕ} (hd : 2 ≤ d)
    (forbidden : Finset (Fin d)) (hF : forbidden.card ≤ 1) (k : ℕ) :
    (avoidingTreeCut forbidden k).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le (pow_pos (by omega : 0 < d - 1) _)
    (pow_le_card_avoidingTreeCut forbidden hF k)

theorem rpow_le_card_avoidingTreeCut {d : ℕ} (hd : 2 ≤ d)
    (forbidden : Finset (Fin d)) (hF : forbidden.card ≤ 1) (k : ℕ)
    {ℓ : ℝ} (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) :
    ((d : ℝ) - 1) ^ (ℓ / 2 - 1) ≤ ((avoidingTreeCut forbidden k).card : ℝ) := by
  have hd1 : 1 ≤ (d : ℝ) - 1 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 :=
    by rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  calc
    ((d : ℝ) - 1) ^ (ℓ / 2 - 1) ≤ ((d : ℝ) - 1) ^ ((k + 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1 hlevel
    _ = (((d - 1) ^ (k + 1) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, Nat.cast_pow, hcast]
    _ ≤ _ := by exact_mod_cast pow_le_card_avoidingTreeCut forbidden hF k

theorem attenuation_le_quarter_threshold {c η x : ℝ}
    (hx : 0 ≤ x) (hη : η ≤ c / 4) (hlength : 8 * Real.log 2 ≤ c * x) :
    Real.exp (-c * x / 2) ≤ Real.exp (-η * x) / 4 := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  apply (le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)).mpr
  conv_lhs => rhs; rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num)]
  rw [← Real.exp_add, hlog]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hη hx]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuations
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem sum_cutContinuations {M : Type*} [AddCommMonoid M]
    (d k L : ℕ) (f : TreeShell d (k + 1 + L) → M) :
    (∑ v : TreeShell d (k + 1 + L), f v) =
      ∑ p : TreeShell d (k + 1), ∑ w : ReducedTail (cutLastColor p) L,
        f (appendCutContinuation p w) := by
  rw [← (cutContinuationEquiv d k L).sum_comp f, Fintype.sum_sigma]
  rfl

theorem sum_cutDescendants {M : Type*} [AddCommMonoid M] {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → M) :
    (∑ v ∈ cutDescendants I L, f v) =
      ∑ p ∈ I, ∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w) := by
  classical
  have h := sum_cutContinuations d k L (fun v => if cutPrefix v ∈ I then f v else 0)
  simpa [cutDescendants, Finset.sum_filter] using h

@[simp] theorem card_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (cutDescendants I L).card = I.card * (d - 1) ^ L := by
  classical
  have h := sum_cutDescendants I L (fun _ => (1 : ℕ))
  simpa using h

theorem average_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → ℝ) :
    (∑ v ∈ cutDescendants I L, f v) / ((cutDescendants I L).card : ℝ) =
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w)) /
        (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [sum_cutDescendants, card_cutDescendants, Nat.cast_mul,
    ← Finset.sum_div, div_div, mul_comm]

theorem rootPathProduct_le_cutContinuationProduct {d k L : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    rootPathProduct a (appendCutContinuation p w).1 ≤ cutContinuationProduct a p w := by
  unfold rootPathProduct
  rw [(appendCutContinuation p w).2, Finset.prod_range_add]
  have hpre : (∏ i ∈ Finset.range (k + 1),
      a (rootPathVertex (appendCutContinuation p w).1 (i + 1))) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (ha _).1) (fun i _ => (ha _).2)
  have htail : 0 ≤ (∏ j ∈ Finset.range L,
      a (rootPathVertex (appendCutContinuation p w).1 (k + 1 + j + 1))) :=
    Finset.prod_nonneg (fun j _ => (ha _).1)
  have h := mul_le_mul_of_nonneg_right hpre htail
  simpa only [one_mul, cutContinuationProduct, Nat.add_assoc] using h

theorem average_rootPathProduct_le_continuation_average {d k : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (∑ v ∈ cutDescendants I L, rootPathProduct a v.1) /
        ((cutDescendants I L).card : ℝ) ≤
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L,
        cutContinuationProduct a p w) / (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [average_cutDescendants]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun w _ => rootPathProduct_le_cutContinuationProduct a ha p w)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutLevelConcentration
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem integral_cond_fiber_le_of_condExp_le
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Ω → S} (hs : Measurable s)
    {f : Ω → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbound : ∀ᵐ ω ∂μ, (μ[f | MeasurableSpace.comap s inferInstance]) ω ≤ C)
    (a : S) (ha : μ (s ⁻¹' {a}) ≠ 0) :
    (∫ ω, f ω ∂μ[|s ⁻¹' {a}]) ≤ C := by
  have : (ae (μ.restrict (s ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp ha)
  have hCE := condExp_comap_eq_cond_on_fiber hs a hf
  have hB := ae_restrict_le (s := s ⁻¹' {a}) hbound
  obtain ⟨ω, hωCE, hωB⟩ := (hCE.and hB).exists
  exact hωCE.symm.le.trans hωB

theorem measureReal_le_of_cond_fibers
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Countable S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} (hs : Measurable s)
    {E : Set Ω} (hE : MeasurableSet E) {C : ℝ}
    (hbound : ∀ a : S, μ (s ⁻¹' {a}) ≠ 0 → μ[|s ⁻¹' {a}].real E ≤ C) :
    μ.real E ≤ C := by
  have hCE : ∀ᵐ ω ∂μ,
      (μ[E.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap s inferInstance]) ω ≤ C := by
    apply ae_of_ae_restrict_fibers hs
    intro a
    by_cases ha : μ (s ⁻¹' {a}) = 0
    · rw [Measure.restrict_eq_zero.mpr ha]
      simp
    filter_upwards [condExp_indicator_comap_eq_cond_on_fiber hs a hE] with ω hω
    exact hω.le.trans (hbound a ha)
  have hint := integral_mono_ae integrable_condExp (integrable_const C) hCE
  rw [integral_condExp hs.comap_le] at hint
  simpa only [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one,
    integral_const, probReal_univ, one_smul, one_mul] using hint

local instance localInst_r8629fa_3 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measure_cutLevel_average_ge_cond_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4)
    (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}]
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  let X := fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
    F c ((fun v => z.1 v.1), fun v => z.2 v.1)
  have hS : Measurable S := by fun_prop
  have hX : ∀ c, Measurable (X c) := fun c => (hF c).comp (by fun_prop)
  let : IsProbabilityMeasure ((μ.prod (Measure.infinitePi ν))[|
      {z | (fun c : TreeShell d n => z.1 c.1) = s}]) := cond_isProbabilityMeasure hs
  apply BoundedAverageConcentration.measure_average_ge_le
    (hμ.iIndepFun_cutLevel_observables_cond h0 h1 n ν F hF s hs) I hI hτ
  · intro c _
    exact (hX c).aemeasurable
  · intro c _
    exact Filter.Eventually.of_forall (fun z => hbound c _)
  · intro c hc
    have hi : Integrable (X c) P := by
      apply Integrable.of_bound (hX c).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound c _).1]
        exact (hbound c _).2)
    have hb := integral_cond_fiber_le_of_condExp_le hS hi
      (hμ.condExp_cutLevel_observable_le_two_integral h0 h1 n ν c (F c) (hF c)
        (hbound c)) s hs
    exact hb.trans (by linarith [hmean c hc])

theorem HasFreeIsingLaw.measure_cutLevel_average_ge_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hsum : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) :=
    Finset.measurable_fun_sum I (fun c _ => (hF c).comp (by fun_prop))
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  apply measureReal_le_of_cond_fibers hS (measurableSet_le measurable_const (hsum.div_const _))
  intro s hs
  have h := hμ.measure_cutLevel_average_ge_cond_le h0 h1 n ν F hF hbound I hI hτ hmean s hs
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h |>.trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuationChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.CutContinuationChannels
open RootedBroadcast

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem measurable_globalCone (v : TreeVertex d) : Measurable (globalCone (A := A) v) := by
  unfold globalCone
  fun_prop

theorem measurable_restrictCone {u v : TreeVertex d} (h : u.1 <+: v.1) :
    Measurable (restrictCone (A := A) h) := by
  unfold restrictCone
  fun_prop

theorem measurable_continuationChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    Measurable (continuationChannel F p w) := by
  apply Finset.measurable_fun_prod
  intro j hj
  exact (hF _).comp (measurable_restrictCone _)

omit [MeasurableSpace A] in
theorem continuationChannel_mem_Icc
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : ConeSample A p.1) : continuationChannel F p w z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (hb _ _).1),
    Finset.prod_le_one (fun _ _ => (hb _ _).1) (fun _ _ => (hb _ _).2)⟩

theorem measurable_averageChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) : Measurable (averageChannel F p L) :=
  (Finset.measurable_fun_sum _ (fun w _ => measurable_continuationChannel F hF p w)).div_const _

omit [MeasurableSpace A] in
theorem averageChannel_mem_Icc (hd : 2 ≤ d)
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) (z : ConeSample A p.1) :
    averageChannel F p L z ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : (0 : ℝ) < Fintype.card (ReducedTail (cutLastColor p) L) := by
    rw [card_reducedTail]
    exact_mod_cast pow_pos (by omega : 0 < d - 1) L
  constructor
  · exact div_nonneg (Finset.sum_nonneg
      (fun w _ => (continuationChannel_mem_Icc F hb p w z).1)) hc.le
  · apply (div_le_iff₀ hc).mpr
    simpa using Finset.sum_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (ReducedTail (cutLastColor p) L))) =>
        (continuationChannel_mem_Icc F hb p w z).2)

omit [MeasurableSpace A] in
theorem path_average_le_averageChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (∑ v ∈ cutDescendants I L, rootPathProduct (globalFactors F z) v.1) /
        ((cutDescendants I L).card : ℝ) ≤
      (∑ p ∈ I, averageChannel F p L (globalCone p.1 z)) / (I.card : ℝ) := by
  simpa only [averageChannel_globalCone] using
    average_rootPathProduct_le_continuation_average (globalFactors F z)
      (fun v => hb v _) I L

theorem integral_averageChannel_le (hd : 2 ≤ d)
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ)
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsProbabilityMeasure P] {m : ℝ}
    (hmean : ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w ∂P) ≤ m) :
    (∫ z, averageChannel F p L (globalCone p.1 z) ∂P) ≤ m := by
  have hc : (0 : ℝ) < Fintype.card (ReducedTail (cutLastColor p) L) := by
    rw [card_reducedTail]
    exact_mod_cast pow_pos (by omega : 0 < d - 1) L
  have hi (w : ReducedTail (cutLastColor p) L) :
      Integrable (fun z => continuationChannel F p w (globalCone p.1 z)) P := by
    apply Integrable.of_bound
      ((measurable_continuationChannel F hF p w).comp (measurable_globalCone p.1)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    change ‖continuationChannel F p w (globalCone p.1 z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (continuationChannel_mem_Icc F hb p w _).1]
    exact (continuationChannel_mem_Icc F hb p w _).2
  calc
    _ = (∑ w : ReducedTail (cutLastColor p) L,
          ∫ z, continuationChannel F p w (globalCone p.1 z) ∂P) /
        (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ) := by
      unfold averageChannel
      rw [integral_div, integral_finsetSum _ (fun w _ => hi w)]
    _ ≤ (∑ _w : ReducedTail (cutLastColor p) L, m) /
        (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact Finset.sum_le_sum (fun w _ => hmean w)
    _ = m := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ m hc.ne'

theorem measure_path_average_ge_le [StandardBorelSpace A]
    {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (hd : 2 ≤ d)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ p ∈ I, ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | τ ≤ (∑ v ∈ cutDescendants I L, rootPathProduct (globalFactors F z) v.1) /
        ((cutDescendants I L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  calc
    _ ≤ (μ.prod (Measure.infinitePi ν))
        {z | τ ≤ (∑ p ∈ I, averageChannel F p L (globalCone p.1 z)) / (I.card : ℝ)} := by
      apply measure_mono
      intro z hz
      exact hz.trans (path_average_le_averageChannel F hb I L z)
    _ ≤ _ := hμ.measure_cutLevel_average_ge_le h0 h1 (k + 1) ν
      (fun p => averageChannel F p L) (fun p => measurable_averageChannel F hF p L)
      (fun p z => averageChannel_mem_Icc hd F hb p L z) I hI hτ
      (fun p hp => integral_averageChannel_le hd F hF hb p L _ (hmean p hp))

theorem measure_restricted_path_average_ge_le_double_exp [StandardBorelSpace A]
    {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (hd : 2 ≤ d)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {q ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hq : q ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ))
    (hmean : ∀ p ∈ avoidingTreeCut forbidden k, ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi ν)) ≤ Real.exp (-q * ℓ) / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | Real.exp (-q * ℓ) ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut forbidden k) L,
          rootPathProduct (globalFactors F z) v.1) /
            ((cutDescendants (avoidingTreeCut forbidden k) L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) / (2 * ((d : ℝ) - 1)))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact (measure_path_average_ge_le hμ h0 h1 hd ν F hF hb
    (avoidingTreeCut forbidden k) (avoidingTreeCut_nonempty hd forbidden hforbidden k)
    L (Real.exp_pos _).le hmean).trans
      (ENNReal.ofReal_le_ofReal (BoundedAverageConcentration.exponential_card_bound
        (by linarith) hℓ hq (rpow_le_card_avoidingTreeCut hd forbidden hforbidden k hlevel)))

end Problem367.CutContinuationChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyRootIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideBranches
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem edge_leaving_cone {d : ℕ} {r u w : TreeVertex d}
    (hu : u ∈ cone r) (hw : w ∉ cone r) (huw : treeAdj u w) :
    u = r ∧ w = parentVertex r := by
  have hur : u = r := by
    by_contra hne
    exact hw (treeAdj_preserves_prefix hu huw hne)
  subst u
  refine ⟨rfl, ?_⟩
  rcases huw with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact False.elim (hw (by
      change r.1 <+: w.1
      rw [hc]
      exact List.prefix_append _ _))
  · apply Subtype.ext
    change w.1 = r.1.dropLast
    rw [hc]
    simp

theorem reachable_in_cone {d : ℕ} {r u : TreeVertex d} (hu : u ∈ cone r) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
  have aux : ∀ n : ℕ, ∀ u : TreeVertex d, u.1.length = n → u ∈ cone r →
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hlen hu
      by_cases hur : u = r
      · subst u
        exact .refl
      · have hlt : r.1.length < u.1.length := by
          have hle := hu.length_le
          have hne : r.1.length ≠ u.1.length := by
            intro heq
            exact hur (Subtype.ext (hu.eq_of_length heq).symm)
          omega
        have hnil : u.1 ≠ [] := by
          intro h
          simp [h] at hlt
        have hp : parentVertex u ∈ cone r := by
          apply List.prefix_of_prefix_length_le hu (List.dropLast_prefix u.1)
          rw [List.length_dropLast]
          omega
        have hplen : (parentVertex u).1.length < n := by
          rw [parentVertex_length]
          omega
        exact (ih _ hplen _ rfl hp).tail ⟨hp, hu, treeAdj_parentVertex hnil⟩
  exact aux _ u rfl hu

theorem parent_not_mem_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    parentVertex r ∉ cone r := by
  intro h
  have hlen := h.length_le
  rw [parentVertex_length] at hlen
  have hpos := List.length_pos_iff.mpr hr
  omega

theorem mem_cone_iff_reachable_avoiding_parent {d : ℕ} (r u : TreeVertex d)
    (hr : r.1 ≠ []) : u ∈ cone r ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ parentVertex r ∧ y ≠ parentVertex r ∧ treeAdj x y)
      r u := by
  constructor
  · intro hu
    apply Relation.ReflTransGen.mono (fun x y hxy => ?_) r u (reachable_in_cone hu)
    exact ⟨fun h => parent_not_mem_cone r hr (h ▸ hxy.1),
      fun h => parent_not_mem_cone r hr (h ▸ hxy.2.1), hxy.2.2⟩
  · intro h
    induction h with
    | refl => exact List.prefix_refl _
    | tail h hxy ih =>
        by_contra hy
        exact hxy.2.1 (edge_leaving_cone ih hy hxy.2.2).2

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideReroot
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem map_reachable_avoiding {d : ℕ} (g : TreeAut d)
    {p a b : TreeVertex d}
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) := by
  induction h with
  | refl => exact .refl
  | tail h hxy ih =>
      exact ih.tail ⟨fun he => hxy.1 (g.toEquiv.injective he),
        fun he => hxy.2.1 (g.toEquiv.injective he), (g.map_adj _ _).mpr hxy.2.2⟩

theorem map_reachable_avoiding_iff {d : ℕ} (g : TreeAut d)
    (p a b : TreeVertex d) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b := by
  constructor
  · intro h
    have hm := map_reachable_avoiding g.symm h
    simpa only [TreeAut.symm, Equiv.symm_apply_apply] using hm
  · exact map_reachable_avoiding g

theorem mem_cone_iff_map_mem_root_branch {d : ℕ} (g : TreeAut d)
    (r : TreeVertex d) (hr : r.1 ≠ []) (c : Fin d)
    (hp : g.toEquiv (parentVertex r) = ConnectedHull.root d)
    (hc : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩) (u : TreeVertex d) :
    u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  let s : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hs : s.1 ≠ [] := by simp [s]
  have hparent : parentVertex s = ConnectedHull.root d := by
    apply Subtype.ext
    rfl
  have hmap := map_reachable_avoiding_iff g (parentVertex r) r u
  rw [hp, hc, ← hparent] at hmap
  rw [mem_cone_iff_reachable_avoiding_parent r u hr]
  change _ ↔ g.toEquiv u ∈ cone s
  rw [mem_cone_iff_reachable_avoiding_parent s (g.toEquiv u) hs]
  exact hmap.symm

theorem exists_reroot_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv (parentVertex r) = ConnectedHull.root d ∧
      g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root (parentVertex r)
  have hadj := (g.map_adj (parentVertex r) r).mpr (treeAdj_parentVertex hr)
  rw [hg] at hadj
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv r).1 = [c] := by
    rcases hadj with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hgr : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  exact ⟨g, c, hg, hgr, mem_cone_iff_map_mem_root_branch g r hr c hg hgr⟩

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_CutChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches CutContinuationChannels

theorem exists_local_gaussianConeFactor {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) :
    ∃ F : ∀ v : TreeVertex d, ConeSample ℝ v → ℝ,
      (∀ v, Measurable (F v)) ∧ (∀ v z, 0 ≤ F v z ∧ F v z ≤ 1) ∧
      ∀ z v, globalFactors F z v = gaussianConeFactor μ t theta z v := by
  classical
  have hex (v : TreeVertex d) : ∃ f : ConeSample ℝ v → ℝ,
      Measurable f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, gaussianConeFactor μ t theta z v = f (globalCone v z) := by
    have hF : Measurable (Function.uncurry
        (fun s x => (t : ℝ) * spinSign s + x)) :=
      ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
        (t : ℝ)).add measurable_snd
    exact exists_selectedAttenuation_local_channel
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hF
      (Subtype.val : cone v → TreeVertex d) id v hθ
  choose f hf hb heq using hex
  exact ⟨f, hf, hb, fun z v => (heq v z).symm⟩

theorem measure_gaussian_restricted_path_average_ge_le_double_exp {d : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      {z | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut forbidden k) L,
          rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants (avoidingTreeCut forbidden k) L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  let := hμ.isProbabilityMeasure
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hc := (ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1).le
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 :=
    le_min (Real.sqrt_nonneg _) (by norm_num)
  obtain ⟨F, hF, hb, heq⟩ := exists_local_gaussianConeFactor μ t hθ
  have hfactor : globalFactors F = gaussianConeFactor μ t (Real.tanh beta) :=
    funext (fun z => funext (fun v => heq z v))
  have hmean (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 t))) ≤
          Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) / 4 := by
    rw [hfactor]
    change (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ _
    refine (integral_cutContinuationProduct_gaussianConeFactor_le
      hμ hbeta hd hcritical ht p w).trans ?_
    calc
      _ ≤ Real.exp (-ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          (min (Real.sqrt (t : ℝ)) 1 * ℓ) / 2) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left htail (mul_nonneg hc hω)
        nlinarith
      _ ≤ Real.exp (-η * (min (Real.sqrt (t : ℝ)) 1 * ℓ)) / 4 :=
        attenuation_le_quarter_threshold (mul_nonneg hω hℓ) hη hlength
      _ = _ := by ring_nf
  have hq : η * min (Real.sqrt (t : ℝ)) 1 ≤ Real.log ((d : ℝ) - 1) / 8 :=
    (mul_le_of_le_one_right hη0 (min_le_right _ _)).trans hηlog
  have h := measure_restricted_path_average_ge_le_double_exp hμ
    (by linarith : -1 ≤ Real.tanh beta) hθ1.le (by omega : 2 ≤ d)
    (fun _ : TreeVertex d => gaussianReal 0 t) F hF hb forbidden hforbidden k L
    hℓ hq hlevel (fun p _ w => hmean p w)
  simpa only [hfactor, PlantedSymmetry.gaussianNoiseLaw] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeComplementFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem prefixFlip_mem_branch_iff {d : ℕ} (c : Fin d) (u : TreeVertex d) :
    [c] <+: (prefixFlip c u).1 ↔ ¬ [c] <+: u.1 := by
  rcases u with ⟨w, hw⟩
  cases w with
  | nil => simp [prefixFlip, prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · subst a
      cases w with
      | nil => simp [prefixFlip, prefixFlipWord]
      | cons b w =>
        have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
        simp [prefixFlip, prefixFlipWord, hcb]
    · simp [prefixFlip, prefixFlipWord, h]

theorem exists_reroot_cone_complement {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv r = ConnectedHull.root d ∧
      g.toEquiv (parentVertex r) = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∉ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  refine ⟨g.trans (prefixTreeAut c), c, ?_, ?_, ?_⟩
  · change prefixFlip c (g.toEquiv r) = _
    rw [hc]
    apply Subtype.ext
    simp [prefixFlip, prefixFlipWord, ConnectedHull.root]
  · change prefixFlip c (g.toEquiv (parentVertex r)) = _
    rw [hp]
    rfl
  · intro u
    change u ∉ cone r ↔ [c] <+: (prefixFlip c (g.toEquiv u)).1
    rw [prefixFlip_mem_branch_iff, hgeo]
end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutFields
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

theorem parent_takeVertex_succ {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : parentVertex (takeVertex v (i + 1)) = takeVertex v i := by
  apply treeAdj_parent_of_length_lt (prefix_adj v hi)
  simp only [takeVertex, List.length_take, Nat.min_eq_left hi.le,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega)]
  omega

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardProducts
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367
open PathSideBranches

theorem gaussianInwardConeFactor_rootPathVertex {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (v : TreeVertex d) {i : ℕ} (hi : i < v.1.length) (z) :
    gaussianInwardConeFactor μ t theta z (rootPathVertex v (i + 1)) =
      responseAttenuation theta (inwardGaussianField μ t v i z) ^ 2 := by
  change responseAttenuation theta (regionGaussianField μ t
    (cone (ConnectedHull.takeVertex v (i + 1)))ᶜ
    (parentVertex (ConnectedHull.takeVertex v (i + 1))) z) ^ 2 = _
  rw [parent_takeVertex_succ v hi]
  rfl

theorem rootPathProduct_gaussianInwardConeFactor {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (v : TreeVertex d) (z) :
    rootPathProduct (gaussianInwardConeFactor μ t theta z) v =
      ∏ i ∈ Finset.range v.1.length,
        responseAttenuation theta (inwardGaussianField μ t v i z) ^ 2 := by
  apply Finset.prod_congr rfl
  intro i hi
  exact gaussianInwardConeFactor_rootPathVertex μ t theta v (Finset.mem_range.mp hi) z

end Problem367

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

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
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

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [field_array_relabel_ae hμ g t] with x hx
  unfold cavityObservable
  rw [hx]
  rfl

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathRerooting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem stripPrefixAut_of_append {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (s : List (Fin d)) (hv : v.1 = stem ++ s) :
    ((stripPrefixAut stem).toEquiv v).1 = s := by
  induction stem generalizing v with
  | nil =>
    change v.1 = s
    simpa only [List.nil_append] using hv
  | cons a stem ih =>
    change ((stripPrefixAut stem).toEquiv (prefixFlip a v)).1 = s
    apply ih
    simp [prefixFlip, prefixFlipWord, hv]

theorem stripPrefixAut_eq_drop {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (hpre : stem <+: v.1) :
    ((stripPrefixAut stem).toEquiv v).1 = v.1.drop stem.length := by
  obtain ⟨s, hs⟩ := hpre
  rw [stripPrefixAut_of_append stem v s hs.symm, ← hs]
  simp

theorem stripPrefixAut_takeVertex {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hi : i ≤ v.1.length) (hij : i ≤ j) :
    (stripPrefixAut (v.1.take i)).toEquiv (ConnectedHull.takeVertex v j) =
      ConnectedHull.takeVertex (dropVertex v i) (j - i) := by
  apply Subtype.ext
  have hpre : v.1.take i <+: (ConnectedHull.takeVertex v j).1 := by
    change v.1.take i <+: v.1.take j
    simpa only [List.take_take, Nat.min_eq_left hij] using
      List.take_prefix i (v.1.take j)
  rw [stripPrefixAut_eq_drop _ _ hpre]
  simp only [ConnectedHull.takeVertex, dropVertex, List.length_take,
    Nat.min_eq_left hi, List.drop_take]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds ConnectedHull

theorem measurable_attenuation {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    Measurable (attenuation hb t inward v) := by
  unfold attenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_cavityObservable hb t _ _))

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InfiniteConeCavity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry CavityFieldLimit PathSideBranches

theorem HasFreeIsingLaw.infiniteCavityField_eq_cone_posterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ r (parentVertex r) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (Subtype.val : cone r → TreeVertex d) r p) := by
  obtain ⟨g, c, hp, hc, hcone⟩ := exists_reroot_cone r hr
  have hr' : g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩ = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
  have hp' : g.toEquiv.symm (ConnectedHull.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
  have hregion : Set.range
      (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i)) =
      Set.range (Subtype.val : cone r → TreeVertex d) := by
    ext u
    rw [Subtype.range_coe_subtype]
    constructor
    · rintro ⟨i, rfl⟩
      apply (hcone _).mpr
      rw [Equiv.apply_symm_apply]
      apply (singleton_prefix_iff_cons c _).mpr
      exact ⟨i.2.1, rfl⟩
    · intro hu
      have hbranch := (singleton_prefix_iff_cons c (g.toEquiv u)).mp ((hcone u).mp hu)
      obtain ⟨i, hi⟩ := mem_range_componentIndexVertex.mpr hbranch
      refine ⟨i, ?_⟩
      change g.toEquiv.symm (componentIndexVertex i) = u
      rw [hi, Equiv.symm_apply_apply]
  have hfield := selectedObservationField_eq_of_range_eq
    (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z) hregion
  simpa only [hr', hp', selectedPosterior, hfield] using
    hμ.infiniteCavityField_eq_relabelled_component hβ t g c

theorem HasFreeIsingLaw.infiniteCavityField_path_eq_forward_posterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β)
    (t : ℝ≥0) (v : TreeVertex d) (k : ℕ) (hk : k < v.1.length) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ (ConnectedHull.takeVertex v (k + 1))
        (ConnectedHull.takeVertex v k) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (Subtype.val : cone (ConnectedHull.takeVertex v (k + 1)) → TreeVertex d)
        (ConnectedHull.takeVertex v (k + 1)) p) := by
  have hr : (ConnectedHull.takeVertex v (k + 1)).1 ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [ConnectedHull.takeVertex, List.length_take, List.length_nil] at hlen
    omega
  have hp : parentVertex (ConnectedHull.takeVertex v (k + 1)) =
      ConnectedHull.takeVertex v k := by
    apply Subtype.ext
    simp only [parentVertex, ConnectedHull.takeVertex,
      List.take_succ_eq_append_getElem hk, List.dropLast_concat]
  simpa only [hp] using hμ.infiniteCavityField_eq_cone_posterior hβ t
    (ConnectedHull.takeVertex v (k + 1)) hr

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_RootGaussianCut
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootGaussianCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation IsingRootWeightedCut
open PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_eq_forward_product
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => terminalAttenuation hbeta v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => ∏ i ∈ Finset.range v.1.length,
        responseAttenuation (Real.tanh beta) (forwardGaussianField μ t v i p) := by
  have hfield (i : Fin v.1.length) :=
    hμ.infiniteCavityField_path_eq_forward_posterior hbeta t v i i.2
  filter_upwards [ae_all_iff.mpr hfield] with p hp
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (responseAttenuation (Real.tanh beta)) (hp ⟨i, Finset.mem_range.mp hi⟩)

end Problem367.IsingRootGaussianCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InfiniteInwardCavity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PlantedSymmetry CavityFieldLimit PathSideBranches

theorem HasFreeIsingLaw.infiniteCavityField_eq_complement_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∀ᵐ z ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta (parentVertex r) r (observation t z) =
        regionGaussianField μ t (cone r)ᶜ (parentVertex r) z := by
  obtain ⟨g, c, hr0, hpc, hcone⟩ := exists_reroot_cone_complement r hr
  have hp' : g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩ = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hpc]
  have hr' : g.toEquiv.symm (ConnectedHull.root d) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hr0]
  have hregion : Set.range
      (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i)) =
      Set.range (Subtype.val : ((cone r)ᶜ : Set (TreeVertex d)) → TreeVertex d) := by
    ext u
    rw [Subtype.range_coe_subtype]
    constructor
    · rintro ⟨i, rfl⟩
      apply (hcone _).mpr
      rw [Equiv.apply_symm_apply]
      apply (singleton_prefix_iff_cons c _).mpr
      exact ⟨i.2.1, rfl⟩
    · intro hu
      have hbranch := (singleton_prefix_iff_cons c (g.toEquiv u)).mp ((hcone u).mp hu)
      obtain ⟨i, hi⟩ := mem_range_componentIndexVertex.mpr hbranch
      refine ⟨i, ?_⟩
      change g.toEquiv.symm (componentIndexVertex i) = u
      rw [hi, Equiv.symm_apply_apply]
  have hfield := selectedObservationField_eq_of_range_eq
    (fun (s : IsingSpin) (x : ℝ) => (t : ℝ) * spinSign s + x) hregion
  simpa only [hp', hr', regionGaussianField, selectedPosterior, hfield] using
    hμ.infiniteCavityField_eq_relabelled_component hbeta t g c

theorem HasFreeIsingLaw.infiniteCavityField_path_eq_inward_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {i : ℕ} (hi : i < v.1.length) :
    ∀ᵐ z ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta (ConnectedHull.takeVertex v i)
        (ConnectedHull.takeVertex v (i + 1)) (observation t z) =
      inwardGaussianField μ t v i z := by
  have hr : (ConnectedHull.takeVertex v (i + 1)).1 ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [ConnectedHull.takeVertex, List.length_take, List.length_nil] at hl
    omega
  simpa only [parent_takeVertex_succ v hi, inwardGaussianField] using
    hμ.infiniteCavityField_eq_complement_posterior hbeta t
      (ConnectedHull.takeVertex v (i + 1)) hr

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral IsingConditionalCopyBounds
open TreeOrbitAverage PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measurable_terminalAttenuation (hb : 0 ≤ beta) (inward : Bool)
    (v : TreeVertex d) : Measurable (terminalAttenuation hb inward v) := by
  unfold terminalAttenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_infiniteCavityField hb _ _))

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_inward_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb true v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v := by
  have hfield (i : Fin v.1.length) :=
    hμ.infiniteCavityField_path_eq_inward_posterior hb t v i.2
  filter_upwards [ae_all_iff.mpr hfield] with z hz
  rw [rootPathProduct_gaussianInwardConeFactor, terminalAttenuation, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun x => responseAttenuation (Real.tanh beta) x ^ 2)
    (hz ⟨i, Finset.mem_range.mp hi⟩)

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_outward_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb false v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) z) v := by
  filter_upwards [IsingRootGaussianCut.terminalAttenuation_eq_forward_product hμ hb t v]
    with z hz
  change IsingRootGaussianCut.terminalAttenuation hb v (observation t z) ^ 2 = _
  rw [hz, ← Finset.prod_pow]
  rfl

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb inward v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (orientedGaussianFactor μ t (Real.tanh beta) inward z) v := by
  cases inward
  · exact terminalAttenuation_outward_sq_eq_rootPathProduct hμ hb t v
  · exact terminalAttenuation_inward_sq_eq_rootPathProduct hμ hb t v

theorem restrictedAverage_identDistrib_gaussian
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) {n : ℕ} (I : Finset (TreeShell d n)) :
    IdentDistrib (restrictedAverage hb t inward I)
      (fun z => (∑ v ∈ I,
        rootPathProduct (orientedGaussianFactor μ t (Real.tanh beta) inward z) v.1) /
          (I.card : ℝ)) (observationLaw μ)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let F : (TreeVertex d → ℝ) → ℝ := fun y =>
    (∑ v ∈ I, terminalAttenuation hb inward v.1 y ^ 2) / (I.card : ℝ)
  have hF : Measurable F :=
    (Finset.measurable_sum _ (fun v _ =>
      (measurable_terminalAttenuation hb inward v.1).pow_const 2)).div_const _
  have hobs : HasLaw (observation (ι := TreeVertex d) t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  have hlaw := ((hasLaw_observationLaw_eval μ t).identDistrib hobs).comp hF
  apply hlaw.trans
  apply IdentDistrib.of_ae_eq (hF.comp (measurable_observation t)).aemeasurable
  filter_upwards [ae_all_iff.mpr (fun v : TreeShell d n =>
    terminalAttenuation_sq_eq_rootPathProduct hμ hb t inward v.1)] with z hz
  change (∑ v ∈ I, terminalAttenuation hb inward v.1 (observation t z) ^ 2) /
    (I.card : ℝ) = _
  congr 1
  exact Finset.sum_congr rfl (fun v _ => hz v)

theorem measure_restrictedAverage_ge_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        restrictedAverage hb t inward (cutDescendants (avoidingTreeCut forbidden k) L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  have heq := (restrictedAverage_identDistrib_gaussian hμ hb t inward
    (cutDescendants (avoidingTreeCut forbidden k) L)).measure_mem_eq
    (measurableSet_Ici (a := orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ)))
  simp only [Set.preimage, Set.mem_Ici] at heq
  rw [heq]
  cases inward
  · simpa only [orientationCutCost, orientedGaussianFactor, Bool.false_eq_true,
      ↓reduceIte, one_mul] using
      measure_gaussian_restricted_path_average_ge_le_double_exp hμ hb hd hcritical ht
        forbidden hforbidden k L hη0 hℓ hη hηlog hlevel htail hlength
  · exact measure_gaussian_inward_restricted_path_average_ge_le_double_exp
      hμ hb hd hcritical ht forbidden hforbidden k L hη0 hℓ hη hηlog hlevel htail hlength

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_StemRerootAverage
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367.TreeOrbitAverage
open ConnectedHull

theorem card_stemForbidden_le_one {d : ℕ} (stem : List (Fin d)) :
    (stemForbidden stem).card ≤ 1 := by
  unfold stemForbidden
  cases stem.getLast? <;> simp

theorem average_extension_suffix {d : ℕ} (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) (f : TreeVertex d → ℝ) :
    (∑ s : Extension stem (k + 1 + L), f (suffixVertex s)) /
        (Fintype.card (Extension stem (k + 1 + L)) : ℝ) =
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L, f v.1) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  classical
  let e := extensionEquivCutDescendants stem hstem k L
  have hsum := e.sum_comp (fun v => f v.1.1)
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_coe] at hcard
  have hs : (∑ s : Extension stem (k + 1 + L), f (suffixVertex s)) =
      ∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L, f v.1 := by
    calc
      _ = ∑ v : {v // v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L},
          f v.1.1 := hsum
      _ = _ := Finset.sum_coe_sort
        (cutDescendants (avoidingTreeCut (stemForbidden stem) k) L)
        (fun v : TreeShell d (k + 1 + L) => f v.1)
  rw [hcard, hs]

theorem stripPrefixAut_extension_prefix {d n : ℕ} {stem : List (Fin d)}
    (s : Extension stem n) (i : ℕ) :
    (stripPrefixAut stem).toEquiv (takeVertex (endpoint s) (stem.length + i)) =
      takeVertex (suffixVertex s) i := by
  have hlen : stem.length ≤ (endpoint s).1.length := by
    change stem.length ≤ (stem ++ s.1).length
    simp
  have htake : (endpoint s).1.take stem.length = stem := by
    change (stem ++ s.1).take stem.length = stem
    simp
  have hdrop : dropVertex (endpoint s) stem.length = suffixVertex s := by
    apply Subtype.ext
    change (stem ++ s.1).drop stem.length = s.1
    simp
  simpa only [htake, hdrop, Nat.add_sub_cancel_left] using
    stripPrefixAut_takeVertex (endpoint s) hlen (Nat.le_add_right stem.length i)

theorem rootEdgeProduct_endpoint_le_rerooted {d n : ℕ} {stem : List (Fin d)}
    (a : TreeVertex d → TreeVertex d → ℝ)
    (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1) (s : Extension stem n) :
    rootEdgeProduct a (endpoint s) ≤
      rootEdgeProduct (fun u v => a ((stripPrefixAut stem).toEquiv.symm u)
        ((stripPrefixAut stem).toEquiv.symm v)) (suffixVertex s) := by
  unfold rootEdgeProduct
  have hlen : (endpoint s).1.length = stem.length + n := by
    simp only [endpoint, List.length_append, s.2.1]
  rw [hlen, Finset.prod_range_add]
  have hpre : (∏ i ∈ Finset.range stem.length,
      a (takeVertex (endpoint s) i) (takeVertex (endpoint s) (i + 1))) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => (ha _ _).1) (fun _ _ => (ha _ _).2)
  have hnonneg : 0 ≤ (∏ j ∈ Finset.range n,
      a (takeVertex (endpoint s) (stem.length + j))
        (takeVertex (endpoint s) (stem.length + j + 1))) :=
    Finset.prod_nonneg (fun _ _ => (ha _ _).1)
  refine (mul_le_mul_of_nonneg_right hpre hnonneg).trans_eq ?_
  rw [one_mul, suffixVertex_length]
  apply Finset.prod_congr rfl
  intro i hi
  have h (j : ℕ) : (stripPrefixAut stem).toEquiv.symm (takeVertex (suffixVertex s) j) =
      takeVertex (endpoint s) (stem.length + j) := by
    rw [← stripPrefixAut_extension_prefix s j, Equiv.symm_apply_apply]
  dsimp only
  rw [h i, h (i + 1), Nat.add_assoc]

theorem average_rootEdgeProduct_endpoint_le_rerooted {d : ℕ}
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    (a : TreeVertex d → TreeVertex d → ℝ)
    (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1) :
    (∑ s : Extension stem (k + 1 + L), rootEdgeProduct a (endpoint s)) /
        (Fintype.card (Extension stem (k + 1 + L)) : ℝ) ≤
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
        rootEdgeProduct (fun u w => a ((stripPrefixAut stem).toEquiv.symm u)
          ((stripPrefixAut stem).toEquiv.symm w)) v.1) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  rw [← average_extension_suffix stem hstem k L]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun s _ => rootEdgeProduct_endpoint_le_rerooted a ha s)

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_StemRerootAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem orderedEdgeFactor_mem_Icc (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (u v : TreeVertex d) (x : Paths d) :
    0 ≤ orderedEdgeFactor hb t inward u v x ∧ orderedEdgeFactor hb t inward u v x ≤ 1 := by
  unfold orderedEdgeFactor
  exact ⟨sq_nonneg _, pow_le_one₀
    (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
    (responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)⟩

theorem rootEdgeProduct_orderedEdgeFactor (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (x : Paths d) :
    rootEdgeProduct (fun u w => orderedEdgeFactor hb t inward u w x) v =
      attenuation hb t inward v x ^ 2 := by
  cases inward <;> simp only [rootEdgeProduct, orderedEdgeFactor, attenuation,
    edge, Bool.false_eq_true, ↓reduceIte, Finset.prod_pow]

omit [IsProbabilityMeasure μ] in
theorem orderedEdgeFactor_relabel_ae [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (g : TreeAut d) (u v : TreeVertex d) :
    (fun x => orderedEdgeFactor hb t inward u v (relabel g x)) =ᵐ[observationLaw μ]
      orderedEdgeFactor hb t inward (g.toEquiv.symm u) (g.toEquiv.symm v) := by
  cases inward
  · exact (cavityObservable_relabel_ae hμ hb g t v u).fun_comp
      (fun y => responseAttenuation (Real.tanh beta) y ^ 2)
  · exact (cavityObservable_relabel_ae hμ hb g t u v).fun_comp
      (fun y => responseAttenuation (Real.tanh beta) y ^ 2)

theorem extensionAverage_le_restricted_average_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) :
    ∀ᵐ x ∂observationLaw μ, extensionAverage hb t inward stem (k + 1 + L) x ≤
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
        attenuation hb t inward v.1 (relabel (stripPrefixAut stem) x) ^ 2) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  have hall : ∀ᵐ x ∂observationLaw μ, ∀ u v : TreeVertex d,
      orderedEdgeFactor hb t inward u v (relabel (stripPrefixAut stem) x) =
        orderedEdgeFactor hb t inward ((stripPrefixAut stem).toEquiv.symm u)
          ((stripPrefixAut stem).toEquiv.symm v) x :=
    ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun v =>
      orderedEdgeFactor_relabel_ae hμ hb t inward (stripPrefixAut stem) u v))
  filter_upwards [hall] with x hx
  have h := average_rootEdgeProduct_endpoint_le_rerooted stem hstem k L
    (fun u v => orderedEdgeFactor hb t inward u v x)
    (fun u v => orderedEdgeFactor_mem_Icc hb t inward u v x)
  have hfactor : (fun u v => orderedEdgeFactor hb t inward
      ((stripPrefixAut stem).toEquiv.symm u) ((stripPrefixAut stem).toEquiv.symm v) x) =
      (fun u v => orderedEdgeFactor hb t inward u v (relabel (stripPrefixAut stem) x)) :=
    funext (fun u => funext (fun v => (hx u v).symm))
  rw [hfactor] at h
  simp_rw [rootEdgeProduct_orderedEdgeFactor] at h
  simpa only [extensionAverage, WeightedOrbitAverage.average, div_eq_mul_inv, mul_comm] using h

theorem measure_extensionAverage_gt_le_restricted_average_ge
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) (τ : ℝ) :
    (observationLaw μ) {x | τ < extensionAverage hb t inward stem (k + 1 + L) x} ≤
      (observationLaw μ) {x | τ ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
          attenuation hb t inward v.1 x ^ 2) /
          ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ)} := by
  let F : Paths d → ℝ := fun x =>
    (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
      attenuation hb t inward v.1 x ^ 2) /
      ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ)
  have hF : Measurable F :=
    (Finset.measurable_fun_sum _ (fun v _ =>
      (measurable_attenuation hb t inward v.1).pow_const 2)).div_const _
  have hp := measurePreserving_observationLaw_relabel hμ (stripPrefixAut stem)
  calc
    _ ≤ (observationLaw μ) {x | τ ≤ F (relabel (stripPrefixAut stem) x)} := by
      apply measure_mono_ae
      filter_upwards [extensionAverage_le_restricted_average_relabel hμ hb t inward
        stem hstem k L] with x hx
      intro h
      exact h.le.trans hx
    _ = _ := hp.measure_preimage (measurableSet_le measurable_const hF).nullMeasurableSet

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedStemTail
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measure_extensionAverage_gt_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hb t inward stem (k + 1 + L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  exact (measure_extensionAverage_gt_le_restricted_average_ge hμ hb t inward stem hstem k L
    (orientationCutCost beta inward * Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ))).trans
      (measure_restrictedAverage_ge_le_double_exp hμ hb hd hcritical ht inward
        (stemForbidden stem) (card_stemForbidden_le_one stem) k L hη0 hℓ hη hηlog
        hlevel htail hlength)

theorem orientationCutCost_le_exp (hb : 0 ≤ beta) (inward : Bool) :
    orientationCutCost beta inward ≤ Real.exp (4 * beta / (1 - Real.tanh beta)) := by
  cases inward
  · change 1 ≤ Real.exp _
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (4 * beta / (1 - Real.tanh beta)) :=
        Real.exp_le_exp.mpr (div_nonneg (mul_nonneg (by norm_num) hb)
          (sub_nonneg.mpr (Real.tanh_lt_one beta).le))
  · exact le_rfl

theorem measure_extensionAverage_gt_le_double_exp_common_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | Real.exp (4 * beta / (1 - Real.tanh beta)) *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hb t inward stem (k + 1 + L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  refine le_trans (measure_mono ?_) (measure_extensionAverage_gt_le_double_exp
    hμ hb hd hcritical ht inward stem hstem k L hη0 hℓ hη hηlog hlevel htail hlength)
  intro x hx
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (orientationCutCost_le_exp hb inward)
    (Real.exp_pos _).le) hx

end Problem367.IsingOrientedPath

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common_oai := @OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common_oai
