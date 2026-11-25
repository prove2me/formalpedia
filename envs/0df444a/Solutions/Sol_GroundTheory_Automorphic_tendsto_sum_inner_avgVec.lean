-- Prove2me | solution 1 for GroundTheory.Automorphic.tendsto_sum_inner_avgVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:55.675167+00:00
-- url     : https://prove2.me/submissions/5c5c9c8d-d811-48eb-aa33-c9b6ab7d8241

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_norm_sum_inner_avgVec_sub_le
import Theorems.Thm_GroundTheory_Automorphic_eventually_finePart_isFine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [UniformSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open MeasurablePartition
namespace GroundTheory.Automorphic
theorem _root_.solution (k : C(X × X, ℂ)) :
    Tendsto (fun V => ∑ i : (finePart V).nonnull μ,
      ⟪(finePart V).avgVec μ i, contKernelOp μ k ((finePart V).avgVec μ i)⟫_ℂ) (fineFilter X)
      (𝓝 (∫ x, k (x, x) ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (μ.real univ + 1)
  have hδ : 0 < δ := by positivity
  have hW := CompactSpace.uniformContinuous_of_continuous k.continuous
    (Metric.dist_mem_uniformity hδ)
  obtain ⟨u, hu, v, hv, huv⟩ := entourageProd_subset hW
  filter_upwards [eventually_finePart_isFine (inter_mem hu hv)] with V hV
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_sum_inner_avgVec_sub_le μ _ k (ε := δ) fun i x hx y hy => ?_) ?_
  · have hmem : ((x, y), (x, x)) ∈ entourageProd u v :=
      ⟨refl_mem_uniformity hu, (hV i y hy x hx).2⟩
    have := huv hmem
    rw [← dist_eq_norm]
    exact (show dist (k (x, y)) (k (x, x)) < δ from this).le
  · have h : δ * μ.real univ = ε * (μ.real univ / (μ.real univ + 1)) := by
      simp only [δ]; field_simp
    rw [h]
    have : μ.real univ / (μ.real univ + 1) < 1 :=
      (div_lt_one (by positivity)).2 (lt_add_one _)
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]
end GroundTheory.Automorphic
