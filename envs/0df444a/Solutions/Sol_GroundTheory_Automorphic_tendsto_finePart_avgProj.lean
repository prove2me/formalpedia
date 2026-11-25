-- Prove2me | solution 1 for GroundTheory.Automorphic.tendsto_finePart_avgProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:40.416849+00:00
-- url     : https://prove2.me/submissions/bf05107c-b15e-4198-979e-40309686173b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_orthonormal_avgVec
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_norm_toLp_sub_avgProj_le
import Theorems.Thm_GroundTheory_Automorphic_eventually_finePart_isFine
import Theorems.Thm_GroundTheory_Automorphic_finProj_mem_span
import Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le


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
theorem _root_.solution [μ.WeaklyRegular] (y : Lp ℂ 2 μ) :
    Tendsto (fun V => (finePart V).avgProj μ y) (fineFilter X) (𝓝 y) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨f, hf⟩ := (ContinuousMap.toLp_denseRange (E := ℂ) (μ := μ) (𝕜 := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).exists_dist_lt y (half_pos hε)
  set C : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hC : 0 ≤ C := by positivity
  set δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by positivity
  have hW := CompactSpace.uniformContinuous_of_continuous f.continuous (Metric.dist_mem_uniformity hδ)
  filter_upwards [eventually_finePart_isFine hW] with V hV
  set F := ContinuousMap.toLp (E := ℂ) 2 μ ℂ f
  set P := (finePart V).avgProj μ
  have h1 : ‖F - P F‖ ≤ C * δ := by
    refine norm_toLp_sub_avgProj_le μ _ hV f hδ.le fun x y hxy => ?_
    rw [← dist_eq_norm]
    exact (show dist (f x) (f y) < δ from hxy).le
  have h2 : ‖y - P y‖ ≤ ‖y - P F‖ :=
    norm_sub_finProj_le ((finePart V).orthonormal_avgVec μ) y (finProj_mem_span _ F)
  have h3 : C * δ < ε / 2 := by
    have : C * δ = ε / 2 * (C / (C + 1)) := by simp only [δ]; field_simp
    rw [this]
    have : C / (C + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one C)
    nlinarith
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖y - P y‖ ≤ ‖y - P F‖ := h2
    _ = ‖(y - F) + (F - P F)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖y - F‖ + ‖F - P F‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [← dist_eq_norm]
        exact add_lt_add_of_lt_of_le hf (h1.trans h3.le)
    _ = ε := add_halves ε
end GroundTheory.Automorphic
