-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_le_of_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:50.039984+00:00
-- url     : https://prove2.me/submissions/9c2e28ec-983b-4d17-8c12-f13a920a0ea1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_lt_top_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_ofSchwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_ofSchwartz_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_denseRange_ofSchwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) {s t C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(E, ℂ), sob t (T φ) ≤ ENNReal.ofReal C * sob s (φ : 𝓢'(E, ℂ))) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) : sob t (T u) ≤ ENNReal.ofReal C * sob s u := by
  obtain ⟨v, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu

  have hS : ∀ φ : 𝓢(E, ℂ), ∃ w : SobolevSpace E ℂ t,
      SobolevSpace.toDistribution w = T φ ∧ ‖w‖ ≤ C * ‖SobolevSpace.ofSchwartz s φ‖ := by
    intro φ
    have h1 := h φ
    rw [sob_ofSchwartz] at h1
    have hmem : MemSobolev t 2 (T φ) :=
      sob_lt_top_iff.1 (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top))
    refine ⟨SobolevSpace.mk _ hmem, rfl, ?_⟩
    rw [sob_of_mem hmem, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  choose S hST hSn using hS
  have hSsub : ∀ φ ψ : 𝓢(E, ℂ), S φ - S ψ = S (φ - ψ) := by
    intro φ ψ
    apply SobolevSpace.toDistribution_injective
    rw [SobolevSpace.toDistribution_sub, hST, hST, hST, map_sub, map_sub]
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1
    (SobolevSpace.denseRange_ofSchwartz (E := E) (F := ℂ) (s := s) v)
  choose φ hφ using hx
  set w : ℕ → SobolevSpace E ℂ t := fun n ↦ S (φ n)
  have hdist : ∀ m n, dist (w m) (w n) ≤ C * dist (x m) (x n) := by
    intro m n
    rw [dist_eq_norm, dist_eq_norm, hSsub, ← hφ m, ← hφ n, ← ofSchwartz_sub]
    exact hSn _
  have hcauchy : CauchySeq w := by
    have hxc := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hxc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hxc (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    calc dist (w m) (w n) ≤ C * dist (x m) (x n) := hdist m n
      _ ≤ C * (ε / (C + 1)) := by gcongr; exact (hN m hm n hn).le
      _ < ε := by
          rw [mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨w₀, hw₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hT : SobolevSpace.toDistribution w₀ = T (SobolevSpace.toDistribution v) := by
    have h1 := ((SobolevSpace.toDistributionCLM E ℂ t).continuous.tendsto w₀).comp hw₀
    simp only [Function.comp_def, SobolevSpace.toDistributionCLM_apply] at h1
    have h2 : Filter.Tendsto (fun n ↦ SobolevSpace.toDistribution (w n)) Filter.atTop
        (nhds (T (SobolevSpace.toDistribution v))) := by
      have h3 := (T.continuous.tendsto _).comp
        (((SobolevSpace.toDistributionCLM E ℂ s).continuous.tendsto v).comp hlim)
      simp only [Function.comp_def, SobolevSpace.toDistributionCLM_apply] at h3
      refine h3.congr fun n ↦ ?_
      simp only [w, hST, ← hφ n, SobolevSpace.toDistribution_ofSchwartz]
    exact tendsto_nhds_unique h1 h2
  rw [← hT, sob_toDistribution, sob_toDistribution, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hn : Filter.Tendsto (fun n ↦ ‖w n‖) Filter.atTop (nhds ‖w₀‖) := hw₀.norm
  have hm : Filter.Tendsto (fun n ↦ C * ‖x n‖) Filter.atTop (nhds (C * ‖v‖)) :=
    hlim.norm.const_mul C
  refine le_of_tendsto_of_tendsto hn hm (Filter.Eventually.of_forall fun n ↦ ?_)
  simp only [w]
  rw [← hφ n]
  exact hSn _
end GroundTheory.Automorphic.Sobolev
