-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.wsc_of_compact_supported
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:22:43.24447+00:00
-- url     : https://prove2.me/submissions/955cb764-9fd3-485d-bd73-59c291ba2374

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean:L206-L221
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.wsc_of_compact_supported. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_bounded_cauchy_approx
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_bounded_cauchy_compact_reduction
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_weakCauchy_biddual_limit

-- ---- from OAI.Analysis.LipschitzEquivalence.CauchyReduction ----
namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem cauchy_compact_reduction [CompleteSpace M] {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → Space M, WeakSequences.WeakCauchy ν ∧
        (∀ i, ν i ∈ supported K) ∧ ∀ i, ‖μ i-ν i‖ < τ := by
  obtain ⟨R,v,hv,hsupp,herr⟩ := bounded_cauchy_approx hw (half_pos hτ)
  obtain ⟨K,hK,hzero,ν,hν,hmem,happrox⟩ :=
    bounded_cauchy_compact_reduction hv hsupp (half_pos hτ)
  refine ⟨K,hK,hzero,ν,hν,hmem,fun i => ?_⟩
  have h : ‖μ i-ν i‖ ≤ ‖μ i-v i‖+‖v i-ν i‖ := by
    rw [show μ i-ν i = (μ i-v i)+(v i-ν i) by abel]
    exact norm_add_le _ _
  have h₁ := herr i
  have h₂ := happrox i
  linarith

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem wsc_of_uniform_weak_approx [CompleteSpace E] {u : ℕ → E} (hu : WeakCauchy u)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → E, ∃ x : E,
      (∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (v n)) atTop (𝓝 (f x))) ∧
      ∀ n, ‖u n-v n‖ < ε) :
    ∃ x : E, ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by
  obtain ⟨φ,hφ⟩ := weakCauchy_biddual_limit hu
  let I : E →ₗᵢ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    NormedSpace.inclusionInDoubleDualLi (E := E) ℝ
  have hmem : φ ∈ closure (Set.range I) := by
    rw [@Metric.mem_closure_iff ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance]
    intro ε hε
    obtain ⟨v,x,hx,herr⟩ := happrox (ε/2) (half_pos hε)
    refine ⟨I x,⟨x,rfl⟩,?_⟩
    have hnorm : ‖φ-I x‖ ≤ ε/2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
      intro f
      change ‖φ f-f x‖ ≤ (ε/2)*‖f‖
      apply le_of_tendsto ((hφ f).sub (hx f)).norm
      apply Eventually.of_forall
      intro n
      rw [← map_sub]
      exact (f.le_opNorm _).trans (by nlinarith [norm_nonneg f,herr n])
    rw [show dist φ (I x) = ‖φ-I x‖ from
      @dist_eq_norm ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance φ (I x)]
    exact hnorm.trans_lt (by linarith)
  have hI : Isometry (I : E → ((E →L[ℝ] ℝ) →L[ℝ] ℝ)) := I.isometry
  have hclosed : IsClosed (Set.range I) := hI.isClosedEmbedding.isClosed_range
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x,hx⟩ := hmem
  refine ⟨x,fun f => ?_⟩
  simpa [← hx, I, NormedSpace.inclusionInDoubleDualLi, NormedSpace.inclusionInDoubleDual] using hφ f

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

theorem wsc_of_compact_supported
    (hcompact : ∀ K : Set M, IsCompact K → (0 : M) ∈ K →
      WeakSequences.WeakSequentiallyComplete (supported K)) :
    WeakSequences.WeakSequentiallyComplete (Space M) := by
  intro μ hμ
  apply WeakSequences.wsc_of_uniform_weak_approx hμ
  intro ε hε
  obtain ⟨K,hK,hzero,ν,hν,hmem,herr⟩ := cauchy_compact_reduction hμ hε
  let v : ℕ → supported K := fun n => ⟨ν n,hmem n⟩
  have hv : WeakSequences.WeakCauchy v := by
    intro f
    obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (supported K) f
    simpa only [← hg] using hν g
  obtain ⟨x,hx⟩ := hcompact K hK hzero v hv
  refine ⟨ν,(x : Space M),fun f => ?_,herr⟩
  exact hx (f.comp (supported K).subtypeL)

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Topology


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.wsc_of_compact_supported.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.wsc_of_compact_supported.{uM}
