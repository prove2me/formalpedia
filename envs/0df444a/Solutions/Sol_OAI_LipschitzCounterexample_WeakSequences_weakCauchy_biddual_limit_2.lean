-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.weakCauchy_biddual_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:20:41.364235+00:00
-- url     : https://prove2.me/submissions/5851059e-fe26-43a3-9b9b-3652320903ca

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean:L151-L166
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.weakCauchy_biddual_limit. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.WeakSums ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uG

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakCauchy.bounded {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => NormedSpace.inclusionInDoubleDual ℝ E (u n))
    (fun f => by
      obtain ⟨C, hC⟩ := (hu f).isBounded_range.exists_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩)
  refine ⟨C, fun n => ?_⟩
  have h := (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (u n)
  exact h ▸ hC n

variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

end WeakSequences

namespace WeakSequences
open Filter Topology
open scoped NNReal ENNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open NullSequences

end WeakSequences

end LipschitzCounterexample
end

end OAI

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

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weakCauchy_biddual_limit {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)) := by
  classical
  choose a ha using fun f : E →L[ℝ] ℝ => cauchySeq_tendsto_of_complete (hu f)
  let L : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ := {
    toFun := a
    map_add' := fun f g => tendsto_nhds_unique (ha (f+g)) ((ha f).add (ha g))
    map_smul' := fun c f => tendsto_nhds_unique (ha (c • f)) ((ha f).const_smul c) }
  obtain ⟨C,hC⟩ := hu.bounded
  have hbound (f : E →L[ℝ] ℝ) : ‖L f‖ ≤ C*‖f‖ := by
    apply le_of_tendsto (ha f).norm
    apply Eventually.of_forall
    intro n
    exact (f.le_opNorm (u n)).trans (by nlinarith [norm_nonneg f,hC n])
  exact ⟨L.mkContinuous C hbound,ha⟩

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Topology


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.weakCauchy_biddual_limit.{uE} := @_root_.OAI.LipschitzCounterexample.WeakSequences.weakCauchy_biddual_limit.{uE}
