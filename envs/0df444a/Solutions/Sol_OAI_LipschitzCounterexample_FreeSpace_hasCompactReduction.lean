-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:02:51.21771+00:00
-- url     : https://prove2.me/submissions/c4ce28ee-3f9a-4c44-89e8-677ef46927cc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactReduction.lean:L116-L130
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_bounded_compact_reduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_bounded_weak_approx

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactReduction ----
namespace OAI

universe uM

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

theorem hasCompactReduction [CompleteSpace M] :
    ∀ μ : ℕ → Space M, WeakSequences.WeakNull μ → ∀ τ : ℝ, 0 < τ →
      ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
        ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ := by
  intro μ hw τ hτ
  obtain ⟨R,v,hv,hsupp,herr⟩ := bounded_weak_approx hw (half_pos hτ)
  obtain ⟨K,hK,hzero,happrox⟩ := bounded_compact_reduction hv hsupp (half_pos hτ)
  refine ⟨K,hK,hzero,fun i => ?_⟩
  obtain ⟨ν,hν,hνerr⟩ := happrox i
  refine ⟨ν,hν,?_⟩
  have h : ‖μ i-ν‖ ≤ ‖μ i-v i‖+‖v i-ν‖ := by
    rw [show μ i-ν = (μ i-v i)+(v i-ν) by abel]
    exact norm_add_le _ _
  have h₁ := herr i
  linarith

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
open scoped NNReal Topology
open Filter Set LocalizedLinearization


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction.{uM}
