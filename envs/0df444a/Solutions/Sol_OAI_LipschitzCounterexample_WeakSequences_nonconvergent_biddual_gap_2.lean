-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.nonconvergent_biddual_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:38:25.000243+00:00
-- url     : https://prove2.me/submissions/80abead2-7e57-4a59-a4a5-bcedd01737ae

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/BidualSeparation.lean:L89-L111
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.nonconvergent_biddual_gap. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_weakCauchy_biddual_limit

-- ---- from OAI.Analysis.LipschitzEquivalence.BidualSeparation ----
namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped NNReal Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nonconvergent_biddual_gap [CompleteSpace E] {u : ℕ → E} (hu : WeakCauchy u)
    (hno : ¬ ∃ x : E, ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    ∃ (φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) (d : ℝ), 0 < d ∧
      (∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f))) ∧
      ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖ := by
  obtain ⟨φ,hφ⟩ := weakCauchy_biddual_limit hu
  let I : E →ₗᵢ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := NormedSpace.inclusionInDoubleDualLi ℝ
  have hnot : φ ∉ Set.range I := by
    rintro ⟨x,hx⟩
    apply hno
    refine ⟨x,fun f => ?_⟩
    simpa [← hx,I,NormedSpace.inclusionInDoubleDualLi,NormedSpace.inclusionInDoubleDual] using hφ f
  have hI : Isometry (I : E → ((E →L[ℝ] ℝ) →L[ℝ] ℝ)) := I.isometry
  have hclosed : IsClosed (Set.range I) := hI.isClosedEmbedding.isClosed_range
  have hnot' : φ ∉ closure (Set.range I) := by rwa [hclosed.closure_eq]
  rw [@Metric.mem_closure_iff ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance] at hnot'
  push Not at hnot'
  obtain ⟨d,hd,hgap⟩ := hnot'
  refine ⟨φ,d,hd,hφ,fun x => ?_⟩
  have h := hgap (I x) ⟨x,rfl⟩
  rw [show dist φ (I x) = ‖φ-I x‖ from
    @dist_eq_norm ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance φ (I x)] at h
  exact h

end LipschitzCounterexample.WeakSequences
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open scoped NNReal Topology BigOperators
open Filter Set


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.nonconvergent_biddual_gap.{uE} := @_root_.OAI.LipschitzCounterexample.WeakSequences.nonconvergent_biddual_gap.{uE}
