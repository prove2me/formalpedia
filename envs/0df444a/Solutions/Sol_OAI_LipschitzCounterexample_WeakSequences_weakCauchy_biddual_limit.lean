-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.weakCauchy_biddual_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:16:01.412439+00:00
-- url     : https://prove2.me/submissions/1182b7dd-e5f9-4ffc-a3aa-436cbe120056

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uM uE
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem h50c_biddual_limit {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)) := by
  have hex : ∀ f : E →L[ℝ] ℝ, ∃ l, Tendsto (fun n => f (u n)) atTop (𝓝 l) :=
    fun f => cauchySeq_tendsto_of_complete (hu f)
  choose L hL using hex
  let g : ℕ → (E →L[ℝ] ℝ) →L[ℝ] ℝ := fun n => NormedSpace.inclusionInDoubleDual ℝ E (u n)
  have hpt : ∀ f, ∃ C, ∀ n, ‖g n f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (hL f))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  let Llin : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := fun f h => tendsto_nhds_unique (hL (f + h)) (by simpa using (hL f).add (hL h))
      map_smul' := fun c f => tendsto_nhds_unique (hL (c • f)) (by simpa using (hL f).const_mul c) }
  refine ⟨Llin.mkContinuous C' (fun f => ?_), fun f => hL f⟩
  have hb : ∀ n, ‖f (u n)‖ ≤ C' * ‖f‖ := by
    intro n
    have := (g n).le_opNorm f
    exact le_trans this (mul_le_mul_of_nonneg_right (hC' n) (norm_nonneg _))
  exact le_of_tendsto (hL f).norm (Eventually.of_forall hb)

theorem solution {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)) := by
  exact h50c_biddual_limit hu

