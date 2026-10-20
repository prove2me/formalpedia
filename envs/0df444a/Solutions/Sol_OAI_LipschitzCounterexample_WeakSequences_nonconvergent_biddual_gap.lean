-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.nonconvergent_biddual_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:20:22.499277+00:00
-- url     : https://prove2.me/submissions/a839be19-c707-4dcd-9049-a7d172b7933e

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE
open scoped NNReal Topology BigOperators
open Filter Set
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

theorem solution [CompleteSpace E] {u : ℕ → E} (hu : WeakCauchy u)
    (hno : ¬ ∃ x : E, ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    ∃ (φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) (d : ℝ), 0 < d ∧
      (∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f))) ∧
      ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖ := by
  obtain ⟨φ, hφ⟩ := h50c_biddual_limit hu
  set S := Set.range (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)) with hS
  have hcl : IsClosed S :=
    ((NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)).isometry.isUniformInducing.isComplete_range).isClosed
  have hnot : φ ∉ S := by
    rintro ⟨x, hx⟩
    apply hno
    refine ⟨x, fun f => ?_⟩
    have : φ f = f x := by rw [← hx]; rfl
    rw [← this]; exact hφ f
  have hne : S.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hd := (hcl.notMem_iff_infDist_pos hne).mp hnot
  refine ⟨φ, Metric.infDist φ S, hd, hφ, fun x => ?_⟩
  have hmem : (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)) x ∈ S := ⟨x, rfl⟩
  have := Metric.infDist_le_dist_of_mem (x := φ) hmem
  exact this.trans_eq (@dist_eq_norm ((E →L[ℝ] ℝ) →L[ℝ] ℝ) _ φ (NormedSpace.inclusionInDoubleDual ℝ E x))

