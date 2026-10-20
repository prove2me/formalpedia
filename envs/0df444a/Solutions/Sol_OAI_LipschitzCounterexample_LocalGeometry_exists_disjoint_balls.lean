-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:24:08.623333+00:00
-- url     : https://prove2.me/submissions/293a5f9e-da3c-4a3a-8359-bb29ed6b79a9

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalGeometry
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]


theorem solution (z : I → M) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun j k => Disjoint (Metric.ball (z j) r) (Metric.ball (z k) r)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI => exact ⟨1, one_pos, fun j => isEmptyElim j⟩
  | inr hI =>
    let g : I × I → ℝ := fun p => if p.1 = p.2 then 1 else dist (z p.1) (z p.2) / 2
    obtain ⟨p0, hp0⟩ := Finite.exists_min g
    have gpos : ∀ p, 0 < g p := by
      intro p
      by_cases h : p.1 = p.2
      · simp [g, h]
      · simp only [g, h, if_false]
        have := dist_pos.mpr (fun he => h (hz he))
        positivity
    refine ⟨g p0, gpos p0, fun j k hjk => ?_⟩
    show Disjoint _ _
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hle := hp0 (j, k)
    simp only [g, hjk, if_false] at hle
    rw [Metric.mem_ball] at hx1 hx2
    have := dist_triangle_left (z j) (z k) x
    linarith

