-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:33:58.641185+00:00
-- url     : https://prove2.me/submissions/c2261a82-f128-4ba1-a59c-6dce72c53287

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean:L163-L188
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactLipschitz ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem exists_disjoint_balls (z : I → M) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun j k => Disjoint (Metric.ball (z j) r) (Metric.ball (z k) r)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi => exact ⟨1,by norm_num,fun j => isEmptyElim j⟩
  | inr hi =>
    let d : I × I → ℝ := fun p => if p.1 = p.2 then 1 else dist (z p.1) (z p.2)/3
    have hd (p : I × I) : 0 < d p := by
      dsimp [d]
      split_ifs with hp
      · norm_num
      · exact div_pos (dist_pos.mpr (fun h => hp (hz h))) (by norm_num)
    let r : ℝ := Finset.univ.inf' Finset.univ_nonempty d
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (fun p _ => hd p)
    refine ⟨r,hr,?_⟩
    intro j k hjk
    have hrd : r ≤ dist (z j) (z k)/3 := by
      have ht : r ≤ d (j,k) := Finset.inf'_le _ (Finset.mem_univ (j,k))
      simpa only [d,ite_eq_right hjk] using ht
    apply Set.disjoint_left.mpr
    intro x hx hy
    have ht := dist_triangle (z j) x (z k)
    rw [dist_comm (z j) x] at ht
    change dist x (z j) < r at hx
    change dist x (z k) < r at hy
    linarith
end LipschitzCounterexample.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalGeometry
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set


theorem solution.{uM,uI} : type_of% @_root_.OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls.{uM,uI} := @_root_.OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls.{uM,uI}
