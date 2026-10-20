-- Prove2me | solution 2 for OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:15:12.264501+00:00
-- url     : https://prove2.me/submissions/34e0b842-08cf-4503-8ad9-cfbf1e8f4b96

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalOrthogonality.lean:L22-L39
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalOrthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem stage_coord_zero (n j : ℕ) (x : M) (a : BlockLabel n)
    (hj : j ≠ stageIndex a) : stage n j x a = 0 := by
  cases j with
  | zero =>
    cases a with
    | inl u => exact (hj rfl).elim
    | inr a => simp [stage, Wzero]
  | succ j =>
    simp only [stage]
    split_ifs with h
    · cases a with
      | inl u => cases u; exact W_at_zero n ⟨j,h⟩ x
      | inr a =>
        apply W_at_other
        intro he
        apply hj
        exact congrArg (fun k : Fin (n+1) => k.val+1) he
    · rfl

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set


theorem solution : type_of% @_root_.OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero := @_root_.OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero
