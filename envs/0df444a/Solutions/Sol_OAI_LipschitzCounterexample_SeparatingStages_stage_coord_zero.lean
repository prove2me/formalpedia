-- Prove2me | solution 1 for OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:28:50.262922+00:00
-- url     : https://prove2.me/submissions/801094fb-aec2-4e63-a94d-57fae930b4ea

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set


theorem solution (n j : ℕ) (x : M) (a : BlockLabel n)
    (hj : j ≠ stageIndex a) : stage n j x a = 0 := by
  rcases a with u | ⟨l, b⟩
  · cases j with
    | zero => exact absurd rfl hj
    | succ k =>
      simp only [stage]
      split_ifs with hk
      · exact W_at_zero n ⟨k, hk⟩ x
      · rfl
  · cases j with
    | zero => simp [stage, Wzero]
    | succ k =>
      simp only [stage]
      split_ifs with hk
      · apply W_at_other
        intro he
        apply hj
        simp [stageIndex, ← he]
      · rfl

