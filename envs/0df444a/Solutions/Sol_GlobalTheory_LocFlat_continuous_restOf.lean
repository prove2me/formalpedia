-- Prove2me | solution 1 for GlobalTheory.LocFlat.continuous_restOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:28.054523+00:00
-- url     : https://prove2.me/submissions/1afd1a5d-123c-48b9-baed-25c04f7567e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LocFlat
theorem _root_.solution (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) :
    Continuous (restOf (k := k) (n := n) (n' := n') rd) := by
  refine continuous_matrix fun r s => ?_
  cases h : rd r s
  · simp only [restOf, Matrix.of_apply, h, Bool.false_eq_true, ↓reduceIte]; fun_prop
  · simp only [restOf, Matrix.of_apply, h]; exact continuous_const
end GlobalTheory.LocFlat
