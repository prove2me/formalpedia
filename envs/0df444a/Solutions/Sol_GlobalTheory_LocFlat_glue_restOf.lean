-- Prove2me | solution 1 for GlobalTheory.LocFlat.glue_restOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:32.5316+00:00
-- url     : https://prove2.me/submissions/9b803156-4d0f-4768-968f-9d68e1b15144

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
theorem _root_.solution {X : Type} (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool)
    (E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X)
    (hER : ∀ z r s, rd r s = true → E (R z) r s = z r s) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    glue rd E (R z, restOf rd z) = z := by
  ext r s
  cases h : rd r s
  · simp [glue, restOf, h]
  · simp [glue, h, hER z r s h]
end GlobalTheory.LocFlat
