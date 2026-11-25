-- Prove2me | solution 1 for GlobalTheory.SymChain.not_freeIx_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:29.815195+00:00
-- url     : https://prove2.me/submissions/ca092413-eac8-4e44-bb35-38a85fe4efd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
omit [Fintype t] [DecidableEq t]
namespace GlobalTheory.SymChain
theorem _root_.solution (ρ : ℕ) {l j : ℕ} (a : Ix (Fin κ ⊕ Fin (l + 1)) t j) :
    ¬ FreeIx ρ a (.inl (.inr 0)) := by
  rcases a with (i | i) | p <;> simp [FreeIx, FreeTop]
end GlobalTheory.SymChain
