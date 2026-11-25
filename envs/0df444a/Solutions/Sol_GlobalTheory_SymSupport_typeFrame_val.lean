-- Prove2me | solution 1 for GlobalTheory.SymSupport.typeFrame_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:11.861952+00:00
-- url     : https://prove2.me/submissions/19f57e6b-f924-4b3d-b351-a8190c76bd41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupport
theorem _root_.solution {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← fromBlocks_diagonal]; simp
end GlobalTheory.SymSupport
