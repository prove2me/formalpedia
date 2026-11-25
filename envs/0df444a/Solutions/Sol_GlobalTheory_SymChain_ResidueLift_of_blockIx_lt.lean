-- Prove2me | solution 1 for GlobalTheory.SymChain.ResidueLift.of_blockIx_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:06.620266+00:00
-- url     : https://prove2.me/submissions/b060f488-020c-4e16-85bb-0bf9a2f75473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc

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
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ResidueLift
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.SymChain.ResidueLift
theorem _root_.solution {a b : n ⊕ Fin c} (h : blockIx p b < blockIx p a) :
    lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) ∧ a ≠ b := by
  rcases a with a | a <;> rcases b with b | b <;> simp only [blockIx, Sum.elim_inl, Sum.elim_inr] at h
  · omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, fun e => ?_⟩
    · simp only [lev, Sum.elim_inr]; omega
    · cases e; omega
end GlobalTheory.SymChain.ResidueLift
