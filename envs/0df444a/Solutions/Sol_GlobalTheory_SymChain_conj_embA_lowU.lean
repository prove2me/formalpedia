-- Prove2me | solution 1 for GlobalTheory.SymChain.conj_embA_lowU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:09.407671+00:00
-- url     : https://prove2.me/submissions/3cf86385-3f24-41c1-8be9-eb7e2be14587

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevel

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
namespace GlobalTheory.SymChain
theorem _root_.solution {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d : Fin c → kˣ)
    (C : Matrix (Fin c) n k) :
    embA n (GlobalTheory.SplitFlip.diagGL d) * lowU (diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C) *
      (embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ = lowU C := by
  apply Units.ext
  have hinv : ((embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ : GL (n ⊕ Fin c) k).val =
      fromBlocks 1 0 0 (diagonal fun i => (((d i)⁻¹ : kˣ) : k)) := by
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  change fromBlocks 1 0 0 (diagonal fun i => (d i : k)) * fromBlocks 1 0 _ 1 * _ = fromBlocks 1 0 C 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [← Matrix.mul_assoc, diagonal_mul_diagonal]
end GlobalTheory.SymChain
