-- Prove2me | solution 1 for GlobalTheory.PClassAlg.diag_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:12.301902+00:00
-- url     : https://prove2.me/submissions/9ded024a-5762-4fbd-8b0f-9171fd81bc73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi
import Theorems.Thm_GlobalTheory_PClassAlg_shape_aa

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
open GlobalTheory GlobalTheory.PClassAlg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.PClassAlg
theorem _root_.solution (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toBlocks₂₂]
  · simp [toBlocks₂₂, diagonal_apply_ne _ h, shape_aa B h1 h2 i j h]
end GlobalTheory.PClassAlg
