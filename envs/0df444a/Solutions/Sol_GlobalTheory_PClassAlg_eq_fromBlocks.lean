-- Prove2me | solution 1 for GlobalTheory.PClassAlg.eq_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:35.155162+00:00
-- url     : https://prove2.me/submissions/8a001b1d-95d8-43f2-901d-d0b701bb817b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi
import Theorems.Thm_GlobalTheory_PClassAlg_shape_aX

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
theorem _root_.solution (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  congr 1
  ext l y; exact shape_aX hp B h1 h2 l y
end GlobalTheory.PClassAlg
