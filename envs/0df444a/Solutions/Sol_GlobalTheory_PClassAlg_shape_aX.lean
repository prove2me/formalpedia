-- Prove2me | solution 1 for GlobalTheory.PClassAlg.shape_aX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:23:19.461851+00:00
-- url     : https://prove2.me/submissions/1a15127a-265f-40b4-ab6f-78c228f6e961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi

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
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (l : Fin c) (y : n) :
    B (Sum.inr l) (Sum.inl y) = 0 := by
  by_cases h : l.val + 1 < p
  · apply h2
    show OrderDual.toDual (lev p (Sum.inl y : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr l : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega
end GlobalTheory.PClassAlg
