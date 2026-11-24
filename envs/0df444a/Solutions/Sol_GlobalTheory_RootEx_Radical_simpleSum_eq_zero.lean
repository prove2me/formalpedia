-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.simpleSum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:50.368737+00:00
-- url     : https://prove2.me/submissions/f7a2a64e-4828-405a-aa12-9333f021cddf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution {g : GL (n ⊕ Fin c) k}
    (h : ∀ i j, g.val (Sum.inr i) (Sum.inr j) = (1 : Matrix (Fin c) (Fin c) k) i j) :
    simpleSum g = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rw [h, Matrix.one_apply_ne]
    rintro rfl
    omega
  · rfl
end GlobalTheory.RootEx.Radical
