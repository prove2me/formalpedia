-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.colE_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:18.130918+00:00
-- url     : https://prove2.me/submissions/5ae0a772-45b8-4f06-b52d-4e0c78600386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {m : Type} (q : Fin c) (β : n → k) (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * x) r s =
      x r s + Sum.elim (fun r' => -(β r' * x (Sum.inr q) s)) 0 r := by
  rcases r with r | r <;>
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj, neg_ite, -Matrix.coe_units_inv]
end GlobalTheory.RootEx.Exchange
