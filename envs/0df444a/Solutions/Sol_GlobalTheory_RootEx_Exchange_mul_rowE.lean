-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.mul_rowE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:18.207477+00:00
-- url     : https://prove2.me/submissions/17a0270c-6727-4371-bd96-309aa6bfd0e2

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
theorem _root_.solution {m : Type} (q : Fin c) (u : n → k) (x : Matrix m (n ⊕ Fin c) k) (r : m) (s : n ⊕ Fin c) :
    (x * (rowE c (q.val + 1) u).val) r s = x r s + Sum.elim (fun s' => x r (Sum.inr q) * u s') 0 s := by
  rcases s with s | s <;>
    simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]
end GlobalTheory.RootEx.Exchange
