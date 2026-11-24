-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.col_colE_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:48.930562+00:00
-- url     : https://prove2.me/submissions/018f1fd3-8f26-4041-8582-d4a661109286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul_affPt

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (q : Fin c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    (fun r => -(((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q.val + 1) x₀ e)
      (Sum.inl r) (Sum.inr q.castSucc)) = β := by
  classical
  funext s
  rw [colE_inv_mul_affPt]
  simp [mat, basePt, ext0, Free, gCol]
end GlobalTheory.RootEx.Exchange
