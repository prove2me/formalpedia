-- Prove2me | solution 1 for GlobalTheory.FunObj.keptPart_joinVars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:21.889862+00:00
-- url     : https://prove2.me/submissions/9afea089-e6c1-4afb-9cb8-f6234ddcf24a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
omit [Field k]
namespace GlobalTheory.FunObj
theorem _root_.solution (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) : keptPart (joinVars (w, f)) = w := by
  funext rs
  exact congrArg (Sum.elim w f) ((stepVarEquiv n c n').symm_apply_apply (.inl rs))
end GlobalTheory.FunObj
