-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.mul_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:37.772822+00:00
-- url     : https://prove2.me/submissions/cbad6d8e-776a-4bad-897c-7c58af733649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_frameGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {a c b : ℕ}
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  rw [frameGL_val, reindex_apply, reindex_apply, ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _)]
  simp
end GlobalTheory.FunObj.FiniteSupport
