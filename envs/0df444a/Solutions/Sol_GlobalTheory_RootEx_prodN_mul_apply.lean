-- Prove2me | solution 1 for GlobalTheory.RootEx.prodN_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:29.669736+00:00
-- url     : https://prove2.me/submissions/ac4c0f17-0779-4f45-aa33-a78ea9e10a1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdNBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx
theorem _root_.solution {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs
end GlobalTheory.RootEx
