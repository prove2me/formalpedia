-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.mul_apply_of_inN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:32.367821+00:00
-- url     : https://prove2.me/submissions/39ff7cad-86e3-44e4-9116-bdc7ec4af3ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) {m : Type*}
    (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (h.val * x) r s = x r s + ∑ r', if lev p r < lev p r' then h.val r r' * x r' s else 0 := by
  have h1 : x r s = ∑ r', (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r r' * x r' s := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r' _ => ?_
  split_ifs with hl
  · rw [Matrix.one_apply_ne, zero_mul, zero_add]
    rintro rfl
    exact lt_irrefl _ hl
  · rw [hh r r' (not_lt.1 hl), add_zero]
end GlobalTheory.RootEx.TargetUnip
