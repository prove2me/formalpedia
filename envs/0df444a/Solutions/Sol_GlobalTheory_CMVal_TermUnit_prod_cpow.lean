-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.prod_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:21.838841+00:00
-- url     : https://prove2.me/submissions/d2a274a5-87d7-4c9f-b93c-d8142c3b5e1e

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (z : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ z = ((∏ j ∈ t, f j : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]
end GlobalTheory.CMVal.TermUnit
