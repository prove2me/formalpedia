-- Prove2me | solution 1 for GlobalTheory.InertZeta.prod_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:08.256805+00:00
-- url     : https://prove2.me/submissions/ebf55941-d4ea-42ac-b9e2-a99954ec16a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]
end GlobalTheory.InertZeta
