-- Prove2me | solution 1 for GlobalTheory.PrinTwo.tD_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:10.092296+00:00
-- url     : https://prove2.me/submissions/85f353d6-422d-4c08-9349-dff856e07b88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_wE
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution (a : kˣ) : (tD a a⁻¹ : GL (Fin (1 + 1)) k) =
    nU (a : k) * nL (-((a⁻¹ : kˣ) : k)) * nU (a : k) * (nU (-1) * nL 1 * nU (-1)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
end GlobalTheory.PrinTwo
