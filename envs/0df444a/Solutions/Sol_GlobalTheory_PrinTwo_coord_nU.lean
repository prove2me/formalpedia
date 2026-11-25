-- Prove2me | solution 1 for GlobalTheory.PrinTwo.coord_nU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:40.761385+00:00
-- url     : https://prove2.me/submissions/311027ca-f3ea-4493-8545-74bb944ad658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_nU_mul_nU
import Theorems.Thm_GlobalTheory_PrinTwo_ev_act
import Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
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
attribute [local simp] GlobalTheory.PrinTwo.evL_apply
attribute [local simp] GlobalTheory.PrinTwo.coordL_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (y x : k) :
    coord (psRep μ₁ μ₂ (nU y) f) x = coord f (x + y) := by
  simp only [coord, ev_act, mul_assoc, nU_mul_nU]
end GlobalTheory.PrinTwo
