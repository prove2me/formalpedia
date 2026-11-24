-- Prove2me | solution 1 for GlobalTheory.EigenLine.twist_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:12.102398+00:00
-- url     : https://prove2.me/submissions/de376450-66ce-4178-8753-5d5d6fb92dba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]
namespace GlobalTheory.EigenLine
theorem _root_.solution (c : O →+* O) (hcc : ∀ a, c (c a) = a) (t : K ⊗[ℤ] O) :
    twist c (twist c t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hcc]
  | add s t hs ht => simp only [map_add, hs, ht]
end GlobalTheory.EigenLine
