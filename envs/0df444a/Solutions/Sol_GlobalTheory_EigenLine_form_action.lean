-- Prove2me | solution 1 for GlobalTheory.EigenLine.form_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:11.455811+00:00
-- url     : https://prove2.me/submissions/06712484-f391-4810-a2e3-6b286cf54f70

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
theorem _root_.solution (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y) (t : K ⊗[ℤ] O) (x y : L) :
    B x (tensorAction ρ t y) = B (tensorAction ρ (twist c t) x) y := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hadj]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
end GlobalTheory.EigenLine
