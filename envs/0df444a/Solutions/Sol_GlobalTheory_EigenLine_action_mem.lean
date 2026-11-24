-- Prove2me | solution 1 for GlobalTheory.EigenLine.action_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:09.348946+00:00
-- url     : https://prove2.me/submissions/9e797195-dc44-4ef1-aa4d-5ba62c09ce8d

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
theorem _root_.solution (ρ : O →+* Module.End K L) (P : Submodule K L)
    (hP : ∀ a, ∀ x ∈ P, ρ a x ∈ P) (t : K ⊗[ℤ] O) : ∀ x ∈ P, tensorAction ρ t x ∈ P := by
  induction t using TensorProduct.induction_on with
  | zero => intro x _; simp
  | tmul r a => intro x hx; rw [tensorAction_tmul]; exact P.smul_mem _ (hP a x hx)
  | add s t hs ht =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem (hs x hx) (ht x hx)
end GlobalTheory.EigenLine
