-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isSplitting_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:07:50.867175+00:00
-- url     : https://prove2.me/submissions/0e18cf78-286e-45ca-a655-d136d4081232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_field
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isUnit_discr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution (E : Type*) [Field E] [NumberField E] :
    IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
  classical
  obtain ⟨b⟩ := nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  exact isSplitting_of_isUnit_discr b (det_sq_eq_discr_of_field Function.injective_id b)
    (by simpa using NumberField.discr_ne_zero E)
end GlobalTheory.EigenSplit
