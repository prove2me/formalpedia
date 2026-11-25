-- Prove2me | solution 1 for GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:30.99449+00:00
-- url     : https://prove2.me/submissions/652d6ee9-bb47-490a-9178-7dbc27cb39ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlatStatement
import Theorems.Thm_GlobalTheory_exists_eq_algebraMap_of_forall_ringHom_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ → Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) → ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  first | exact @GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | exact GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | (intros; apply GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq <;> assumption)
end _root_.GlobalTheory.T
