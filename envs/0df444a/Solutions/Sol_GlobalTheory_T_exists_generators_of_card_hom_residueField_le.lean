-- Prove2me | solution 1 for GlobalTheory.T.exists_generators_of_card_hom_residueField_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:22.662461+00:00
-- url     : https://prove2.me/submissions/806bfcef-63b6-4134-b1f2-e28e2e69fc91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLeStatement
import Theorems.Thm_GlobalTheory_exists_span_eq_top_of_card_hom_residueField_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  first | exact @GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | exact GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | (intros; apply GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le <;> assumption)
end _root_.GlobalTheory.T
