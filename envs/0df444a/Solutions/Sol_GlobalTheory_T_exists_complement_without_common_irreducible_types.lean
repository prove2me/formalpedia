-- Prove2me | solution 1 for GlobalTheory.T.exists_complement_without_common_irreducible_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:17.458259+00:00
-- url     : https://prove2.me/submissions/32891bd2-f08e-410b-91a7-b76f4c68019c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypesStatement
import Theorems.Thm_GlobalTheory_TypeComplement_exists_typeComplement


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
theorem _root_.solution : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  first | exact @GlobalTheory.TypeComplement.exists_typeComplement | exact GlobalTheory.TypeComplement.exists_typeComplement | (intros; apply GlobalTheory.TypeComplement.exists_typeComplement <;> assumption)
end _root_.GlobalTheory.T
