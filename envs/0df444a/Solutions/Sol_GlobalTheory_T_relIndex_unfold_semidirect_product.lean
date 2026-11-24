-- Prove2me | solution 1 for GlobalTheory.T.relIndex_unfold_semidirect_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:46.515571+00:00
-- url     : https://prove2.me/submissions/5baae3dc-0c2c-4055-a173-72d9c2426809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProductStatement
import Theorems.Thm_GlobalTheory_relIndex_unfold_semidirect


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
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  first | exact @GlobalTheory.relIndex_unfold_semidirect | exact GlobalTheory.relIndex_unfold_semidirect | (intros; apply GlobalTheory.relIndex_unfold_semidirect <;> assumption)
end _root_.GlobalTheory.T
