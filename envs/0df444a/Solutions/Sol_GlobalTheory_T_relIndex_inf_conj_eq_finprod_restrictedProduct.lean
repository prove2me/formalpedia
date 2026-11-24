-- Prove2me | solution 1 for GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:45.835804+00:00
-- url     : https://prove2.me/submissions/3b13179f-8080-4eb8-92fa-c5bff3f3c8d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexInfConjEqFinprodRestrictedProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexInfConjEqFinprodRestrictedProductStatement
import Theorems.Thm_GlobalTheory_relIndex_inf_conj_eq_finprod_of_restricted_product


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i) → (∀ i, CH i ≤ TH i) → (∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧ (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0) → (∀ᶠ i in cofinite, CH i ≤ KH i) → (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C = ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  first | exact @GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | exact GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | (intros; apply GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product <;> assumption)
end _root_.GlobalTheory.T
