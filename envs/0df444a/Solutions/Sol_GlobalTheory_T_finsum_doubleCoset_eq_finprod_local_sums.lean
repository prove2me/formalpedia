-- Prove2me | solution 1 for GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:34.694801+00:00
-- url     : https://prove2.me/submissions/0c0b99ce-1e3a-469d-84b7-b5ffdf2b8635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSumsStatement
import Theorems.Thm_GlobalTheory_DoubleCosetEuler_finsum_doubleCoset_eq_finprod_local


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
theorem _root_.solution : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  first | exact @GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | exact GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | (intros; apply GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local <;> assumption)
end _root_.GlobalTheory.T
