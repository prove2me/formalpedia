-- Prove2me | solution 1 for GlobalTheory.T.finsum_doubleCoset_regroup_commutative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:27.929145+00:00
-- url     : https://prove2.me/submissions/11bdbe5f-8ecd-49e7-a804-a65863971959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetRegroupCommutative
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetRegroupCommutativeStatement
import Theorems.Thm_GlobalTheory_finsum_doubleCoset_regroup


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
theorem _root_.solution : ∀ (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → C ≤ T → (∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) → (∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) → ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  first | exact @GlobalTheory.finsum_doubleCoset_regroup | exact GlobalTheory.finsum_doubleCoset_regroup | (intros; apply GlobalTheory.finsum_doubleCoset_regroup <;> assumption)
end _root_.GlobalTheory.T
