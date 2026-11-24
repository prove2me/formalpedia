-- Prove2me | solution 1 for GlobalTheory.finsum_finprod_mul_two_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:41.544303+00:00
-- url     : https://prove2.me/submissions/699c9fec-3f7b-4620-a9a8-713ed34fadc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
import Theorems.Thm_GlobalTheory_LocalGrouping_finprod_finsum_eq
import Theorems.Thm_GlobalTheory_LocalGrouping_finsum_fibres_eq

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
open GlobalTheory
open Function
namespace GlobalTheory
theorem _root_.solution :
    ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R)
      (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) →
      (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) →
      (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) →
      (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
        Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) →
      (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
        (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  intro I R D S B ℓ A k m H0 H1 H2 H3 H4
  have hbad : {i | ¬ ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0}.Finite :=
    Filter.eventually_cofinite.mp H2
  let T : Finset I := (hbad.inter_of_left S).toFinset
  let u : ∀ i, D i := fun i =>
    if h : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 then h.choose else (H0 i).some
  have hTS : (T : Set I) ⊆ S := by
    intro i hi
    simp only [T, Set.Finite.coe_toFinset] at hi
    exact hi.2
  have hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0 := by
    intro i hi hT
    have hgood : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 := by
      by_contra h
      apply hT
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, hi⟩
    intro d
    simp only [u, hgood, dite_true]
    exact hgood.choose_spec d
  rw [LocalGrouping.finprod_finsum_eq I D S B T u hTS H1 hind]
  exact LocalGrouping.finsum_fibres_eq I R D S B ℓ A k m T u hTS H1 hind H3 H4
end GlobalTheory
