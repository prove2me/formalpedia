-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_zmod_prime_sq_isUnit_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:02.950612+00:00
-- url     : https://prove2.me/submissions/9ac2e986-cd2a-4bf8-9f80-afee942f6ebc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_NumberFieldToModPSquared
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FiniteTypeToNumberField
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FiniteTypeToModPSquared
import Theorems.Thm_GlobalTheory_T_finite_type_to_number_field
import Theorems.Thm_GlobalTheory_T_number_field_to_mod_p_squared


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]
end GlobalTheory
