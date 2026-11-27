-- Prove2me | solution 1 for GlobalTheory.card_subgroups_le_and_card_automorphisms_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:58.322866+00:00
-- url     : https://prove2.me/submissions/736307d7-7dfa-44ba-8ce9-9c934da175dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_and_ncard_setOf_index_pi_le
import Theorems.Thm_GlobalTheory_finite_and_ncard_linearEquiv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ ρ m : ℕ, 1 ≤ m → {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
      {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ) ∧
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (n : ℕ), finrank ℤ L = n →
      ∀ (lam1 lamN c : ℝ), 0 < lam1 → 1 ≤ c → (∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖) →
      ∀ v : Fin n → L, LinearIndependent ℤ v → (∀ i, ‖(v i : E)‖ ≤ lamN) →
      ∀ G : Set (L ≃ₗ[ℤ] L), (∀ g ∈ G, ∀ x : L, ‖(g x : E)‖ ≤ c * ‖(x : E)‖) →
      G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2)) :=
  ⟨fun ρ _ hm => finite_and_ncard_setOf_index_pi_le ρ (by omega),
    fun _ _ _ _ L _ _ _ hn _ _ _ h1 hc hL _ hv hvN G hG =>
      finite_and_ncard_linearEquiv_le L hn hv h1 (zero_le_one.trans hc) hL hvN G hG⟩
end GlobalTheory
