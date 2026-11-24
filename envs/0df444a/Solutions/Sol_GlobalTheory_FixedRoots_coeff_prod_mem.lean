-- Prove2me | solution 1 for GlobalTheory.FixedRoots.coeff_prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:40.960151+00:00
-- url     : https://prove2.me/submissions/f9f49cec-6329-4cb5-8d55-f76684d34f67

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemOfForallRingEquivFixed
import Theorems.Thm_GlobalTheory_FixedRoots_mem_of_forall_ringEquiv_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FixedRoots
namespace GlobalTheory.FixedRoots
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω)
    (S : Finset Ω) (hS : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) (n : ℕ) :
    (∏ x ∈ S, (X - C x)).coeff n ∈ k := by
  apply mem_of_forall_ringEquiv_fixed k
  intro σ hσ
  have hmap : S.map σ.toEquiv.toEmbedding = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact hS σ hσ x hx
    · simp
  have hP : (∏ x ∈ S, (X - C x)).map (σ : Ω →+* Ω) = ∏ x ∈ S, (X - C x) := by
    rw [Polynomial.map_prod]
    conv_rhs => rw [← hmap]
    rw [Finset.prod_map]
    simp
  have := congrArg (fun P => Polynomial.coeff P n) hP
  simpa [Polynomial.coeff_map] using this
end GlobalTheory.FixedRoots
