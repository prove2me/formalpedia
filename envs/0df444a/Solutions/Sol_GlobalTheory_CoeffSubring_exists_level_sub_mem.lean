-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_level_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:55.922821+00:00
-- url     : https://prove2.me/submissions/db299a64-cf4d-47cb-b2cd-1c12a72ca3e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_closure_pow_eq_top
import Theorems.Thm_GlobalTheory_CoeffSubring_pow_mem_level
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution (hp : p.Prime) (h0 : (p : S) ∈ maximalIdeal S)
    (hB : Subring.closure (Set.range (fun x : ResidueField S => x ^ p) ∪ residue S '' L) = ⊤)
    (n : ℕ) (s : S) : ∃ t ∈ level p L n, s - t ∈ maximalIdeal S := by
  have h1 := closure_pow_eq_top hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0) hB n
  have h2 : (level p L n).map (residue S) = ⊤ := by
    rw [eq_top_iff, ← h1, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, rfl⟩)
    · obtain ⟨x, rfl⟩ := residue_surjective x
      exact ⟨_, pow_mem_level n x, map_pow _ _ _⟩
    · exact ⟨x, mem_level_of_mem hx, rfl⟩
  obtain ⟨t, ht, h⟩ := h2.ge (Subring.mem_top (residue S s))
  exact ⟨t, ht, by rw [← residue_eq_zero_iff, map_sub, h, sub_self]⟩
end GlobalTheory.CoeffSubring
