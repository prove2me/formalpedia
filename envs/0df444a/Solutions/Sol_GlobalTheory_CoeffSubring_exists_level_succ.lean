-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_level_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:36.328793+00:00
-- url     : https://prove2.me/submissions/a1bb5f96-8d07-4e02-ae94-8797a6f4173f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_pow_sub_pow_mem

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
theorem _root_.solution (h0 : (p : S) ∈ maximalIdeal S)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (n : ℕ) {s : S}
    (h : s ∈ level p L n) : ∃ t ∈ level p L (n + 1), s - t ∈ maximalIdeal S ^ (n + 1) := by
  let π := Ideal.Quotient.mk (maximalIdeal S ^ (n + 1))
  have : level p L n ≤ ((level p L (n + 1)).map π).comap π := by
    refine Subring.closure_le.2 ?_
    rintro _ ((⟨x, rfl⟩ | hx) | hx)
    · obtain ⟨t, ht, hxt⟩ := hs (n + 1) x
      exact ⟨t ^ p ^ n, pow_mem ht _, (Ideal.Quotient.eq.2 (pow_sub_pow_mem h0 hxt n)).symm⟩
    · exact ⟨_, mem_level_of_mem hx, rfl⟩
    · exact ⟨0, Subring.zero_mem _, (map_zero π).trans (Ideal.Quotient.eq_zero_iff_mem.2 hx).symm⟩
  obtain ⟨t, ht, h'⟩ := this h
  exact ⟨t, ht, Ideal.Quotient.eq.1 h'.symm⟩
end GlobalTheory.CoeffSubring
