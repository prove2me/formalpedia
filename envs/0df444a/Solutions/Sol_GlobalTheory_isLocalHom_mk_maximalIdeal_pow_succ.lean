-- Prove2me | solution 1 for GlobalTheory.isLocalHom_mk_maximalIdeal_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:52.290133+00:00
-- url     : https://prove2.me/submissions/087e8c9f-5aff-4538-a613-a39cfe7df3a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))),
    Ideal.Quotient.eq] at hc
  have h1 : a * c - 1 ∈ maximalIdeal A := Ideal.pow_le_self n.succ_ne_zero hc
  have h2 : a * c ∈ maximalIdeal A := Ideal.mul_mem_right _ _ hu
  have h3 : (1 : A) ∈ maximalIdeal A := by simpa using sub_mem h2 h1
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
end GlobalTheory
