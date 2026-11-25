-- Prove2me | solution 1 for GlobalTheory.MinkowskiOrder.exists_prime_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:01:18.429948+00:00
-- url     : https://prove2.me/submissions/00e89511-41cc-4085-8a01-45fa4c08367f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.MinkowskiOrder
namespace GlobalTheory.MinkowskiOrder
theorem _root_.solution (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ l : ℕ, l.Prime ∧ p < l ∧ ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp h2 2
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (p ^ 2))ˣ)
  obtain ⟨l, hlp, hl, hlg⟩ := Nat.forall_exists_prime_gt_and_eq_mod g.isUnit p
  refine ⟨l, hl, hlp, fun i hi => ?_⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by norm_num)] at hg
  have : g ^ i = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hlg, Units.val_one]
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hi
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  have := orderOf_dvd_of_pow_eq_one this
  rw [hg] at this
  simpa using this
end GlobalTheory.MinkowskiOrder
