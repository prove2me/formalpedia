-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.card_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:31:01.51881+00:00
-- url     : https://prove2.me/submissions/6073eb40-df30-4b91-9d18-e2ac783f04c0

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PrimeToNormalVanishing
variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]
namespace GlobalTheory.PrimeToNormalVanishing
theorem _root_.solution (l : ℕ) (hl : l.Prime) (h : ∀ k ∈ K, ∃ n, Nat.Coprime n l ∧ k ^ n = 1) :
    Nat.Coprime (Fintype.card K) l := by
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
  obtain ⟨n, hn, hxn⟩ := h x x.2
  have : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxn))
  rw [hx] at this
  exact hl.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hn this dvd_rfl)
end GlobalTheory.PrimeToNormalVanishing
