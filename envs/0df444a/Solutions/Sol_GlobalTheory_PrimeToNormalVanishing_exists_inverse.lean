-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.exists_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:31:03.174849+00:00
-- url     : https://prove2.me/submissions/2a222275-a216-4089-ab14-c9fffca93846

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
theorem _root_.solution {X : Type} [Finite X] (l N : ℕ) (hN : Nat.Coprime N l)
    (htor : ∀ m : M, ∃ n, l ^ n • m = 0) (φ : X → M) : ∃ a : ℤ, ∀ x, a • N • φ x = φ x := by
  choose n hn using htor
  obtain ⟨k, hk⟩ := (Set.finite_range fun x => n (φ x)).bddAbove
  have h0 : ∀ x, l ^ k • φ x = 0 := fun x => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (hk ⟨x, rfl⟩)
    rw [hd, pow_add, mul_smul, hn, smul_zero]
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (hN.pow_right k)
  refine ⟨a, fun x => ?_⟩
  have : (a * N + b * (l ^ k : ℕ)) • φ x = φ x := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h0, smul_zero, add_zero] at this
end GlobalTheory.PrimeToNormalVanishing
