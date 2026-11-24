-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.two_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:52.359804+00:00
-- url     : https://prove2.me/submissions/fab80050-32af-4a91-9c29-3d00e1defa0a

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_sum_shift

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
theorem _root_.solution [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → M)
    (heq : ∀ g a b, F (π g * a) (π g * b) = ρ g (F a b))
    (hc : ∀ a b c, F b c - F a c + F a b = 0) :
    ∃ m : M, ∀ g, (Fintype.card K) ^ 2 • F 1 (π g) = ρ g m - m := by
  have hS : ∀ a b, ∑ i : K, ∑ j : K, F (a * i) (b * j) = 0 := by
    intro a b
    refine hinv _ fun g hg => ?_
    simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, F x (b * j)) a _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ x) b _ (hJK g hg)
  have key : ∀ a b, (Fintype.card K) ^ 2 • F a b =
      Fintype.card K • ∑ i : K, F a (a * i) - Fintype.card K • ∑ i : K, F b (b * i) := by
    intro a b
    have e : ∀ a' b', F a b = F a' b' + F a a' - F b b' := by
      intro a' b'
      have e1 := hc a a' b'
      have e2 := hc a b b'
      rw [← sub_eq_zero, ← sub_self (0 : M)]
      nth_rewrite 1 [← e2]
      rw [← e1]; abel
    calc _ = ∑ i : K, ∑ j : K, F a b := by simp [pow_two, mul_smul]
      _ = ∑ i : K, ∑ j : K, (F (a * i) (b * j) + F a (a * i) - F b (b * j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e _ _
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum]
  refine ⟨-(Fintype.card K • ∑ i : K, F 1 (1 * i)), fun g => ?_⟩
  rw [key, map_neg, map_nsmul, map_sum]
  simp only [← heq, mul_one, one_mul]
  abel
end GlobalTheory.PrimeToNormalVanishing
