-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.three_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:51.261899+00:00
-- url     : https://prove2.me/submissions/c7176d84-a6fe-464f-8206-48031c9d1db2

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
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → Q → M)
    (heq : ∀ g a b c, F (π g * a) (π g * b) (π g * c) = ρ g (F a b c))
    (hc : ∀ a b c d, F b c d - F a c d + F a b d - F a b c = 0) :
    ∃ H : Q → M, ∀ g h, (Fintype.card K) ^ 3 • F 1 (π g) (π (g * h)) =
      ρ g (H (π h)) - H (π (g * h)) + H (π g) := by
  have hS : ∀ a b c, ∑ i : K, ∑ j : K, ∑ k : K, F (a * i) (b * j) (c * k) = 0 := by
    intro a b c
    refine hinv _ fun g hg => ?_
    simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, ∑ k : K, F x (b * j) (c * k)) a _ (hJK g hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_shift K (fun x => ∑ k : K, F _ x (c * k)) b _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ _ x) c _ (hJK g hg)
  let H : Q → Q → M := fun a b =>
    Fintype.card K • ∑ i : K, ∑ j : K, (F a b (b * j) - F a (a * i) (b * j))
  have key : ∀ a b c, (Fintype.card K) ^ 3 • F a b c = H b c - H a c + H a b := by
    intro a b c
    have e : ∀ a' b' c', F a b c = F a' b' c' + (F b c c' - F b b' c') - (F a c c' - F a a' c')
        + (F a b b' - F a a' b') := by
      intro a' b' c'
      have e1 := hc a a' b' c'
      have e2 := hc a b b' c'
      have e3 := hc a b c c'
      have e4 : (0 : M) = 0 - 0 - 0 := by simp
      rw [← sub_eq_zero, e4]
      nth_rewrite 1 [← e2]
      nth_rewrite 1 [← e1]
      rw [← e3]; abel
    calc _ = ∑ i : K, ∑ j : K, ∑ k : K, F a b c := by simp [pow_succ, mul_smul]
      _ = ∑ i : K, ∑ j : K, ∑ k : K, (F (a * i) (b * j) (c * k) +
          (F b c (c * k) - F b (b * j) (c * k)) - (F a c (c * k) - F a (a * i) (c * k))
          + (F a b (b * j) - F a (a * i) (b * j))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => e _ _ _
      _ = _ := by
        simp only [H, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum, smul_sub]
  have hH : ∀ g a b, H (π g * a) (π g * b) = ρ g (H a b) := by
    intro g a b
    simp only [H, map_nsmul, map_sum, map_sub, ← heq, mul_assoc]
  refine ⟨H 1, fun g h => ?_⟩
  rw [key, ← hH, mul_one, map_mul]
end GlobalTheory.PrimeToNormalVanishing
