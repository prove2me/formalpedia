-- Prove2me | solution 1 for GlobalTheory.separated_roots_additive_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:38.890303+00:00
-- url     : https://prove2.me/submissions/7ab539d5-2074-4c52-a141-4466640418b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparatedRootsAdditivePoly
import Theorems.Thm_GlobalTheory_T_card_roots_closedBall_bounds_ultrametric
import Theorems.Thm_GlobalTheory_T_card_roots_closedBall_le_prime_pow
import Theorems.Thm_GlobalTheory_T_exists_finset_separated_of_multiset_bounded_cluster


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG
  have hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0 := by
    intro j
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  have hcd : G.coeff (l ^ (M + h)) = a (M + h) := by
    rw [hcoeff, Finset.sum_eq_single (M + h)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh; exact hb (hinj hh)
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hcd0 : G.coeff (l ^ (M + h)) ≠ 0 := by
    rw [hcd]; intro h0; rw [h0, norm_zero] at haMh; exact zero_ne_one haMh
  have hcle : ∀ j, ‖G.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_
    split_ifs
    · exact ha1 k (by have := Finset.mem_range.1 hk; omega)
    · simp
  have hrc := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcd, haMh]; exact hcle j)
  set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs
  have hG0 : G ≠ 0 := by
    intro h0; apply hcd0; rw [h0]; simp
  obtain ⟨Z, hZc, hZs, hZsep⟩ := GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le
    (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by
      intro W hW
      have hW1 : ‖W‖ ≤ 1 := (Multiset.mem_filter.1 hW).2
      refine le_trans (Multiset.card_le_card ?_) (GlobalTheory.T.card_roots_closedBall_le_prime_pow l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)
      exact Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  refine ⟨Z, hZc, fun W hW => ?_, hZsep⟩
  have hWs := Multiset.mem_filter.1 (hZs W hW)
  refine ⟨hWs.2, ?_⟩
  have hr := (Polynomial.mem_roots hG0).1 hWs.1
  have := hr.eq_zero
  rw [hG, Polynomial.eval_finsetSum] at this
  simpa [Polynomial.eval_monomial] using this
end GlobalTheory
