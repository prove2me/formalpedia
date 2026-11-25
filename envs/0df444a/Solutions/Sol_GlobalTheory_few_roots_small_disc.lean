-- Prove2me | solution 1 for GlobalTheory.few_roots_small_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:42.884801+00:00
-- url     : https://prove2.me/submissions/4e58b976-033d-4d41-b3b4-56d74424bc8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc
import Theorems.Thm_GlobalTheory_roots_taylor_eq_map_sub
import Theorems.Thm_GlobalTheory_coeff_sum_monomial_pow
import Theorems.Thm_GlobalTheory_coeff_sum_monomial_small
import Theorems.Thm_GlobalTheory_T_card_roots_closedBall_bounds_ultrametric
import Theorems.Thm_GlobalTheory_T_norm_taylor_coeff_sub_coeff_le_norm_l


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  intro l _ E M a ρ W hME ha hρ0 hρ1 hM hgt hW
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k) with hG
  set H := taylor W G with hH
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  have hroots : Multiset.card (G.roots.filter fun z => ‖z - W‖ ≤ ρ)
      = Multiset.card (H.roots.filter fun z => ‖z‖ ≤ ρ) := by
    rw [hH, roots_taylor_eq_map_sub, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [hroots]
  have hd1 : 1 ≤ l ^ M := Nat.one_le_pow _ _ (by omega)
  have hGd : G.coeff (l ^ M) = a M := coeff_sum_monomial_pow l E a M hME
  have hdiff : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ ≤ ‖(l : ℂ_[l])‖ :=
    GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l l E a W ha hW
  have hρj : ∀ j, 1 ≤ j → ρ ^ j < 1 := fun j hj => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hdiffsmall : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ * ρ ^ j < ‖(l : ℂ_[l])‖ := by
    intro j hj
    calc ‖H.coeff j - G.coeff j‖ * ρ ^ j ≤ ‖(l : ℂ_[l])‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right (hdiff j hj) (by positivity)
      _ < ‖(l : ℂ_[l])‖ := mul_lt_of_lt_one_right hlpos (hρj j hj)
  have hHd : ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ := by
    have hlt : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ < ‖G.coeff (l ^ M)‖ := by
      have h1 : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ * ρ ^ l ^ M
          < ‖G.coeff (l ^ M)‖ * ρ ^ l ^ M := by
        rw [hGd, hM]; have h0 := hdiffsmall _ hd1; rwa [hGd] at h0
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    have h2 : H.coeff (l ^ M) = G.coeff (l ^ M) + (H.coeff (l ^ M) - G.coeff (l ^ M)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hGd, hM]
  have hHd0 : H.coeff (l ^ M) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hHd
    exact hlpos.ne hHd
  have hbig : ∀ j, l ^ M < j → ‖H.coeff j‖ * ρ ^ j < ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M := by
    intro j hj
    rw [hHd]
    have h2 : H.coeff j = G.coeff j + (H.coeff j - G.coeff j) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max (G.coeff j) (H.coeff j - G.coeff j)
    rw [← h2] at h3
    have hρ : 0 ≤ ρ ^ j := by positivity
    calc ‖H.coeff j‖ * ρ ^ j ≤ max ‖G.coeff j‖ ‖H.coeff j - G.coeff j‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right h3 hρ
      _ = max (‖G.coeff j‖ * ρ ^ j) (‖H.coeff j - G.coeff j‖ * ρ ^ j) := max_mul_of_nonneg _ _ hρ
      _ < ‖(l : ℂ_[l])‖ := max_lt (coeff_sum_monomial_small l E M a ρ hρ0 hgt j hj)
          (hdiffsmall j (by omega))
  exact (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] H ρ (l ^ M) hρ0 hHd0).2 hbig
end GlobalTheory
