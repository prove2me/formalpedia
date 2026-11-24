-- Prove2me | solution 1 for GlobalTheory.abssum_eigen_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:08.145373+00:00
-- url     : https://prove2.me/submissions/917a95dd-a09f-4029-b5c1-1d27444230ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  intro l _ A _ _ φ h w hw
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(l : A)} ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  let S : ℕ → A := fun N => ∑ k ∈ Finset.range N, (l : A) ^ k * w k
  have hS : ∀ m n, m ≤ n → (l : A) ^ m ∣ S n - S m := by
    intro m n hmn
    simp only [S]
    rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro k hk
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _
  obtain ⟨W, hW⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) (M := A) inferInstance (f := S)
    (fun {m n} hmn => by rw [SModEq.sub_mem, key]; exact dvd_sub_comm.1 (hS m n hmn))
  have hWN : ∀ N, ∃ c : A, W = S N + (l : A) ^ N * c := by
    intro N
    have h1 := SModEq.sub_mem.1 (hW N)
    rw [key] at h1
    obtain ⟨c, hc⟩ := dvd_sub_comm.1 h1
    exact ⟨c, by rw [← hc]; ring⟩
  simp only [← RingHom.coe_pow] at hw ⊢
  have hSψ : ∀ N, (φ ^ h) (S N) = (l : A) * S N := by
    intro N
    simp only [S, map_sum, map_mul, map_pow, map_natCast, hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨W, ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    obtain ⟨c, hc⟩ := hWN n
    rw [hc, map_add, map_mul, map_pow, map_natCast, hSψ]
    exact ⟨(φ ^ h) c - (l : A) * c, by ring⟩
  · intro Θ hΘ
    have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
      rw [show (l : ℂ_[l]) = (((l : ℚ_[l])) : ℂ_[l]) by simp, PadicComplex.norm_extends', Padic.norm_p]
    have hlt : ‖(l : ℂ_[l])‖ < 1 := by
      rw [hl]
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Fact.out : l.Prime).one_lt
    have hbound : ∀ k, ‖(l : ℂ_[l]) ^ k * Θ (w k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hΘ _)
    have hsum : Summable (fun k => (l : ℂ_[l]) ^ k * Θ (w k)) :=
      Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hlt) hbound
    rw [hsum.hasSum_iff_tendsto_nat]
    have hpart : ∀ N, ∑ i ∈ Finset.range N, (l : ℂ_[l]) ^ i * Θ (w i) = Θ (S N) := by
      intro N
      simp [S, map_sum, map_mul, map_pow, map_natCast]
    simp only [hpart]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt)
    obtain ⟨c, hc⟩ := hWN N
    rw [hc, map_add, sub_add_cancel_left, norm_neg, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hΘ _)
end GlobalTheory
