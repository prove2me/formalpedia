-- Prove2me | solution 1 for GlobalTheory.charSeries_kill_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:09.294251+00:00
-- url     : https://prove2.me/submissions/24a63849-bad2-4471-843f-59a5a746e1c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hneg : ∀ i, i ≠ i₀ → ∃ a, e i a = -1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by
  classical
  refine Finset.induction_on s ⟨c, rfl, by simp, fun i => le_rfl, hF⟩ ?_
  intro j s _ ih
  obtain ⟨c', h1, h2, h3, h4⟩ := ih
  by_cases hji : j = i₀
  · subst hji
    refine ⟨c', h1, ?_, h3, h4⟩
    intro i hi hne
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd rfl hne
    · exact h2 i hi hne
  · obtain ⟨b, hb⟩ := hneg j hji
    refine ⟨fun i => c' i * (1 + e i b) / 2, ?_, ?_, ?_, ?_⟩
    · show c' i₀ * (1 + e i₀ b) / 2 = c i₀
      rw [h0 b, h1]; ring
    · intro i hi hne
      show c' i * (1 + e i b) / 2 = 0
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hb]; ring
      · rw [h2 i hi hne]; ring
    · intro i
      show ‖c' i * (1 + e i b) / 2‖ ≤ ‖c i‖
      have h2b : ‖(1 : ℂ) + e i b‖ ≤ 2 :=
        (norm_add_le _ _).trans (by rw [norm_one]; linarith [hle i b])
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      calc ‖c' i‖ * ‖1 + e i b‖ / 2 ≤ ‖c' i‖ * 2 / 2 := by gcongr
        _ = ‖c' i‖ := by ring
        _ ≤ ‖c i‖ := h3 i
    · intro a
      show ∑' i, c' i * (1 + e i b) / 2 * e i a = 0
      have hsum : ∀ x, Summable (fun i => c' i * e i x) := fun x =>
        Summable.of_norm_bounded hs (fun i => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hle i x)).trans (h3 i))
      have key : ∀ i, c' i * (1 + e i b) / 2 * e i a = (c' i * e i a + c' i * e i (b + a)) / 2 := by
        intro i; rw [hmul i b a]; ring
      simp only [key]
      rw [tsum_div_const, (hsum a).tsum_add (hsum (b + a)), h4 a, h4 (b + a)]
      simp
end GlobalTheory
