-- Prove2me | solution 1 for GlobalTheory.charSeries_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:02.232135+00:00
-- url     : https://prove2.me/submissions/0d03da53-1810-4a7b-99f8-c4506bea560e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Theorems.Thm_GlobalTheory_charSeries_kill_finset

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
theorem _root_.solution : ∀ (A I : Type) [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I), (∀ i a b, e i (a + b) = e i a * e i b) → (∀ i a, ‖e i a‖ ≤ 1) → (∀ a, e i₀ a = 1) → (∀ i, i ≠ i₀ → ∃ a, e i a = -1) → Summable (fun i => ‖c i‖) → c i₀ ≠ 0 → ∃ a, ∑' i, c i * e i a ≠ 0 := by
  intro A I _ e c i₀ hmul hle h0 hneg hs hc
  by_contra hcon
  push Not at hcon
  have he0 : ∀ i, e i 0 = 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; exact h0 0
    · obtain ⟨a, ha⟩ := hneg i hi
      have h := hmul i a 0
      rw [add_zero, ha] at h
      linear_combination h
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.2 hc
  obtain ⟨s, hs1, hs2⟩ := (((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖))).2 _ hpos).and
    (Filter.eventually_ge_atTop {i₀})).exists
  have htail : ∑' x : {x // x ∉ s}, ‖c x‖ < ‖c i₀‖ := hs1
  have hi0 : i₀ ∈ s := hs2 (Finset.mem_singleton_self i₀)
  obtain ⟨c', hc'0, hc's, hc'le, hc'F⟩ :=
    charSeries_kill_finset e c i₀ hmul hle h0 hneg hs hcon s
  have hsum' : Summable c' := Summable.of_norm_bounded hs hc'le
  have key := hc'F 0
  simp only [he0, mul_one] at key
  rw [← hsum'.sum_add_tsum_subtype_compl s] at key
  have hfin : ∑ x ∈ s, c' x = c i₀ := by
    rw [Finset.sum_eq_single i₀ (fun b hb hne => hc's b hb hne) (fun h => absurd hi0 h)]
    exact hc'0
  rw [hfin] at key
  have hbound : ‖∑' x : {x // x ∉ s}, c' x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ :=
    tsum_of_norm_bounded ((hs.subtype _).hasSum) (fun x => hc'le x)
  have hnorm : ‖c i₀‖ = ‖∑' x : {x // x ∉ s}, c' x‖ := by
    rw [eq_neg_of_add_eq_zero_left key, norm_neg]
  linarith
end GlobalTheory
