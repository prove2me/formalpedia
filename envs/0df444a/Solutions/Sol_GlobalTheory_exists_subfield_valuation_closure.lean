-- Prove2me | solution 1 for GlobalTheory.exists_subfield_valuation_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:21.206035+00:00
-- url     : https://prove2.me/submissions/9458adfb-2306-4d52-ac82-39d227c3ad90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsSubfieldValuationClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Topology Filter
namespace GlobalTheory
theorem _root_.solution :
    ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U),
      ∃ S' : Subfield U, ∀ u, u ∈ S' ↔
        ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  intro U _ v S
  refine ⟨{ carrier := {u | ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ}
            zero_mem' := ?hz, one_mem' := ?ho, add_mem' := ?ha, neg_mem' := ?hn, mul_mem' := ?hm,
            inv_mem' := ?hi }, fun _ => Iff.rfl⟩
  case hz =>
    intro γ hγ
    exact ⟨0, S.zero_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
  case ho =>
    intro γ hγ
    exact ⟨1, S.one_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
  case ha =>

    intro a b ha hb γ hγ
    obtain ⟨s, hs, hs'⟩ := ha γ hγ
    obtain ⟨t, ht, ht'⟩ := hb γ hγ
    refine ⟨s + t, S.add_mem hs ht, ?_⟩
    rw [show a + b - (s + t) = (a - s) + (b - t) by ring]
    exact v.map_add_lt hs' ht'
  case hn =>
    intro a ha γ hγ
    obtain ⟨s, hs, hs'⟩ := ha γ hγ
    refine ⟨-s, S.neg_mem hs, ?_⟩
    rw [show -a - -s = -(a - s) by ring, Valuation.map_neg]
    exact hs'
  case hm =>

    intro a b ha hb γ hγ
    obtain ⟨M, haM, hbM, hM1⟩ : ∃ M : WithZero (Multiplicative ℤ), v a ≤ M ∧ v b ≤ M ∧ 1 ≤ M :=
      ⟨max (max (v a) (v b)) 1, le_trans (le_max_left _ _) (le_max_left _ _),
        le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
    have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM1)
    obtain ⟨δ, hδ0, hδγ, hδ1⟩ : ∃ δ : WithZero (Multiplicative ℤ), δ ≠ 0 ∧ δ ≤ γ * M⁻¹ ∧ δ ≤ 1 := by
      refine ⟨min (γ * M⁻¹) 1, ?_, min_le_left _ _, min_le_right _ _⟩
      rcases le_total (γ * M⁻¹) 1 with h | h
      · rw [min_eq_left h]; exact mul_ne_zero hγ (inv_ne_zero hM0)
      · rw [min_eq_right h]; exact one_ne_zero
    obtain ⟨s, hs, hs'⟩ := ha δ hδ0
    obtain ⟨t, ht, ht'⟩ := hb δ hδ0
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have hMδ : M * δ ≤ γ := by
      calc M * δ ≤ M * (γ * M⁻¹) := mul_le_mul_right hδγ M
        _ = γ := by rw [mul_comm γ, ← mul_assoc, mul_inv_cancel₀ hM0, one_mul]
    have hvt : v t ≤ M := by
      rw [show t = b - (b - t) by ring]
      exact v.map_sub_le hbM (le_trans (le_of_lt ht') (le_trans hδ1 hM1))
    rw [show a * b - s * t = a * (b - t) + (a - s) * t by ring]
    refine v.map_add_lt ?_ ?_
    · rw [v.map_mul]
      calc v a * v (b - t) ≤ M * v (b - t) := mul_le_mul_left haM _
        _ < M * δ := mul_lt_mul_of_pos_left ht' (zero_lt_iff.2 hM0)
        _ ≤ γ := hMδ
    · rw [v.map_mul]
      calc v (a - s) * v t ≤ v (a - s) * M := mul_le_mul_right hvt _
        _ < δ * M := mul_lt_mul_of_pos_right hs' (zero_lt_iff.2 hM0)
        _ = M * δ := mul_comm _ _
        _ ≤ γ := hMδ
  case hi =>

    intro a ha γ hγ
    by_cases h0 : a = 0
    · subst h0
      rw [inv_zero]
      exact ⟨0, S.zero_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
    have hva : v a ≠ 0 := (v.ne_zero_iff).2 h0
    obtain ⟨δ, hδ0, hδa, hδγ⟩ :
        ∃ δ : WithZero (Multiplicative ℤ), δ ≠ 0 ∧ δ ≤ v a ∧ δ ≤ γ * (v a * v a) := by
      refine ⟨min (v a) (γ * (v a * v a)), ?_, min_le_left _ _, min_le_right _ _⟩
      rcases le_total (v a) (γ * (v a * v a)) with h | h
      · rw [min_eq_left h]; exact hva
      · rw [min_eq_right h]; exact mul_ne_zero hγ (mul_ne_zero hva hva)
    obtain ⟨s, hs, hs'⟩ := ha δ hδ0
    have hvs : v s = v a :=
      v.map_eq_of_sub_lt (by rw [v.map_sub_swap]; exact lt_of_lt_of_le hs' hδa)
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, map_zero] at hvs
      exact hva hvs.symm
    refine ⟨s⁻¹, S.inv_mem hs, ?_⟩
    have key : a⁻¹ - s⁻¹ = (s - a) * (a⁻¹ * s⁻¹) := by
      rw [sub_mul, mul_left_comm, mul_inv_cancel₀ hs0, mul_one, ← mul_assoc,
        mul_inv_cancel₀ h0, one_mul]
    rw [key, v.map_mul, v.map_mul, v.map_inv, v.map_inv, hvs, v.map_sub_swap]
    have hpos : 0 < (v a)⁻¹ * (v a)⁻¹ :=
      zero_lt_iff.2 (mul_ne_zero (inv_ne_zero hva) (inv_ne_zero hva))
    calc v (a - s) * ((v a)⁻¹ * (v a)⁻¹) < γ * (v a * v a) * ((v a)⁻¹ * (v a)⁻¹) :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hs' hδγ) hpos
      _ = γ := by rw [mul_assoc, ← mul_inv, mul_inv_cancel₀ (mul_ne_zero hva hva), mul_one]
end GlobalTheory
