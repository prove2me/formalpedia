-- Prove2me | solution 1 for GuthMaynard.norm_S_three_le_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:20:54.328407+00:00
-- url     : https://prove2.me/submissions/d63110bd-a07e-4e2b-9fe3-34f96d633f1b

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_norm_S_three_le_refined

namespace GuthMaynard.P81

open GuthMaynard

lemma card_sq_le_energy (W : Finset ℝ) : (W.card : ℝ) ^ 2 ≤ (energy W : ℝ) := by
  have h : (W ×ˢ W).card ≤ energy W := by
    unfold energy
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2, p.1, p.2)) ?_ ?_
    · intro p hp
      have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
      simp only [Finset.coe_filter, Finset.mem_product]
      refine ⟨⟨hp'.1, hp'.2, hp'.1, hp'.2⟩, ?_⟩
      simp
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
  rw [Finset.card_product] at h
  exact_mod_cast (by nlinarith [h] : W.card ^ 2 ≤ energy W)

lemma key (T N c E : ℝ) (hT : 0 ≤ T) (hNT : N ≤ T) (hN : 0 ≤ N) (hc : 0 ≤ c) (hE : c ^ 2 ≤ E) :
    T ^ 2 * c ^ (3 / 2 : ℝ) + T * N * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) ≤
      2 * (T ^ 2 * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) := by
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have h32 : c ^ (3 / 2 : ℝ) = c ^ (1 / 2 : ℝ) * c := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hc (by norm_num), Real.rpow_one]
  have hcE : c ≤ E ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hE
  have h1 : T ^ 2 * c ^ (3 / 2 : ℝ) ≤ T ^ 2 * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
    rw [h32, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcE (by positivity)) (by positivity)
  have h2 : T * N * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) ≤ T ^ 2 * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
    have : T * N ≤ T ^ 2 := by nlinarith
    have hp : 0 ≤ c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by positivity
    calc T * N * c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) = (T * N) * (c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) := by ring
      _ ≤ T ^ 2 * (c ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right this hp
      _ = _ := by ring
  linarith

theorem norm_S_three_le_energy_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 3 w N W‖ ≤ C * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by
  intro δ hδ
  obtain ⟨C, T₀, h⟩ := GuthMaynard.norm_S_three_le_refined w hw ε hε δ hδ
  refine ⟨2 * max C 0, max T₀ 0, ?_⟩
  intro T hT N hN W a hsep hW
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hb := h T (le_trans (le_max_left _ _) hT) N hN W a hsep hW
  have hk := key T N (W.card : ℝ) (energy W : ℝ) hT0 hN.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (card_sq_le_energy W)
  have hTd : 0 ≤ T ^ δ := Real.rpow_nonneg hT0 _
  have hR : 0 ≤ T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc ‖S 3 w N W‖ ≤ C * T ^ δ * _ := hb
    _ ≤ max C 0 * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hTd) hR
    _ ≤ max C 0 * T ^ δ * (2 * (T ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hk (mul_nonneg (le_max_right _ _) hTd)
    _ = _ := by ring

end GuthMaynard.P81


theorem solution : type_of% @GuthMaynard.P81.norm_S_three_le_energy_dev := @GuthMaynard.P81.norm_S_three_le_energy_dev
