-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:51:02.328286+00:00
-- url     : https://prove2.me/submissions/6fb174b0-1384-4640-8089-03d5c8733c1d

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_1

section
namespace MulticlassOmni.Dev.B2

open MulticlassOmni.Lipschitz

theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [pow_succ]; omega

/-- the transformed point: permute coordinates by `τ`, multiply by `σ`, rescale and shift. -/
noncomputable def T (k : ℕ) (τ : Equiv.Perm (Fin k)) (σ : ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun y => vbar k y + σ * x (τ y) / (8 * (k : ℝ))

theorem T_injective (k : ℕ) (hk : 0 < k) (τ : Equiv.Perm (Fin k)) (σ : ℝ) (hσ : σ ≠ 0) :
    Function.Injective (T k τ σ) := by
  intro x x' h
  funext y
  have := congrFun h (τ.symm y)
  simp only [T, Equiv.apply_symm_apply] at this
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have h8 : (8 * (k:ℝ)) ≠ 0 := by positivity
  have h2 := add_left_cancel this
  exact mul_left_cancel₀ hσ ((div_left_inj' h8).1 h2)

theorem sub_vbar (k : ℕ) (τ : Equiv.Perm (Fin k)) (σ : ℝ) (x : Fin k → ℝ) (y : Fin k) :
    T k τ σ x y - vbar k y = σ * x (τ y) / (8 * (k : ℝ)) := by
  simp [T]

end MulticlassOmni.Dev.B2

namespace MulticlassOmni.Lipschitz

open MulticlassOmni.Dev.B2 in
theorem chk_lemma_B_2 :
    ∃ Cpack ε₀ : ℝ, 0 < Cpack ∧ 0 < ε₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ X : Finset (Fin k → ℝ), IsSimplexPacking Cpack k ε X := by
  obtain ⟨C, hC, hM⟩ := lemma_B_1
  obtain ⟨ε₀, hε₀, H⟩ := hM 0
  refine ⟨C + 1, ε₀, by linarith, hε₀, ?_⟩
  intro k hk ε hε hεle
  obtain ⟨X, hcard, ⟨hbox, hsum, hsq, hdot⟩, -, -⟩ := H k hk ε hε hεle
  classical
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  set z0 : Fin k := ⟨0, hk0⟩ with hz0
  -- groups
  let F : Fin k × Bool → Finset (Fin k → ℝ) := fun p =>
    X.filter (fun x => if p.2 then 1 / 2 ≤ x p.1 else x p.1 ≤ -1 / 2)
  have hcover : ∀ x ∈ X, ∃ p, x ∈ F p := by
    intro x hx
    by_contra hno
    push Not at hno
    have hlt : ∀ y, x y ^ 2 < 1 / 4 := by
      intro y
      have h1 := hno (y, true)
      have h2 := hno (y, false)
      simp only [F, Finset.mem_filter, if_true, not_and] at h1 h2
      have a := h1 hx
      have b := h2 hx
      simp at a b
      nlinarith
    have : ∑ y, x y ^ 2 < ∑ _y : Fin k, (1 / 4 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty ⟨z0, Finset.mem_univ _⟩ (fun y _ => hlt y)
    rw [hsq x hx] at this
    simp at this
    linarith
  have hXsub : X ⊆ Finset.univ.biUnion F := by
    intro x hx
    obtain ⟨p, hp⟩ := hcover x hx
    exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hp⟩
  have hcardle : (X.card : ℝ) ≤ ∑ p, ((F p).card : ℝ) := by
    have := (Finset.card_le_card hXsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hex : ∃ p, (X.card : ℝ) / (2 * k) ≤ ((F p).card : ℝ) := by
    by_contra hno
    push Not at hno
    have : ∑ p, ((F p).card : ℝ) < ∑ _p : Fin k × Bool, (X.card : ℝ) / (2 * k) :=
      Finset.sum_lt_sum_of_nonempty ⟨(z0, true), Finset.mem_univ _⟩ (fun p _ => hno p)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul] at this
    have e : ((k * 2 : ℕ) : ℝ) * ((X.card : ℝ) / (2 * k)) = X.card := by
      push_cast; field_simp
    rw [e] at this
    linarith
  obtain ⟨⟨y₀, b⟩, hp⟩ := hex
  set τ : Equiv.Perm (Fin k) := Equiv.swap z0 y₀ with hτ
  set σ : ℝ := if b then -1 else 1 with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσ0 : σ ≠ 0 := by rw [hσ]; split_ifs <;> norm_num
  have hσabs : |σ| = 1 := by rw [hσ]; split_ifs <;> norm_num
  set Y := (F (y₀, b)).image (T k τ σ) with hY
  have hFX : F (y₀, b) ⊆ X := Finset.filter_subset _ _
  have hYcard : Y.card = (F (y₀, b)).card :=
    Finset.card_image_of_injective _ (T_injective k hk0 τ σ hσ0)
  have hτsum : ∀ f : Fin k → ℝ, ∑ y, f (τ y) = ∑ y, f y := fun f =>
    Equiv.sum_comp τ f
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cardinality
    rw [hYcard]
    refine le_trans ?_ hp
    rw [le_div_iff₀ (by positivity)]
    have h2k : (2 * (k:ℝ)) ≤ 2 ^ k := by exact_mod_cast two_mul_le_two_pow k
    have hpow : (2:ℝ) ^ (-(C + 1) * k) * (2 : ℝ) ^ (k:ℝ) = (2:ℝ) ^ (-C * k) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have hpos : 0 ≤ (2:ℝ) ^ (-(C + 1) * k) * ε ^ (-((k : ℝ) - 2) / 2) := by positivity
    calc (2:ℝ) ^ (-(C + 1) * k) * ε ^ (-((k : ℝ) - 2) / 2) * (2 * k)
        ≤ (2:ℝ) ^ (-(C + 1) * k) * ε ^ (-((k : ℝ) - 2) / 2) * 2 ^ k :=
          mul_le_mul_of_nonneg_left h2k hpos
      _ = (2:ℝ) ^ (-C * k) * ε ^ (-((k : ℝ) - 2) / 2) := by
          rw [← hpow, ← Real.rpow_natCast]; ring
      _ ≤ X.card := hcard
  all_goals intro x hx
  all_goals obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
  all_goals have hx0X := hFX hx0
  all_goals have hgrp := (Finset.mem_filter.1 hx0).2
  all_goals simp only at hgrp
  · -- simplex
    refine ⟨fun y => ?_, ?_⟩
    · have := hbox x0 hx0X (τ y)
      simp only [T, vbar]
      have h1 : |σ * x0 (τ y)| ≤ 1 := by
        rw [abs_mul, hσabs, one_mul, abs_le]; exact ⟨this.1, this.2⟩
      rw [abs_le] at h1
      have : -1 / (8 * (k:ℝ)) ≤ σ * x0 (τ y) / (8 * k) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
      have : 1 / (8 * (k:ℝ)) ≤ 1 / k := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have e : -1 / (8 * (k:ℝ)) = - (1 / (8 * k)) := by ring
      linarith
    · simp only [T, vbar, Finset.sum_add_distrib]
      rw [← Finset.sum_div (f := fun i => σ * x0 (τ i)), ← Finset.mul_sum,
        hτsum (fun y => x0 y), hsum x0 hx0X]
      simp; field_simp
  · intro y
    have := hbox x0 hx0X (τ y)
    simp only [T, vbar]
    have h1 : |σ * x0 (τ y)| ≤ 1 := by
      rw [abs_mul, hσabs, one_mul, abs_le]; exact ⟨this.1, this.2⟩
    rw [abs_le] at h1
    constructor
    · rw [show 7 / (8 * (k:ℝ)) = 1 / k + (-1) / (8 * k) by field_simp; ring]
      have : -1 / (8 * (k:ℝ)) ≤ σ * x0 (τ y) / (8 * k) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
      linarith
    · rw [show 9 / (8 * (k:ℝ)) = 1 / k + 1 / (8 * k) by field_simp; ring]
      have : σ * x0 (τ y) / (8 * k) ≤ 1 / (8 * (k:ℝ)) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
      linarith
  · intro y hy
    have hyz : y = z0 := Fin.ext (by simp [hz0, hy])
    subst hyz
    have hτ0 : τ z0 = y₀ := by simp [hτ]
    simp only [T, vbar, hτ0]
    have key : σ * x0 y₀ ≤ -1 / 2 := by
      rw [hσ]; cases b
      · simp at hgrp ⊢; linarith
      · simp at hgrp ⊢; linarith
    rw [show 15 / (16 * (k:ℝ)) = 1 / k + (-1 / 2) / (8 * k) by field_simp; ring]
    have : σ * x0 y₀ / (8 * k) ≤ (-1 / 2) / (8 * (k:ℝ)) := by
      rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
    linarith
  · simp only [sub_vbar]
    have : ∀ y, (σ * x0 (τ y) / (8 * (k:ℝ))) ^ 2 = (x0 (τ y)) ^ 2 / (64 * (k:ℝ) ^ 2) := by
      intro y
      rw [div_pow, mul_pow, show σ ^ 2 = 1 by rw [sq]; exact hσ2]; ring
    simp only [this]
    rw [← Finset.sum_div, hτsum (fun y => x0 y ^ 2), hsq x0 hx0X]
    field_simp; ring
  · intro x' hx' hne
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.1 hx'
    have hne' : x0 ≠ x1 := fun h => hne (by rw [h])
    have hd := hdot x0 hx0X x1 (hFX hx1) hne'
    unfold dot at hd ⊢
    have : ∀ y, (T k τ σ x0 - vbar k) y * (T k τ σ x1 - vbar k) y
        = x0 (τ y) * x1 (τ y) / (64 * (k:ℝ) ^ 2) := by
      intro y
      simp only [Pi.sub_apply, sub_vbar]
      rw [div_mul_div_comm, mul_mul_mul_comm, hσ2]
      ring
    simp only [this]
    rw [← Finset.sum_div, hτsum (fun y => x0 y * x1 y)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ 1 - 8000 * ε ∨ 1 - 8000 * ε < 0 := le_or_gt _ _
    nlinarith [hd]

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_B_2 := @MulticlassOmni.Lipschitz.chk_lemma_B_2
