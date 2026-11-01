-- Prove2me | solution 1 for InterimTesting.NotProficient.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:27:57.046726+00:00
-- url     : https://prove2.me/submissions/6ab65479-6d54-4d68-80b1-6f1cfe88ad59

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model
import Theorems.Thm_InterimTesting_NotProficient_eq_A211
import Theorems.Thm_InterimTesting_NotProficient_eq_A212
import Theorems.Thm_InterimTesting_NotProficient_eq_A214
import Theorems.Thm_InterimTesting_NotProficient_lemma_A11

open InterimTesting.NotProficient

theorem solution (θ : Params) (hθ : θ.Standing) :
    (θ.B = 0 → ∀ M : ℝ, 0 ≤ M →
        optProb θ true .N M = optProb θ false .N M ∧ ¬ investsInterim θ .N M) ∧
      (0 < θ.B → Cond14 θ →
        (∀ M : ℝ, 0 ≤ M → M < ML θ → optProb θ true .N M = optProb θ false .N M) ∧
        (∀ M : ℝ, MU θ ≤ M → optProb θ true .N M = optProb θ false .N M) ∧
        (∀ M : ℝ, 0 ≤ M → (investsInterim θ .N M ↔
            (HI1 θ ≤ M ∧ M < H1 θ) ∨
            (mu0 θ < θ.μ ∧ max (HI1 θ) (H1 θ) ≤ M ∧ M < H2 θ)))) := by
  have hθ' := hθ
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  refine ⟨fun hB M hM => ?_, fun hB h14 => ?_⟩
  · have e : optProb θ true .N M = optProb θ false .N M := by
      rw [lemma_A11 θ hθ' hB true M hM, lemma_A11 θ hθ' hB false M hM]
    refine ⟨e, ?_⟩
    unfold investsInterim
    rw [e]
    exact lt_irrefl _
  -- part b
  obtain ⟨hv2iff, hHI1H2, hH2HI2, h3⟩ := eq_A214 θ hθ' hB
  obtain ⟨hH1H2, hH2MU⟩ := h3 h14
  have hA211 := (eq_A211 θ hθ' hB h14).2
  have hA212 := eq_A212 θ hθ' hB
  have hs : θ.μ * θ.B < 1 := by nlinarith
  -- HI2 ≤ MU
  have hHI2MU : HI2 θ ≤ MU θ := by
    unfold HI2 MU
    have h1 : 0 < 1 - θ.μ := by linarith
    have hC : 0 ≤ 1 + (1 - θ.μ) * θ.B := by nlinarith
    have : (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) / θ.A ≤
        (1 + (1 - θ.μ) * θ.B) / ((1 - θ.μ) * θ.A) := by
      rw [div_le_div_iff₀ hA (by positivity)]
      have : (θ.A + θ.B) * (1 - θ.μ) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hC hA.le)]
    linarith
  -- values
  set v1 := θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B) with hv1
  set v2F := θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
    with hv2F
  set v2I := θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B)) with hv2I
  set v3 := θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) with hv3
  set v4 := θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) with hv4
  have f1 : v1 < v2F := by
    have e : v2F - v1 = θ.μ * θ.A * (θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B)) := by
      rw [hv1, hv2F]; ring
    have : 0 < θ.μ * θ.A * (θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B)) := by
      have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
      have : 0 ≤ θ.φPP * θ.B := mul_nonneg (by linarith) hB0
      have : 0 < θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B) := by linarith
      positivity
    linarith
  have f2 : v1 < v2I := by
    have e : v2I - v1 = θ.μ * θ.B * θ.A := by rw [hv1, hv2I]; ring
    have : 0 < θ.μ * θ.B * θ.A := by positivity
    linarith
  have f3 : v2F < v3 := by
    have e : v3 - v2F = θ.μ * θ.A * ((1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP)) := by
      rw [hv3, hv2F]; ring
    have : 0 < θ.μ * θ.A * ((1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP)) := by
      have : 0 < (1 - θ.μ * θ.B) * (1 - θ.φPN) := mul_pos (by linarith) (by linarith)
      have : 0 ≤ θ.B * (1 - θ.φPP) := mul_nonneg hB0 (by linarith)
      have : 0 < (1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP) := by linarith
      positivity
    linarith
  have f4 : v2I < v3 := by
    have e : v3 - v2I = θ.μ * θ.A * (1 - θ.μ * θ.B) := by rw [hv3, hv2I]; ring
    have : 0 < θ.μ * θ.A * (1 - θ.μ * θ.B) := by
      have : 0 < 1 - θ.μ * θ.B := by linarith
      positivity
    linarith
  have f5 : v3 < v4 := by
    have e : v4 - v3 = θ.μ * (θ.A + θ.B) * ((1 - θ.μ) * θ.A) := by rw [hv3, hv4]; ring
    have : 0 < θ.μ * (θ.A + θ.B) * ((1 - θ.μ) * θ.A) := by
      have : 0 < 1 - θ.μ := by linarith
      have : 0 < θ.A + θ.B := by linarith
      positivity
    linarith
  -- strict comparison of the second steps
  have hstrict : v2F < v2I ↔ mu0 θ < θ.μ := by
    have e : v2I - v2F = θ.μ * θ.A * (θ.B * (1 - θ.φPP) - θ.φPN + θ.μ * θ.B * θ.φPN) := by
      rw [hv2I, hv2F]; ring
    have e2 : mu0 θ = (θ.φPN - θ.B * (1 - θ.φPP)) / (θ.B * θ.φPN) := by
      unfold mu0; field_simp
    have hμA : 0 < θ.μ * θ.A := by positivity
    rw [e2, div_lt_iff₀ (by positivity)]
    constructor
    · intro h
      have h1 : 0 < θ.μ * θ.A * (θ.B * (1 - θ.φPP) - θ.φPN + θ.μ * θ.B * θ.φPN) := by linarith
      have h2 := pos_of_mul_pos_right h1 hμA.le
      nlinarith
    · intro h
      have : 0 < θ.B * (1 - θ.φPP) - θ.φPN + θ.μ * θ.B * θ.φPN := by nlinarith
      have := mul_pos hμA this
      linarith
  have hHI1HI2 : HI1 θ ≤ HI2 θ := le_trans hHI1H2 hH2HI2
  refine ⟨fun M hM hML => ?_, fun M hMU => ?_, fun M hM => ?_⟩
  · have h1 : M < H1 θ := lt_of_lt_of_le hML (min_le_left _ _)
    have h2 : M < HI1 θ := lt_of_lt_of_le hML (min_le_right _ _)
    rw [hA211 M hM, hA212 M hM, if_pos h1, if_pos h2]
  · have hM : 0 ≤ M := by
      have : 0 ≤ MU θ := by
        unfold MU
        have : 0 < 1 - θ.μ := by linarith
        have : 0 ≤ 1 + (1 - θ.μ) * θ.B := by nlinarith
        positivity
      linarith
    have n1 : ¬ M < H1 θ := by linarith
    have n2 : ¬ M < H2 θ := by linarith
    have n3 : ¬ M < MU θ := by linarith
    have n4 : ¬ M < HI1 θ := by linarith
    have n5 : ¬ M < HI2 θ := by linarith
    rw [hA211 M hM, hA212 M hM, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5]
  · unfold investsInterim
    rw [hA211 M hM, hA212 M hM, max_le_iff]
    by_cases hmu : mu0 θ < θ.μ
    · have hlt := hstrict.mpr hmu
      split_ifs <;> constructor <;> intro h <;>
        (try rcases h with ⟨h1, h2⟩ | ⟨h1, ⟨h2, h3⟩, h4⟩) <;>
        first
        | (exfalso; linarith)
        | (left; constructor <;> linarith)
        | (right; exact ⟨hmu, ⟨by linarith, by linarith⟩, by linarith⟩)
        | linarith
    · have hge : v2I ≤ v2F := not_lt.mp (fun h => hmu (hstrict.mp h))
      split_ifs <;> constructor <;> intro h <;>
        (try rcases h with ⟨h1, h2⟩ | ⟨h1, ⟨h2, h3⟩, h4⟩) <;>
        first
        | (exfalso; linarith)
        | (left; constructor <;> linarith)
        | linarith
