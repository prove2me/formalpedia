-- Prove2me | solution 1 for InnovAlloc.Optimal.prop3_region_b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:31:29.693687+00:00
-- url     : https://prove2.me/submissions/4830bd3a-6409-40f6-a94e-a7f50ff4ace3

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

open InnovAlloc.Optimal in
theorem solution (α γ B : ℝ) (hs : Standing α γ)
    (ha0 : alphaLow ≤ α) (ha1 : α < 1 / 2) (hB : 2 < γ * B) :
    (profitMono γ B ≤ profitDuo α γ B ↔
      γ * B ∈ Set.Icc (bandLow α) (bandHigh α)) := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  obtain ⟨t, ht⟩ : ∃ t, t = γ * B := ⟨_, rfl⟩
  have ht2 : 2 < t := by rw [ht]; exact hB
  have htpos : 0 < t := by linarith
  have hpos : 0 < 1 - γ := by linarith
  have hk : 0 < 1 - 2 * α := by linarith
  set D := α ^ 2 + 16 * α - 8 with hDdef
  have hD : 0 ≤ D := by
    unfold alphaLow at ha0
    have h72 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  set s := Real.sqrt D with hsdef
  have hs2 : s ^ 2 = D := Real.sq_sqrt hD
  have hs0 : 0 ≤ s := Real.sqrt_nonneg D
  set X := (α ^ 2 * t - 8 * α + 8) / t with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    apply div_nonneg _ htpos.le
    nlinarith
  set q := (1 - 2 * α) * t ^ 2 - 2 * (1 - α) * t + 9 with hq
  have hMono : profitMono γ B = (1 - γ) * (1 - 1 / t) := by
    unfold profitMono
    rw [← ht, if_neg (by linarith)]
  have hDuo : profitDuo α γ B = (1 - γ) * (α - 4 / t + Real.sqrt X) := by
    unfold profitDuo
    rw [← ht, if_neg (by linarith)]
    have : γ * α ^ 2 * B = α ^ 2 * t := by rw [ht]; ring
    rw [this]
  have hA : profitMono γ B ≤ profitDuo α γ B ↔ 1 - α + 3 / t ≤ Real.sqrt X := by
    rw [hMono, hDuo]
    have e : 1 - α + 3 / t = (α - 4 / t + Real.sqrt X) - (1 - 1 / t) + (1 - α + 3 / t) -
        ((α - 4 / t + Real.sqrt X) - (1 - 1 / t)) := by ring
    constructor
    · intro h
      have := le_of_mul_le_mul_left h hpos
      have e2 : 3 / t = 4 / t - 1 / t := by ring
      linarith
    · intro h
      apply mul_le_mul_of_nonneg_left _ hpos.le
      have e2 : 3 / t = 4 / t - 1 / t := by ring
      linarith
  have hpos3 : 0 ≤ 1 - α + 3 / t := by
    have : 0 < 3 / t := by positivity
    linarith
  have hB' : 1 - α + 3 / t ≤ Real.sqrt X ↔ (1 - α + 3 / t) ^ 2 ≤ X :=
    Real.le_sqrt hpos3 hX0
  have e' : q = -(X - (1 - α + 3 / t) ^ 2) * t ^ 2 := by
    rw [hq, hX]
    field_simp
    ring
  have hC : (1 - α + 3 / t) ^ 2 ≤ X ↔ q ≤ 0 := by
    have htt : 0 < t ^ 2 := by positivity
    constructor
    · intro h
      rw [e']
      nlinarith [mul_nonneg (sub_nonneg.mpr h) htt.le]
    · intro h
      by_contra hc
      push_neg at hc
      have : 0 < ((1 - α + 3 / t) ^ 2 - X) * t ^ 2 := mul_pos (by linarith) htt
      rw [e'] at h
      nlinarith
  have hfac : (1 - 2 * α) * q = ((1 - 2 * α) * t - (1 - α)) ^ 2 - s ^ 2 := by
    rw [hs2, hq, hDdef]; ring
  have hD' : q ≤ 0 ↔ t ∈ Set.Icc (bandLow α) (bandHigh α) := by
    unfold bandLow bandHigh
    rw [← hsdef, Set.mem_Icc, div_le_iff₀ hk, le_div_iff₀ hk]
    constructor
    · intro h
      have h1 : ((1 - 2 * α) * t - (1 - α)) ^ 2 ≤ s ^ 2 := by nlinarith
      obtain ⟨l, u⟩ := abs_le_of_sq_le_sq' h1 hs0
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      have h3 : ((1 - 2 * α) * t - (1 - α)) ^ 2 ≤ s ^ 2 := by
        apply sq_le_sq'
        · linarith
        · linarith
      nlinarith
  rw [hA, hB', hC, hD', ht]
