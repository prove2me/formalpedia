-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.nash_product_maximizer_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:06.545719+00:00
-- url     : https://prove2.me/submissions/206c2bde-28d0-4cab-817c-54c204ccb9ac

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem nash_product_maximizer_exists_unique (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_zero : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hS_gain : ∃ s ∈ S, 0 < s.1 ∧ 0 < s.2) :
    ∃! p : ℝ × ℝ, p ∈ S ∧ 0 < p.1 ∧ 0 < p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 := by
  set Q : Set (ℝ × ℝ) := {u | 0 ≤ u.1 ∧ 0 ≤ u.2} with hQ
  have hQc : IsClosed Q := by
    refine IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (isClosed_le continuous_const continuous_snd)
  have hK : IsCompact (S ∩ Q) := hS_compact.inter_right hQc
  have hne : (S ∩ Q).Nonempty := ⟨(0, 0), hS_zero, le_refl _, le_refl _⟩
  obtain ⟨p, hpK, hpmax⟩ := hK.exists_isMaxOn hne
    ((continuous_fst.mul continuous_snd).continuousOn)
  obtain ⟨hpS, hp1, hp2⟩ := hpK
  have hprod : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ p.1 * p.2 := fun s hs h1 h2 =>
    hpmax ⟨hs, h1, h2⟩
  obtain ⟨s0, hs0, hs01, hs02⟩ := hS_gain
  have hpos : 0 < p.1 * p.2 :=
    lt_of_lt_of_le (mul_pos hs01 hs02) (hprod s0 hs0 hs01.le hs02.le)
  have hp1' : 0 < p.1 := lt_of_le_of_ne hp1 (fun h => by rw [← h] at hpos; simp at hpos)
  have hp2' : 0 < p.2 := lt_of_le_of_ne hp2 (fun h => by rw [← h] at hpos; simp at hpos)
  have hstrict : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 := by
    intro s hs h1 h2 hne
    by_contra hge
    push Not at hge
    have hle := hprod s hs h1 h2
    have heq : s.1 * s.2 = p.1 * p.2 := le_antisymm hle hge
    have hspos : 0 < s.1 * s.2 := heq ▸ hpos
    have hs1 : 0 < s.1 :=
      lt_of_le_of_ne h1 (fun h => by rw [← h, zero_mul] at hspos; exact lt_irrefl _ hspos)
    have hs2 : 0 < s.2 :=
      lt_of_le_of_ne h2 (fun h => by rw [← h, mul_zero] at hspos; exact lt_irrefl _ hspos)
    -- midpoint
    have hq : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • s ∈ S :=
      hS_convex hpS hs (by norm_num) (by norm_num) (by norm_num)
    have hqx : 0 ≤ ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • s).1 := by simp; linarith
    have hqy : 0 ≤ ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • s).2 := by simp; linarith
    have hqle := hprod _ hq hqx hqy
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hqle
    set m := p.1 * p.2 with hm
    -- p1 s2 + s1 p2 ≤ 2m
    have hsum : p.1 * s.2 + s.1 * p.2 ≤ 2 * m := by nlinarith
    have hxy : (p.1 * s.2) * (s.1 * p.2) = m * m := by
      calc (p.1 * s.2) * (s.1 * p.2) = (p.1 * p.2) * (s.1 * s.2) := by ring
        _ = m * m := by rw [heq]
    have hx : 0 < p.1 * s.2 := mul_pos hp1' hs2
    have hy : 0 < s.1 * p.2 := mul_pos hs1 hp2'
    have hxeq : p.1 * s.2 = s.1 * p.2 := by nlinarith [sq_nonneg (p.1 * s.2 - s.1 * p.2)]
    have hxm : p.1 * s.2 = m := by nlinarith
    have hs2p : s.2 = p.2 := by
      have : p.1 * s.2 = p.1 * p.2 := hxm
      exact mul_left_cancel₀ hp1'.ne' this
    have hs1p : s.1 = p.1 := by
      have : s.1 * s.2 = p.1 * p.2 := heq
      rw [hs2p] at this
      exact mul_right_cancel₀ hp2'.ne' this
    exact hne (Prod.ext hs1p hs2p)
  refine ⟨p, ⟨hpS, hp1', hp2', hstrict⟩, ?_⟩
  rintro q ⟨hqS, hq1, hq2, hqstrict⟩
  by_contra hne
  have h1 := hqstrict p hpS hp1 hp2 (Ne.symm hne)
  have h2 := hstrict q hqS hq1.le hq2.le hne
  linarith

end NashWork

theorem solution (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_zero : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hS_gain : ∃ s ∈ S, 0 < s.1 ∧ 0 < s.2) :
    ∃! p : ℝ × ℝ, p ∈ S ∧ 0 < p.1 ∧ 0 < p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 :=
  NashWork.nash_product_maximizer_exists_unique S hS_compact hS_convex hS_zero hS_gain

#print axioms solution
