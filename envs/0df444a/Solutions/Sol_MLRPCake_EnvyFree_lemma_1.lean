-- Prove2me | solution 1 for MLRPCake.EnvyFree.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:46:17.255703+00:00
-- url     : https://prove2.me/submissions/f98fdcb0-05e1-4a6e-b09c-3f771586b8b1

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace Aux_MLRPl1
open MLRPCake.EnvyFree MeasureTheory

lemma ii_sub {g : ℝ → ℝ} (hg : IsDensity g) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable g volume a b := by
  apply hg.2.2.1.mono_set
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
  exact Set.Icc_subset_Icc ha hb

lemma int_pos {g : ℝ → ℝ} (hg : IsDensity g) (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < g x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : 0 < ∫ t in a..b, g t := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (ii_sub hg ha hab.le hb) _ hab
  intro x hx
  exact hpos x ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩

lemma int_nonneg {g : ℝ → ℝ} (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < g x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : 0 ≤ ∫ t in a..b, g t := by
  apply intervalIntegral.integral_nonneg hab
  intro x hx
  exact (hpos x ⟨ha.trans hx.1, hx.2.trans hb⟩).le

end Aux_MLRPl1

open MLRPCake.EnvyFree Aux_MLRPl1 in
theorem solution (fi fj : ℝ → ℝ) (hi : IsDensity fi) (hj : IsDensity fj)
    (hpos_i : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fi x) (hpos_j : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fj x)
    (hmlrp : ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ 1 → fj b / fi b ≤ fj c / fi c) :
    (∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c < d → d ≤ 1 →
      (∫ t in a..b, fj t) / (∫ t in a..b, fi t) ≤ (∫ t in c..d, fj t) / (∫ t in c..d, fi t)) ∧
    (∀ a x b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 →
      (∫ t in x..b, fi t) / (∫ t in a..b, fi t) ≤ (∫ t in x..b, fj t) / (∫ t in a..b, fj t)) := by
  have part1 : ∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c < d → d ≤ 1 →
      (∫ t in a..b, fj t) / (∫ t in a..b, fi t) ≤ (∫ t in c..d, fj t) / (∫ t in c..d, fi t) := by
    intro a b c d ha hab hbc hcd hd
    have hb0 : 0 ≤ b := ha.trans hab
    have hb1 : b ≤ 1 := hbc.trans (hcd.le.trans hd)
    have hc0 : 0 ≤ c := hb0.trans hbc
    have hfib := hpos_i b ⟨hb0, hb1⟩
    have hfjb := hpos_j b ⟨hb0, hb1⟩
    set R : ℝ := fj b / fi b with hR
    have hR0 : 0 < R := div_pos hfjb hfib
    -- left interval
    have hleft : (∫ t in a..b, fj t) ≤ R * ∫ t in a..b, fi t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab (ii_sub hj ha hab hb1)
        ((ii_sub hi ha hab hb1).const_mul R)
      intro t ht
      have ht0 : 0 ≤ t := ha.trans ht.1
      have hfit := hpos_i t ⟨ht0, ht.2.trans hb1⟩
      have := hmlrp t b ht0 ht.2 hb1
      rw [div_le_iff₀ hfit] at this
      calc fj t ≤ fj b / fi b * fi t := this
        _ = R * fi t := rfl
    have hright : R * (∫ t in c..d, fi t) ≤ ∫ t in c..d, fj t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hcd.le ((ii_sub hi hc0 hcd.le hd).const_mul R)
        (ii_sub hj hc0 hcd.le hd)
      intro t ht
      have ht0 : 0 ≤ t := hc0.trans ht.1
      have hfit := hpos_i t ⟨ht0, ht.2.trans hd⟩
      have := hmlrp b t hb0 (hbc.trans ht.1) (ht.2.trans hd)
      rw [le_div_iff₀ hfit] at this
      exact this
    have hcdpos := int_pos hi hpos_i hc0 hcd hd
    have hRle : R ≤ (∫ t in c..d, fj t) / (∫ t in c..d, fi t) := by
      rw [le_div_iff₀ hcdpos]; exact hright
    refine le_trans ?_ hRle
    rcases eq_or_lt_of_le hab with h | h
    · subst h; simp [hR0.le]
    · rw [div_le_iff₀ (int_pos hi hpos_i ha h hb1)]
      exact hleft
  refine ⟨part1, ?_⟩
  intro a x b ha hax hxb hb
  have hx0 : 0 ≤ x := ha.trans hax
  rcases eq_or_lt_of_le hxb with h | h
  · subst h; simp
  have hsplit_i : (∫ t in a..b, fi t) = (∫ t in a..x, fi t) + ∫ t in x..b, fi t :=
    (intervalIntegral.integral_add_adjacent_intervals (ii_sub hi ha hax (hxb.trans hb))
      (ii_sub hi hx0 hxb hb)).symm
  have hsplit_j : (∫ t in a..b, fj t) = (∫ t in a..x, fj t) + ∫ t in x..b, fj t :=
    (intervalIntegral.integral_add_adjacent_intervals (ii_sub hj ha hax (hxb.trans hb))
      (ii_sub hj hx0 hxb hb)).symm
  have hq := int_pos hi hpos_i hx0 h hb
  have hQ := int_pos hj hpos_j hx0 h hb
  have hp := int_nonneg hpos_i ha hax (hxb.trans hb)
  have hP := int_nonneg hpos_j ha hax (hxb.trans hb)
  have hcross : (∫ t in a..x, fj t) * (∫ t in x..b, fi t) ≤
      (∫ t in x..b, fj t) * (∫ t in a..x, fi t) := by
    rcases eq_or_lt_of_le hax with h' | h'
    · subst h'; simp
    · have hp' := int_pos hi hpos_i ha h' (hxb.trans hb)
      have := part1 a x x b ha hax le_rfl h hb
      rw [div_le_div_iff₀ hp' hq] at this
      exact this
  rw [hsplit_i, hsplit_j, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hcross]
