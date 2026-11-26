-- Prove2me | solution 1 for MasulloRH.dyadic_exp_row_sound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T10:12:02.894459+00:00
-- url     : https://prove2.me/submissions/224ee50a-df3f-4b8c-8e60-d86df839d20f

import Definitions.Def_MasulloRH_DyadicExpRows
import Theorems.Thm_MasulloRH_HeightTwoScalar_exp_row_sound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.HeightTwoScalar MasulloRH.DyadicExp
open scoped BigOperators

theorem solution (t : ℚ) :
    (row t).argument = t ∧ (row t).Valid ∧ 0 ≤ (row t).lower ∧
      ((row t).lower:ℝ) ≤ Real.exp (t:ℝ) ∧ Real.exp (t:ℝ) ≤ ((row t).upper:ℝ) := by
  have hscale : 0 < scale := by norm_num [scale]
  have hd (v : ℚ) : down v ≤ v :=
    (div_le_iff₀ hscale).2 (Int.floor_le _)
  have hu (v : ℚ) : v ≤ up v :=
    (le_div_iff₀ hscale).2 (Int.le_ceil _)
  have hdn (v : ℚ) (h : 0 ≤ v) : 0 ≤ down v := by
    apply div_nonneg _ hscale.le
    exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg h hscale.le))
  have main : (row t).argument = t ∧ (row t).Valid ∧ 0 ≤ (row t).lower := by
    by_cases hz : t = 0
    · subst t
      norm_num [row, ExpRow.Valid]
    by_cases hc : t ≤ -64
    · have eq : row t = ⟨3,t,0,1/(2:ℚ)^64,0,0,0,0,0,64⟩ := by simp [row,hz,hc]
      rw [eq]
      refine ⟨rfl,?_,le_rfl⟩
      change (64:ℚ) ≤ -t ∧ (0:ℚ) ≤ 0 ∧ 1/(2:ℚ)^64 ≤ 1/2^64
      exact ⟨by linarith,le_rfl,le_rfl⟩
    let p := max 1 ⌈4*|t|⌉₊
    let x := |t| / (p:ℚ)
    let a := max (1/2) (down (taylorRat x 9 - remainderRat x 9))
    let b := up (taylorRat x 9 + remainderRat x 9)
    have hp : 0 < p := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    have hp' : (0:ℚ)<p := by exact_mod_cast hp
    have ht : 4*|t| ≤ (p:ℚ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right 1 ⌈4*|t|⌉₊))
    have hx : 0 ≤ x := div_nonneg (abs_nonneg _) hp'.le
    have hx' : x ≤ 1 := (div_le_iff₀ hp').2 (by linarith [abs_nonneg t])
    have hpx : (p:ℚ)*x = |t| := by dsimp [x]; field_simp
    have hT : 1 ≤ taylorRat x 9 := by
      have h := Finset.single_le_sum (f := fun m : ℕ => x^m/(m.factorial:ℚ))
        (fun m _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
        (by decide : 0 ∈ Finset.range 9)
      simpa [taylorRat] using h
    have hR : remainderRat x 9 ≤ 1/2 := by
      have h : x^9 ≤ 1 := pow_le_one₀ hx hx'
      norm_num [remainderRat, Nat.factorial]
      linarith
    have hR0 : 0 ≤ remainderRat x 9 := by unfold remainderRat; positivity
    have ha : 0 < a := lt_of_lt_of_le (by norm_num : (0:ℚ)<1/2) (le_max_left _ _)
    have hal : a ≤ taylorRat x 9 - remainderRat x 9 :=
      max_le (by linarith) (hd _)
    have hbu : taylorRat x 9 + remainderRat x 9 ≤ b := hu _
    have hb : 0 ≤ b := by linarith
    by_cases hpos : 0 < t
    · have eq : row t = ⟨1,t,down (a^p),up (b^p),x,a,b,p,9,0⟩ := by
        simp only [row,if_neg hz,if_neg hc,if_pos hpos]; rfl
      rw [eq]
      refine ⟨rfl,?_,hdn _ (pow_nonneg ha.le _)⟩
      change PositiveExpCheck t x a b (down (a^p)) (up (b^p)) p 9
      exact ⟨hx,hx',by decide,(abs_of_pos hpos).symm.trans hpx.symm,ha,hal,hbu,hd _,hu _⟩
    · have eq : row t = ⟨2,t,down (1/b^p),up (1/a^p),x,a,b,p,9,0⟩ := by
        simp only [row,if_neg hz,if_neg hc,if_neg hpos]; rfl
      rw [eq]
      refine ⟨rfl,?_,hdn _ (by positivity)⟩
      change NegativeExpCheck (-t) x a b (down (1/b^p)) (up (1/a^p)) p 9
      exact ⟨hx,hx',by decide,(abs_of_nonpos (le_of_not_gt hpos)).symm.trans hpx.symm,
        ha,hal,hbu,hd _,hu _⟩
  obtain ⟨harg,hv,hn⟩ := main
  have he := MasulloRH.HeightTwoScalar.exp_row_sound (row t) hv
  rw [harg] at he
  exact ⟨harg,hv,hn,he⟩
