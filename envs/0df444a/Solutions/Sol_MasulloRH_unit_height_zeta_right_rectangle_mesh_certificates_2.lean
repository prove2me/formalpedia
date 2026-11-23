-- Prove2me | solution 2 for MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:33:52.096259+00:00
-- url     : https://prove2.me/submissions/9bf06c8c-662d-475d-937e-ab24e4b2f30c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

-- Step 1: `mathlib_riemannHypothesis` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hhalf := mathlib_riemannHypothesis s hz htriv hs_one
  linarith

end

-- Step 2: `MasulloRH.zero_free_right` implies `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` (accepted reduction of `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates`).
section

set_option autoImplicit false

private theorem meshCoordinate_mem_Icc {a b : ℝ} (hab : a ≤ b) {m : ℕ}
    (hm : 0 < m) (i : Fin (m + 1)) :
    a + (b - a) * ((i.val : ℝ) / m) ∈ Set.Icc a b := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hfrac : (i.val : ℝ) / m ≤ 1 := (div_le_one hmReal).2 hi
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hstep₀ := mul_nonneg hwidth (div_nonneg (Nat.cast_nonneg i.val) hmReal.le)
  have hstep₁ := mul_le_of_le_one_right hwidth hfrac
  exact ⟨by linarith only [hstep₀], by linarith only [hstep₁]⟩

theorem solution (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∃ (m : ℕ) (M : ℚ), 0 < m ∧ 0 ≤ M ∧
      (∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
        ‖deriv riemannZeta s‖ ≤ (M : ℝ)) ∧
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        2 * (M : ℝ) / m < ‖riemannZeta s‖ := by
  intro margin left bottom top
  let R := Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top)
  have hmargin : 0 < margin := by dsimp [margin]; positivity
  have hmargin_le : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hleft : left ≤ 1 := by dsimp [left]; linarith only [hmargin_le]
  have hbottom : bottom ≤ top := by dsimp [bottom, top]; linarith only [hmargin_le]
  have hbottom_pos : 0 < bottom := by dsimp [bottom, margin]; positivity
  have hcompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hnonempty : R.Nonempty :=
    ⟨⟨left, bottom⟩, Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hleft⟩, ⟨le_rfl, hbottom⟩⟩⟩

  -- Both the zeta function and its derivative are continuous on the rectangle.
  have hpole {s : ℂ} (hs : s ∈ R) : s ≠ 1 := by
    intro h
    have him : bottom ≤ s.im := (Complex.mem_reProdIm.mp hs).2.1
    rw [h, Complex.one_im] at him
    exact (not_le_of_gt hbottom_pos) him
  have hanalytic : AnalyticOnNhd ℂ riemannZeta R :=
    analyticOn_riemannZeta.mono fun _ hs => hpole hs
  obtain ⟨smax, _, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    hanalytic.deriv.continuousOn.norm
  obtain ⟨M, hM⟩ := exists_rat_gt ‖deriv riemannZeta smax‖
  have hMreal : 0 ≤ (M : ℝ) := (norm_nonneg _).trans hM.le
  have hMnonneg : 0 ≤ M := by exact_mod_cast hMreal

  -- The imported zero-free theorem gives a strictly positive compact minimum.
  obtain ⟨smin, hsmin, hmin⟩ := hcompact.exists_isMinOn hnonempty
    hanalytic.continuousOn.norm
  let δ := ‖riemannZeta smin‖
  have hδ : 0 < δ := by
    have hl : left ≤ smin.re := (Complex.mem_reProdIm.mp hsmin).1.1
    dsimp [left] at hl
    have hr : 1 / 2 < smin.re := by linarith only [hmargin, hl]
    exact norm_pos_iff.mpr (MasulloRH.zero_free_right smin hr (hpole hsmin))

  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (2 * (M : ℝ) / δ))
  have hmReal : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmPos : 0 < m := by exact_mod_cast hmReal
  have hmesh : 2 * (M : ℝ) / m < δ := by
    have h := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt hm)
    exact (div_lt_iff₀ hmReal).2 (by simpa only [mul_comm δ (m : ℝ)] using h)
  refine ⟨m, M, hmPos, hMnonneg, fun s hs => (hmax hs).trans hM.le, ?_⟩
  intro i j s
  have hs : s ∈ R := Complex.mem_reProdIm.mpr
    ⟨meshCoordinate_mem_Icc hleft hmPos i, meshCoordinate_mem_Icc hbottom hmPos j⟩
  exact hmesh.trans_le (hmin hs)

end
