-- Prove2me | solution 1 for MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:49:45.621041+00:00
-- url     : https://prove2.me/submissions/c8770f91-fd05-4314-ab18-6da1b12c2f08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_deriv_bound
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Theorems.Thm_MasulloRH_unit_height_em_mesh_certificates
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

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
  obtain ⟨m, K, N, hm, hK, hN, hmesh⟩ := MasulloRH.unit_height_em_mesh_certificates n k
  let M : ℚ := 16 * (100003 + n)
  refine ⟨m, M, hm, ?_, ?_, ?_⟩
  · dsimp [M]
    positivity
  · intro s hs
    have hderiv := MasulloRH.unit_height_zeta_right_rectangle_deriv_bound n k s hs
    have hM_cast : (M : ℝ) = (16 : ℝ) * (100003 + n) := by
      dsimp [M]
      push_cast
      ring
    rw [hM_cast]
    exact hderiv
  · intro i j
    dsimp only
    set s : ℂ :=
      ⟨left + (1 - left) * ((i.val : ℝ) / m),
        bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hmargin_pos : 0 < margin := by
      dsimp [margin]
      positivity
    have hmargin_le : margin ≤ 1 / 3 := by
      dsimp [margin]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hleft_le_one : left ≤ 1 := by
      dsimp [left]
      linarith
    have hbottom_le_top : bottom ≤ top := by
      dsimp [bottom, top]
      linarith
    have hi_nonneg : 0 ≤ (i.val : ℝ) / (m : ℝ) := by positivity
    have hi_le_one : (i.val : ℝ) / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hm_pos, one_mul]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)
    have hj_nonneg : 0 ≤ (j.val : ℝ) / (m : ℝ) := by positivity
    have hj_le_one : (j.val : ℝ) / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hm_pos, one_mul]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt)
    have hs_mem : s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top) := by
      refine Complex.mem_reProdIm.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · change left ≤ left + (1 - left) * ((i.val : ℝ) / m)
        have : 0 ≤ (1 - left) * ((i.val : ℝ) / m) :=
          mul_nonneg (sub_nonneg.mpr hleft_le_one) hi_nonneg
        linarith
      · change left + (1 - left) * ((i.val : ℝ) / m) ≤ 1
        have : (1 - left) * ((i.val : ℝ) / m) ≤ (1 - left) * 1 :=
          mul_le_mul_of_nonneg_left hi_le_one (sub_nonneg.mpr hleft_le_one)
        linarith
      · change bottom ≤ bottom + (top - bottom) * ((j.val : ℝ) / m)
        have : 0 ≤ (top - bottom) * ((j.val : ℝ) / m) :=
          mul_nonneg (sub_nonneg.mpr hbottom_le_top) hj_nonneg
        linarith
      · change bottom + (top - bottom) * ((j.val : ℝ) / m) ≤ top
        have : (top - bottom) * ((j.val : ℝ) / m) ≤ (top - bottom) * 1 :=
          mul_le_mul_of_nonneg_left hj_le_one (sub_nonneg.mpr hbottom_le_top)
        linarith
    let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
    have henc :
        ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤ (err : ℝ) :=
      MasulloRH.unit_height_em_enclosure n k K N hK hN s hs_mem
    have hpt :
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ :=
      hmesh i j
    have htri :
        ‖ZetaReflection.EMHigh.emFinite K s N‖ ≤
          ‖riemannZeta s‖ + ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ := by
      have h0 := norm_sub_le (riemannZeta s) (riemannZeta s - ZetaReflection.EMHigh.emFinite K s N)
      have hsub : riemannZeta s - (riemannZeta s - ZetaReflection.EMHigh.emFinite K s N) =
          ZetaReflection.EMHigh.emFinite K s N := by ring
      rwa [hsub] at h0
    have hcast : ((2 * M / m + err : ℚ) : ℝ) = 2 * (M : ℝ) / (m : ℝ) + (err : ℝ) := by
      push_cast
      ring
    linarith
