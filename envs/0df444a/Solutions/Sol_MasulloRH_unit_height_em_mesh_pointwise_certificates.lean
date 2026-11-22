-- Prove2me | solution 1 for MasulloRH.unit_height_em_mesh_pointwise_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:11:23.077745+00:00
-- url     : https://prove2.me/submissions/0b71daa9-a032-4abb-bbf6-22f14b18e3d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order
import Theorems.Thm_MasulloRH_unit_height_em_adaptive_ball_certificates
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_deriv_bound

open Set
set_option autoImplicit false

theorem solution (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ m : ℕ, 0 < m ∧
      ∀ i j : Fin (m + 1), ∃ (K N : ℕ), 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by
  intro margin left bottom top M
  let R := Complex.reProdIm (Icc left 1) (Icc bottom top)
  let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
  let err (K N : ℕ) : ℚ :=
    ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
  obtain ⟨points, rad, hAtPoint, hCover⟩ := MasulloRH.unit_height_em_adaptive_ball_certificates n k
  have hM : 0 ≤ (M : ℝ) := by dsimp [M]; push_cast; positivity
  have hBot : 0 < bottom := by dsimp [bottom, margin]; positivity
  have hMargin : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hLeft : left ≤ 1 := by dsimp [left]; linarith
  have hBottom : bottom ≤ top := by dsimp [bottom, top]; linarith
  have hRNonempty : R.Nonempty :=
    ⟨⟨left, bottom⟩, Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hLeft⟩, ⟨le_rfl, hBottom⟩⟩⟩
  have hRCompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hRConv : Convex ℝ R := by
    change Convex ℝ ((Complex.reLm ⁻¹' Icc left 1) ∩ (Complex.imLm ⁻¹' Icc bottom top))
    exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
      ((convex_Icc _ _).linear_preimage Complex.imLm)
  have hDiff (s : ℂ) (hs : s ∈ R) : DifferentiableAt ℂ riemannZeta s := by
    apply differentiableAt_riemannZeta
    rintro rfl
    exact hBot.not_ge (by simpa only [Complex.one_im] using (Complex.mem_reProdIm.mp hs).2.1)
  have hD (s : ℂ) (hs : s ∈ R) : ‖deriv riemannZeta s‖ ≤ (M : ℝ) := by
    have h := MasulloRH.unit_height_zeta_right_rectangle_deriv_bound n k s hs
    dsimp [M]
    push_cast
    exact h
  have hEnc (s : ℂ) (hs : s ∈ R) (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
      ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤ (err K N : ℝ) :=
    MasulloRH.unit_height_em_enclosure n k K N hK hN s hs
  have hNonzero (s : ℂ) (hs : s ∈ R) : riemannZeta s ≠ 0 := by
    obtain ⟨p, hp, hr⟩ := hCover s hs
    change dist s (center p) < (rad p : ℝ) at hr
    obtain ⟨hpR, K, N, hK, hN, hgap⟩ := hAtPoint p hp
    change center p ∈ R at hpR
    change ((M * rad p + err K N : ℚ) : ℝ) <
      ‖ZetaReflection.EMHigh.emFinite K (center p) N‖ at hgap
    push_cast at hgap
    have hder := hRConv.norm_image_sub_le_of_norm_deriv_le hDiff hD hs hpR
    rw [← dist_eq_norm (center p) s, dist_comm (center p) s] at hder
    have htri := norm_sub_norm_le (ZetaReflection.EMHigh.emFinite K (center p) N)
      (riemannZeta (center p))
    rw [norm_sub_rev] at htri
    have hval := hEnc (center p) hpR K N hK hN
    have hrad := mul_le_mul_of_nonneg_left hr.le hM
    intro hZero
    rw [hZero, sub_zero] at hder
    linarith
  obtain ⟨smin, hsmin, hMin⟩ := hRCompact.exists_isMinOn hRNonempty
    (show ContinuousOn riemannZeta R from
      (fun s hs => (hDiff s hs).continuousAt.continuousWithinAt)).norm
  let δ := ‖riemannZeta smin‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hNonzero smin hsmin)

  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (4 * (M : ℝ) / δ))
  have hmReal : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmPos : 0 < m := by exact_mod_cast hmReal
  let cost : ℚ := 2 * M / m
  have hCost : (cost : ℝ) < δ / 2 := by
    have h := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hm)
    dsimp [cost]
    push_cast
    exact (div_lt_iff₀ hmReal).2 (by nlinarith)
  let c : ℝ := ((100002 + n + 2 * 1 : ℕ) : ℝ) ^ 3 / 108
  have hCastErr (N : ℕ) : (err 1 N : ℝ) = c / (N : ℝ) ^ 2 := by
    dsimp only [err, c]
    push_cast
    norm_num
    rw [div_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * c / δ))
  have hNReal : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNPos : 1 ≤ N := by exact_mod_cast hNReal.le
  have hNLarge : 4 * c < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
  have hNSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNReal, sq_nonneg ((N : ℝ) - 1)]
  have hSmall : 2 * (err 1 N : ℝ) < δ / 2 := by
    have hAux : 4 * c < (N : ℝ) ^ 2 * δ :=
      hNLarge.trans_le (mul_le_mul_of_nonneg_right hNSq hδ.le)
    rw [hCastErr, ← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  have hCoord {a b : ℝ} (hab : a ≤ b) (i : Fin (m + 1)) :
      a + (b - a) * ((i.val : ℝ) / m) ∈ Icc a b := by
    have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hq : (i.val : ℝ) / m ∈ Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hmReal.le, (div_le_one hmReal).2 hi⟩
    have hlo := mul_nonneg (sub_nonneg.mpr hab) hq.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) hq.2
    exact ⟨by linarith, by linarith⟩
  refine ⟨m, hmPos, ?_⟩
  intro i j
  let s : ℂ := ⟨left + (1 - left) * (i.val / (m : ℝ)),
    bottom + (top - bottom) * (j.val / (m : ℝ))⟩
  have hs : s ∈ R := Complex.mem_reProdIm.mpr ⟨hCoord hLeft i, hCoord hBottom j⟩
  refine ⟨1, N, le_rfl, hNPos, ?_⟩
  change ((cost + err 1 N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite 1 s N‖
  push_cast
  have hBound := hEnc s hs 1 N le_rfl hNPos
  have hTri := norm_sub_norm_le (riemannZeta s) (ZetaReflection.EMHigh.emFinite 1 s N)
  have hLower : δ ≤ ‖riemannZeta s‖ := hMin hs
  linarith
