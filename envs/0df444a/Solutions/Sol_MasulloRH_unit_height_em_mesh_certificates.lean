-- Prove2me | solution 1 for MasulloRH.unit_height_em_mesh_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:34:30.261595+00:00
-- url     : https://prove2.me/submissions/45098543-2a56-40c3-8f8f-ad03741ba0d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order

import Mathlib.Data.Finset.Max
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Theorems.Thm_MasulloRH_unit_height_em_mesh_pointwise_certificates

set_option autoImplicit false

open Set

theorem solution (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ (m K N : ℕ), 0 < m ∧ 1 ≤ K ∧ 1 ≤ N ∧
      let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
        (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by
  intro margin left bottom top M
  obtain ⟨m, hm, hPointwise⟩ := MasulloRH.unit_height_em_mesh_pointwise_certificates n k
  let err (K N : ℕ) : ℚ :=
    ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
  let sample (i j : Fin (m + 1)) : ℂ :=
    ⟨left + (1 - left) * ((i.val : ℝ) / m),
      bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
  let cost : ℚ := 2 * M / m
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmargin : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hLeft : left ≤ 1 := by dsimp [left]; linarith
  have hBottom : bottom ≤ top := by dsimp [bottom, top]; linarith
  have hCoord {a b : ℝ} (hab : a ≤ b) (i : Fin (m + 1)) :
      a + (b - a) * ((i.val : ℝ) / m) ∈ Icc a b := by
    have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hq : (i.val : ℝ) / m ∈ Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hm'.le, (div_le_one hm').2 hi⟩
    have hlo := mul_nonneg (sub_nonneg.mpr hab) hq.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) hq.2
    exact ⟨by linarith, by linarith⟩
  have hIn (i j : Fin (m + 1)) :
      sample i j ∈ Complex.reProdIm (Icc left 1) (Icc bottom top) :=
    Complex.mem_reProdIm.mpr ⟨hCoord hLeft i, hCoord hBottom j⟩
  have hEncl (i j : Fin (m + 1)) (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
      ‖riemannZeta (sample i j) - ZetaReflection.EMHigh.emFinite K (sample i j) N‖ ≤
        (err K N : ℝ) :=
    MasulloRH.unit_height_em_enclosure n k K N hK hN _ (hIn i j)

  -- Transfer each pointwise certificate to a strict, precision-independent margin.
  have hMargin (i j : Fin (m + 1)) : (cost : ℝ) < ‖riemannZeta (sample i j)‖ := by
    obtain ⟨K, N, hK, hN, hGap⟩ := hPointwise i j
    change ((cost + err K N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (sample i j) N‖ at hGap
    push_cast at hGap
    have hError := hEncl i j K N hK hN
    have hTriangle := norm_sub_norm_le (ZetaReflection.EMHigh.emFinite K (sample i j) N)
      (riemannZeta (sample i j))
    rw [norm_sub_rev] at hTriangle
    linarith

  let gap (p : Fin (m + 1) × Fin (m + 1)) : ℝ :=
    ‖riemannZeta (sample p.1 p.2)‖ - (cost : ℝ)
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ gap Finset.univ_nonempty
  let δ := gap p
  have hδ : 0 < δ := sub_pos.mpr (hMargin p.1 p.2)
  have hMin (i j : Fin (m + 1)) :
      δ ≤ ‖riemannZeta (sample i j)‖ - (cost : ℝ) :=
    hp (i, j) (Finset.mem_univ _)

  -- At first order the enclosure radius is c / N², uniformly over the mesh.
  let c : ℝ := ((100002 + n + 2 * 1 : ℕ) : ℝ) ^ 3 / 108
  have hCastErr (N : ℕ) : (err 1 N : ℝ) = c / (N : ℝ) ^ 2 := by
    dsimp only [err, c]
    push_cast
    norm_num
    rw [div_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * c / δ))
  have hNReal : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNPos : 1 ≤ N := by exact_mod_cast hNReal.le
  have hNLarge : 2 * c < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
  have hNSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNReal, sq_nonneg ((N : ℝ) - 1)]
  have hSmall : 2 * (err 1 N : ℝ) < δ := by
    rw [hCastErr, ← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity)).2
      (hNLarge.trans_le (mul_comm (N : ℝ) δ ▸
        mul_le_mul_of_nonneg_left hNSq hδ.le))

  refine ⟨m, 1, N, hm, le_rfl, hNPos, ?_⟩
  change ∀ i j : Fin (m + 1),
    ((cost + err 1 N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite 1 (sample i j) N‖
  intro i j
  push_cast
  have hError := hEncl i j 1 N le_rfl hNPos
  have hTriangle := norm_sub_norm_le (riemannZeta (sample i j))
    (ZetaReflection.EMHigh.emFinite 1 (sample i j) N)
  linarith [hMin i j]
