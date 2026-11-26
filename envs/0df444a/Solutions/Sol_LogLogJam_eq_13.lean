-- Prove2me | solution 1 for LogLogJam.eq_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:35:32.932839+00:00
-- url     : https://prove2.me/submissions/4f7d222e-1438-4952-82bd-7c6851bfa6bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LogLogJam_lemma_5_10
import Theorems.Thm_LogLogJam_lemma_6_1
import Theorems.Thm_LogLogJam_posterior_predictive_density
open MeasureTheory LogLogJam
open scoped ENNReal

private theorem average_cap (l : ℝ) (hl : 1 < l) (k : ℕ) (W : Q k → Q k → ℝ)
    (hw : IsCov k (Matrix.of W)) :
    ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, measFisher l k W θ) ≤
      (k:ℝ≥0∞) * ENNReal.ofReal (4 * energy l) := by
  cases k with
  | zero =>
    simp [measFisher, fisherInfo, outDens, dotProduct]
  | succ k =>
    have hb := (lemma_6_1 l hl.le (k+1) (by omega) W hw).1
    have he : 0 < energy l := by unfold energy; positivity
    calc
      _ ≤ ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal (((k+1:ℕ):ℝ)*Real.pi*(4*energy l-2)) := by gcongr
      _ = ENNReal.ofReal (((k+1:ℕ):ℝ)*(4*energy l-2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
      _ ≤ ENNReal.ofReal (((k+1:ℕ):ℝ)*(4*energy l)) := by
        apply ENNReal.ofReal_le_ofReal; gcongr <;> linarith
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; norm_cast

theorem solution (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (Gpot lam) ≤ Gpot lam H + (k : ℝ≥0∞) * (Gpot lam H) ^ (1 / 2 : ℝ) := by
  have hl : 0 < lam := by linarith
  have he : 0 < energy lam := by unfold energy; positivity
  let p := postFisher lam H
  let A := ENNReal.ofReal (8*Real.pi*energy lam)
  let D := A^2
  have ha : 0 < A := ENNReal.ofReal_pos.mpr (by positivity)
  have hd0 : D ≠ 0 := pow_ne_zero _ ha.ne'
  have hdtop : D ≠ ∞ := by dsimp [D,A]; finiteness
  have hid : D⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hd0
  have hscale : ENNReal.ofReal ((8*Real.pi*energy lam)^2) = D := ENNReal.ofReal_pow (by positivity) _
  let w := fun y => ENNReal.ofReal (predDens lam H k W y)
  obtain ⟨hwm,hw1⟩ := posterior_predictive_density lam hlam H hH k W hW
  have heq : nextCondExp lam H k W (Gpot lam) =
      (1 + nextCondExp lam H k W (postFisher lam)) / D := by
    unfold nextCondExp Gpot
    simp only [hscale, div_eq_mul_inv, ← mul_assoc, lintegral_mul_const' _ _ hid,
      mul_add, mul_one, lintegral_add_left hwm, hw1]
  obtain ⟨hpost, hgain⟩ := lemma_5_10 lam hlam H hH k W hW
  have hπ : (1:ℝ≥0∞) ≤ ENNReal.ofReal Real.pi := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show 1 ≤ Real.pi by linarith [Real.pi_gt_three]))
  let R := (1 + p) ^ (1/2 : ℝ)
  have hR : (1:ℝ≥0∞) ≤ R := by
    calc
      _ = (1:ℝ≥0∞)^(1/2:ℝ) := by simp
      _ ≤ _ := ENNReal.rpow_le_rpow le_self_add (by norm_num)
  have hpR : p^(1/2:ℝ) ≤ R := ENNReal.rpow_le_rpow le_add_self (by norm_num)
  have hconst : (1:ℝ≥0∞) ≤ ENNReal.ofReal Real.pi * R := by simpa using mul_le_mul' hπ hR
  have hterm : 1 + ENNReal.ofReal Real.pi * p^(1/2:ℝ) ≤
      ENNReal.ofReal Real.pi*R + ENNReal.ofReal Real.pi*R :=
    add_le_add hconst (by gcongr)
  have hh : nextCondExp lam H k W (postFisher lam) ≤ p + (k:ℝ≥0∞)*A*R := by
    rw [hpost]
    refine add_le_add le_rfl ?_
    refine hgain.trans ?_
    calc
      _ ≤ (ENNReal.ofReal Real.pi*R + ENNReal.ofReal Real.pi*R) *
          ((k:ℝ≥0∞)*ENNReal.ofReal (4*energy lam)) :=
        mul_le_mul' hterm (average_cap lam hlam k W hW)
      _ = _ := by
        have hA : A = (ENNReal.ofReal Real.pi + ENNReal.ofReal Real.pi) * ENNReal.ofReal (4*energy lam) := by
          rw [← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le, ← ENNReal.ofReal_mul (by positivity)]
          dsimp [A]; congr 1; ring
        rw [← add_mul, hA]; ac_rfl
  have hG : Gpot lam H = (1+p)/D := by simp [Gpot,hscale,p]
  have hRt : R = Gpot lam H ^ (1/2:ℝ) * A := by
    have hs : 1+p = Gpot lam H * D := by rw [hG, ENNReal.div_mul_cancel hd0 hdtop]
    dsimp [R]; rw [hs, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    dsimp [D]; rw [← ENNReal.rpow_natCast_mul]; norm_num
  rw [heq]
  apply (ENNReal.div_le_iff hd0 hdtop).mpr
  calc
    _ ≤ 1+(p + (k:ℝ≥0∞)*A*R) := add_le_add le_rfl hh
    _ = _ := by
      rw [add_mul, ← add_assoc, hRt, show Gpot lam H * D = 1+p by rw [hG, ENNReal.div_mul_cancel hd0 hdtop]]
      dsimp [D]; rw [pow_two]; ac_rfl
