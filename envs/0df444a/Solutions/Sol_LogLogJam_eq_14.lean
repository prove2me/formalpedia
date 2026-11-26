-- Prove2me | solution 1 for LogLogJam.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:15:41.692928+00:00
-- url     : https://prove2.me/submissions/d595f630-bf58-49a1-9104-4a4963f2ab67

import Theorems.Thm_LogLogJam_lemma_5_4
import Theorems.Thm_LogLogJam_lemma_5_9

open MeasureTheory LogLogJam
open scoped ENNReal

private theorem hist_dom {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (t : ℕ) (f g : Hist t → ℝ≥0∞)
    (h : ∀ x, f x ≤ c * g x) :
    histInt lam θ P t f ≤ c * histInt lam θ P t g := by
  induction t with
  | zero => exact h _
  | succ t ih =>
    simp only [histInt]
    apply ih
    intro H
    rw [← lintegral_const_mul' _ _ hc]
    apply lintegral_mono
    intro s
    dsimp only
    rw [← lintegral_const_mul' _ _ hc]
    apply lintegral_mono
    intro y
    dsimp only
    calc
      _ ≤ _ * (c * g _) := by gcongr; apply h
      _ = _ := by ac_rfl

theorem solution {T : ℕ} (P : GaussProtocol T) (lam ε : ℝ) (hlam : 1 < lam)
    (hE : 1 < energy lam) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    succProb lam ε P ≤
        ENNReal.ofReal (2 * Real.pi * ε / energy lam) *
          (ENNReal.ofReal (1 / Real.pi) +
            ENNReal.ofReal (8 * Real.pi * energy lam) * (expG lam P) ^ (1 / 2 : ℝ)) ∧
      ENNReal.ofReal (2 * Real.pi * ε / energy lam) *
          (ENNReal.ofReal (1 / Real.pi) +
            ENNReal.ofReal (8 * Real.pi * energy lam) * (expG lam P) ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (2 * ε / energy lam) +
          ENNReal.ofReal (16 * Real.pi ^ 2 * ε) * (expG lam P) ^ (1 / 2 : ℝ) := by
  let A := ENNReal.ofReal (8 * Real.pi * energy lam)
  have he : 0 < energy lam := by linarith
  have hpos : 0 < 8 * Real.pi * energy lam := by positivity
  have hA : 0 < A := ENNReal.ofReal_pos.mpr hpos
  have hAfin : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA2 : A^2 ≠ ⊤ := by finiteness
  have hA2z : A^2 ≠ 0 := pow_ne_zero _ hA.ne'
  have hj : Jbar lam P T ≤ A^2 * expG lam P := by
    rw [lemma_5_9 P lam hlam T le_rfl, expG, mul_left_comm, ← lintegral_const_mul' _ _ hA2]
    gcongr with θ
    apply hist_dom P lam θ _ hA2
    intro H
    rw [Gpot, ENNReal.ofReal_pow hpos.le, show ENNReal.ofReal (8 * Real.pi * energy lam) = A from rfl,
      mul_comm (A^2), ENNReal.div_mul_cancel hA2z hA2]
    exact le_add_self
  have hroot : (Jbar lam P T) ^ (1/2 : ℝ) ≤ A * (expG lam P) ^ (1/2 : ℝ) := by
    calc
      _ ≤ (A^2 * expG lam P) ^ (1/2 : ℝ) := ENNReal.rpow_le_rpow hj (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast_mul]
        norm_num
  have e1 : ENNReal.ofReal (2 * Real.pi * ε / energy lam) * ENNReal.ofReal (1 / Real.pi) =
      ENNReal.ofReal (2 * ε / energy lam) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have e2 : ENNReal.ofReal (2 * Real.pi * ε / energy lam) * A =
      ENNReal.ofReal (16 * Real.pi^2 * ε) := by
    dsimp [A]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    <;> ring
  have e3 : ENNReal.ofReal (2 * ε / energy lam) * ENNReal.ofReal Real.pi =
      ENNReal.ofReal (2 * Real.pi * ε / energy lam) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  change _ ≤ _ * (_ + A * _) ∧ _ * (_ + A * _) ≤ _
  rw [mul_add, e1, ← mul_assoc, e2]
  refine ⟨(lemma_5_4 P lam ε hlam hE hε hε2).trans ?_, le_rfl⟩
  rw [mul_add, mul_one, ← mul_assoc, e3, ← e2, mul_assoc (ENNReal.ofReal (2 * Real.pi * ε / energy lam)) A]
  exact add_le_add le_rfl (mul_le_mul le_rfl hroot (by positivity) (by positivity))
