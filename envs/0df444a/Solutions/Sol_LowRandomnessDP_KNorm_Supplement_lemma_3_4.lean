-- Prove2me | solution 1 for LowRandomnessDP.KNorm.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:29:38.653662+00:00
-- url     : https://prove2.me/submissions/34271baf-67b0-44d3-bd0f-99021aa83709

import Mathlib
import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical
open LowRandomnessDP.KNorm LowRandomnessDP.KNorm.Supplement

theorem LRDP34_step (w t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Int.fract (w + t) - Int.fract w = t - (if 1 - t ≤ Int.fract w then 1 else 0) := by
  have hf0 := Int.fract_nonneg w
  have hf1 := Int.fract_lt_one w
  have e : w + t = (Int.fract w + t) + ((⌊w⌋ : ℤ) : ℝ) := by
    linarith [Int.floor_add_fract w]
  rw [e, Int.fract_add_intCast]
  split_ifs with h
  · have : Int.fract (Int.fract w + t) = Int.fract w + t - 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [this]; ring
  · push Not at h
    have : Int.fract (Int.fract w + t) = Int.fract w + t :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [this]; ring

theorem solution (d : ℕ) (hd : 0 < d) (x : Vec d) (a b m : Fin d)
    (hcong : Int.ModEq (d : ℤ) (b.val : ℤ) ((a.val : ℤ) - (m.val : ℤ))) :
    phi x b - phi x a = (m.val : ℝ) -
      ((Finset.univ.filter (fun i : Fin d =>
        1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) := by
  obtain ⟨k, hk⟩ := hcong.dvd
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hkR : ((a.val : ℝ) - m.val) - b.val = d * k := by exact_mod_cast hk
  have ht0 : (0:ℝ) ≤ (m.val : ℝ) / d := by positivity
  have ht1 : (m.val : ℝ) / d < 1 := by
    rw [div_lt_one hdR]; exact_mod_cast m.2
  have hshift : ∀ i, x i - (b.val : ℝ) / d = (x i - (a.val : ℝ) / d + (m.val : ℝ) / d) + (k : ℝ) := by
    intro i
    have : (b.val : ℝ) = a.val - m.val - d * k := by linarith
    rw [this]; field_simp; ring
  unfold phi
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Int.fract (x i - (b.val : ℝ) / d) - Int.fract (x i - (a.val : ℝ) / d)
        = (m.val : ℝ) / d - (if 1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d) then 1 else 0) := by
    intro i _
    rw [hshift i, Int.fract_add_intCast]
    exact LRDP34_step _ _ ht0 ht1
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_boole]
  field_simp
