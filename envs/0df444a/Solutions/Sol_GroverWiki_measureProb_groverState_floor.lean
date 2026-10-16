-- Prove2me | solution 1 for GroverWiki.measureProb_groverState_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:56:34.134985+00:00
-- url     : https://prove2.me/submissions/5cf4d844-5dfe-4019-9106-5519a591ae86

import Mathlib
import Definitions.Def_GroverWiki_Defs
import Theorems.Thm_GroverWiki_measureProb_groverState

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    1 - 1 / (N : ℝ) ≤
      measureProb (groverState f ⌊Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌋₊) ω := by
  have hNp : 0 < N := lt_of_le_of_lt (Nat.zero_le ω.val) ω.isLt
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNp
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNp)
  have hs_sq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hx1 : 1 / Real.sqrt (N : ℝ) ≤ 1 := (div_le_one hs).2 hs1
  let t : ℝ := Real.arcsin (1 / Real.sqrt N)
  have ht : 0 < t := Real.arcsin_pos.2 (by positivity)
  have htpi : t ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin t = 1 / Real.sqrt N :=
    Real.sin_arcsin (by linarith [one_div_pos.mpr hs]) hx1
  let q : ℝ := Real.pi / (4 * t)
  let k : ℕ := ⌊q⌋₊
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hklo : (k : ℝ) ≤ q := Nat.floor_le hq
  have hkhi : q < (k : ℝ) + 1 := Nat.lt_floor_add_one q
  have hqt : q * (4 * t) = Real.pi := by
    dsimp [q]
    exact div_mul_cancel₀ _ (by positivity)
  let δ : ℝ := (2 * (k : ℝ) + 1) * t - Real.pi / 2
  have hdlo : -t ≤ δ := by
    dsimp [δ]
    nlinarith [mul_lt_mul_of_pos_right hkhi (show 0 < 4 * t by positivity)]
  have hdhi : δ ≤ t := by
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_right hklo (show 0 ≤ 4 * t by positivity)]
  have hdabs : |δ| ≤ t := abs_le.2 ⟨hdlo, hdhi⟩
  have hcos : Real.cos t ≤ Real.cos δ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ)
      (show t ≤ Real.pi by linarith [Real.pi_pos]) hdabs
    simpa only [Real.cos_abs] using h
  have hcos0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], htpi⟩
  have hsin_sq : Real.sin t ^ 2 = 1 / (N : ℝ) := by
    rw [hsin]
    rw [div_pow, one_pow, hs_sq]
  have hbase : Real.cos t ^ 2 = 1 - 1 / (N : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hang : ((k : ℝ) + 1 / 2) * (2 * t) = δ + Real.pi / 2 := by
    dsimp [δ]
    ring
  have hbound : 1 - 1 / (N : ℝ) ≤ Real.sin (((k : ℝ) + 1 / 2) * (2 * t)) ^ 2 := by
    rw [hang, Real.sin_add_pi_div_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcos)
      (add_nonneg (le_trans hcos0 hcos) hcos0)]
  rw [GroverWiki.measureProb_groverState f ω hω]
  exact hbound
