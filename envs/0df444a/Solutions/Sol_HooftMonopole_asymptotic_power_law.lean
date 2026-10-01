-- Prove2me | solution 1 for HooftMonopole.asymptotic_power_law
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T22:37:51.053451+00:00
-- url     : https://prove2.me/submissions/da77e3cc-8ebd-4993-be4d-5a2a7fca539d

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real
open HooftMonopole

private lemma potencia_atinge (m q : ℝ) (hm : m ≠ 0) (hq : 0 < q) :
    ∃ r : ℝ, 0 < r ∧ r ^ m = q := by
  exact ⟨q ^ m⁻¹, Real.rpow_pos_of_pos hq _, Real.rpow_inv_rpow hq.le hm⟩

private lemma unicidade_algebrica (b c m : ℝ) (hb : b ≠ 0) (hc : 0 < c)
    (h : ∀ r : ℝ, 0 < r →
      m * (m - 1) * (b * r ^ m) =
        (b * r ^ m + 1) * ((b * r ^ m) * (b * r ^ m + 2) + c * r ^ 2)) :
    m = 0 ∧ b = -1 := by
  have hm : m = 0 := by
    by_contra hm
    rcases lt_or_gt_of_ne hb with hb | hb
    · obtain ⟨r, hr, hpot⟩ := potencia_atinge m ((-1) / b) hm (div_pos_of_neg_of_neg (by norm_num) hb)
      have hvalor : b * r ^ m = -1 := by rw [hpot]; field_simp
      have hcoef := h r hr
      rw [hvalor] at hcoef
      have hzero : m * (m - 1) = 0 := by nlinarith [hcoef]
      obtain ⟨s, hs, hpot⟩ := potencia_atinge m ((-2) / b) hm (div_pos_of_neg_of_neg (by norm_num) hb)
      have hvalor : b * s ^ m = -2 := by rw [hpot]; field_simp
      have hcontra := h s hs
      rw [hvalor, hzero] at hcontra
      nlinarith [sq_pos_of_pos hs]
    · let q := max (m * (m - 1)) 0 + 1
      have hq : 0 < q := by dsimp [q]; positivity
      have hmaior : m * (m - 1) < q := by dsimp [q]; linarith [le_max_left (m * (m - 1)) 0]
      obtain ⟨r, hr, hpot⟩ := potencia_atinge m (q / b) hm (div_pos hq hb)
      have hvalor : b * r ^ m = q := by rw [hpot]; field_simp
      have hcontra := h r hr
      rw [hvalor] at hcontra
      have hlimite := mul_lt_mul_of_pos_right hmaior hq
      have hcubo : 0 ≤ q ^ 3 := by positivity
      have hresto : 0 ≤ (q + 1) * (c * r ^ 2) := by positivity
      nlinarith [hcontra]
  refine ⟨hm, ?_⟩
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  simp only [hm, Real.rpow_zero, mul_one, zero_mul] at h1 h2
  have hproduto : c * (b + 1) = 0 := by nlinarith [h1, h2]
  rcases mul_eq_zero.mp hproduto with hzero | hzero
  · exact False.elim ((ne_of_gt hc) hzero)
  · linarith

private lemma equacao_normalizada (e F a n r : ℝ) (he : e ≠ 0) (hr : 0 < r) :
    radialWEquation e (fun s => a * s ^ (-n)) (fun s => F / s) r ↔
      (2 - n) * (1 - n) * (e * a * r ^ (2 - n)) =
        (e * a * r ^ (2 - n) + 1) *
          ((e * a * r ^ (2 - n)) * (e * a * r ^ (2 - n) + 2) + e ^ 2 * F ^ 2 * r ^ 2) := by
  have hderiv : deriv (fun s : ℝ => a * s ^ (-n)) =
      fun s => a * (-n * s ^ (-n - 1)) := by
    ext s
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
  have hW := (Real.hasDerivAt_rpow_const (x := r) (p := -n) (Or.inl (ne_of_gt hr))).const_mul a
  have hW' := ((Real.hasDerivAt_rpow_const (x := r) (p := -n - 1)
    (Or.inl (ne_of_gt hr))).const_mul (-n)).const_mul a
  have hfluxo := ((((hasDerivAt_id r).pow 4).const_mul 2).mul hW').add
    ((((hasDerivAt_id r).pow 3).const_mul 4).mul hW)
  change HasDerivAt (fun s : ℝ => 2 * s ^ 4 * (a * (-n * s ^ (-n - 1))) +
    4 * s ^ 3 * (a * s ^ (-n))) _ r at hfluxo
  unfold radialWEquation
  rw [hderiv, hfluxo.deriv]
  have hpot : r ^ (2 - n) = r ^ 2 * r ^ (-n) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_two]
  rw [hpot]
  simp only [Real.rpow_sub_one (ne_of_gt hr)]
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  constructor <;> intro h
  · linear_combination (norm := (field_simp; ring)) (e / 2) * h
  · linear_combination (norm := (field_simp [he]; ring)) (2 / e) * h

theorem solution (e F : ℝ) (he : 0 < e) (hF : 0 < F) (a n : ℝ) (ha : a ≠ 0) :
    (∀ r : ℝ, 0 < r → radialWEquation e (fun s => a * s ^ (-n)) (fun s => F / s) r) ↔
      (n = 2 ∧ a = -1 / e) := by
  constructor
  · intro h
    have hnorm : ∀ r : ℝ, 0 < r →
        (2 - n) * ((2 - n) - 1) * (e * a * r ^ (2 - n)) =
          (e * a * r ^ (2 - n) + 1) *
            ((e * a * r ^ (2 - n)) * (e * a * r ^ (2 - n) + 2) +
              (e ^ 2 * F ^ 2) * r ^ 2) := by
      intro r hr
      convert (equacao_normalizada e F a n r (ne_of_gt he) hr).mp (h r hr) using 1
      ring
    obtain ⟨hm, hb⟩ := unicidade_algebrica (e * a) (e ^ 2 * F ^ 2) (2 - n)
      (mul_ne_zero (ne_of_gt he) ha) (by positivity) hnorm
    refine ⟨by linarith, ?_⟩
    apply (eq_div_iff (ne_of_gt he)).2
    nlinarith [hb]
  · rintro ⟨rfl, rfl⟩ r hr
    apply (equacao_normalizada e F (-1 / e) 2 r (ne_of_gt he) hr).mpr
    norm_num
    field_simp
    norm_num
