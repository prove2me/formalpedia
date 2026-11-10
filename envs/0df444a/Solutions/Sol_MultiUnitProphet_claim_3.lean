-- Prove2me | solution 1 for MultiUnitProphet.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:01:58.831974+00:00
-- url     : https://prove2.me/submissions/92043426-4630-42b1-b645-1e447f24e71c

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Aux_MUP_claim3

theorem jensen_inv (p q μ ν : ℝ) (hp : 0 < p) (hq : 0 < q) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (h : μ + ν = 1) : 1 / (μ * p + ν * q) ≤ μ / p + ν / q := by
  have hden : 0 < μ * p + ν * q := by
    rcases le_total p q with hpq | hpq
    · nlinarith [mul_le_mul_of_nonneg_left hpq hν]
    · nlinarith [mul_le_mul_of_nonneg_left hpq hμ]
  rw [div_add_div _ _ hp.ne' hq.ne', div_le_div_iff₀ hden (mul_pos hp hq)]
  have h2 : p * q = (μ + ν) ^ 2 * (p * q) := by rw [h]; ring
  nlinarith [mul_nonneg (mul_nonneg hμ hν) (sq_nonneg (p - q))]

theorem key (a b z : ℝ) (hz : z + a ≠ 0) : (b - a * z) / (z + a) = -a + (b + a ^ 2) / (z + a) := by
  field_simp <;> ring

end Aux_MUP_claim3

theorem solution (a b : ℝ) :
    (0 < a → 0 < b → 0 < 2 * a + 1 - b →
      (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x * y + a * (x + y) = b →
          y = (b - a * x) / (x + a)) ∧
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => (b - a * x) / (x + a)) ∧
      StrictAntiOn (fun x => (b - a * x) / (x + a)) (Set.Icc (0 : ℝ) 1)) ∧
    (a < 0 → b < 0 → 2 * a + 1 - b < 0 →
      (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x * y + a * (x + y) = b →
          x < -a ∧ y = (b - a * x) / (x + a)) ∧
      ConcaveOn ℝ (Set.Iio (-a)) (fun x => (b - a * x) / (x + a)) ∧
      StrictAntiOn (fun x => (b - a * x) / (x + a)) (Set.Iio (-a))) := by
  refine ⟨fun ha hb hab => ?_, fun ha hb hab => ?_⟩
  · have hK : 0 < b + a ^ 2 := by positivity
    refine ⟨fun x y hx _ hxy => ?_, ⟨convex_Icc 0 1, fun x hx y hy μ ν hμ hν hμν => ?_⟩,
      fun x hx y hy hlt => ?_⟩
    · have hne : x + a ≠ 0 := by linarith [hx.1]
      rw [eq_div_iff hne]
      linear_combination hxy
    · simp only [smul_eq_mul]
      have hp : 0 < x + a := by linarith [hx.1]
      have hq : 0 < y + a := by linarith [hy.1]
      have hj := Aux_MUP_claim3.jensen_inv (x + a) (y + a) μ ν hp hq hμ hν hμν
      have e : μ * x + ν * y + a = μ * (x + a) + ν * (y + a) := by linear_combination (-a) * hμν
      have hpos : 0 < μ * (x + a) + ν * (y + a) := by
        rcases le_total (x + a) (y + a) with h1 | h1
        · nlinarith [mul_le_mul_of_nonneg_left h1 hν]
        · nlinarith [mul_le_mul_of_nonneg_left h1 hμ]
      rw [Aux_MUP_claim3.key a b (μ * x + ν * y) (by rw [e]; exact hpos.ne'), Aux_MUP_claim3.key a b x hp.ne',
        Aux_MUP_claim3.key a b y hq.ne', e]
      have h3 := mul_le_mul_of_nonneg_left hj hK.le
      have e2 : (b + a ^ 2) / (μ * (x + a) + ν * (y + a))
          = (b + a ^ 2) * (1 / (μ * (x + a) + ν * (y + a))) := by ring
      have e3 : μ * (-a + (b + a ^ 2) / (x + a)) + ν * (-a + (b + a ^ 2) / (y + a))
          = -a * (μ + ν) + (b + a ^ 2) * (μ / (x + a) + ν / (y + a)) := by ring
      rw [e2, e3, hμν]
      linarith
    · show (b - a * y) / (y + a) < (b - a * x) / (x + a)
      have hp : 0 < x + a := by linarith [hx.1]
      have hq : 0 < y + a := by linarith [hy.1]
      rw [Aux_MUP_claim3.key a b x hp.ne', Aux_MUP_claim3.key a b y hq.ne']
      have := div_lt_div_of_pos_left hK hp (by linarith : x + a < y + a)
      linarith
  · have hK : 0 < b + a ^ 2 := by nlinarith [sq_nonneg (a + 1)]
    refine ⟨fun x y hx hy hxy => ?_, ⟨convex_Iio (-a), fun x hx y hy μ ν hμ hν hμν => ?_⟩,
      fun x hx y hy hlt => ?_⟩
    · have hprod : (x + a) * (y + a) = b + a ^ 2 := by linear_combination hxy
      have hgt : (a + 1) ^ 2 < (x + a) * (y + a) := by rw [hprod]; nlinarith
      have hxlt : x < -a := by
        by_contra hc
        push_neg at hc
        have hxa : 0 < x + a := by
          rcases (show 0 ≤ x + a by linarith).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, zero_mul] at hgt
            nlinarith [sq_nonneg (a + 1)]
        have hya : 0 < y + a := by
          by_contra h
          push_neg at h
          have := mul_nonpos_iff.mpr (Or.inl ⟨hxa.le, h⟩)
          nlinarith [sq_nonneg (a + 1)]
        have hle : (x + a) * (y + a) ≤ (1 + a) * (1 + a) :=
          mul_le_mul (by linarith [hx.2]) (by linarith [hy.2]) hya.le (by linarith [hx.2])
        nlinarith
      refine ⟨hxlt, ?_⟩
      have hne : x + a ≠ 0 := by linarith
      rw [eq_div_iff hne]
      linear_combination hxy
    · simp only [smul_eq_mul]
      have hx' : x < -a := hx
      have hy' : y < -a := hy
      have hp : 0 < -(x + a) := by linarith
      have hq : 0 < -(y + a) := by linarith
      have hj := Aux_MUP_claim3.jensen_inv (-(x + a)) (-(y + a)) μ ν hp hq hμ hν hμν
      have e : μ * x + ν * y + a = μ * (x + a) + ν * (y + a) := by linear_combination (-a) * hμν
      have hneg : μ * (x + a) + ν * (y + a) < 0 := by
        rcases le_total (-(x + a)) (-(y + a)) with h1 | h1
        · nlinarith [mul_le_mul_of_nonneg_left h1 hν]
        · nlinarith [mul_le_mul_of_nonneg_left h1 hμ]
      rw [Aux_MUP_claim3.key a b (μ * x + ν * y) (by rw [e]; exact hneg.ne), Aux_MUP_claim3.key a b x (ne_of_lt (by linarith)),
        Aux_MUP_claim3.key a b y (ne_of_lt (by linarith)), e]
      have h3 := mul_le_mul_of_nonpos_left hj (by linarith : -(b + a ^ 2) ≤ 0)
      have e4 : (b + a ^ 2) / (μ * (x + a) + ν * (y + a))
          = -(b + a ^ 2) * (1 / (μ * -(x + a) + ν * -(y + a))) := by
        rw [show μ * -(x + a) + ν * -(y + a) = -(μ * (x + a) + ν * (y + a)) by ring, div_neg]
        ring
      have e5 : μ * (-a + (b + a ^ 2) / (x + a)) + ν * (-a + (b + a ^ 2) / (y + a))
          = -a * (μ + ν) + -(b + a ^ 2) * (μ / -(x + a) + ν / -(y + a)) := by
        rw [div_neg, div_neg]
        ring
      rw [e4, e5, hμν]
      linarith
    · show (b - a * y) / (y + a) < (b - a * x) / (x + a)
      have hx' : x < -a := hx
      have hy' : y < -a := hy
      rw [Aux_MUP_claim3.key a b x (ne_of_lt (by linarith)), Aux_MUP_claim3.key a b y (ne_of_lt (by linarith))]
      have h1 := div_lt_div_of_pos_left hK (by linarith : 0 < -(y + a)) (by linarith : -(y + a) < -(x + a))
      rw [div_neg, div_neg] at h1
      linarith
