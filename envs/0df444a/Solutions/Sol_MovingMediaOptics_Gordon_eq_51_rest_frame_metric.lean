-- Prove2me | solution 1 for MovingMediaOptics.Gordon.eq_51_rest_frame_metric
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:37:45.788625+00:00
-- url     : https://prove2.me/submissions/319bc5e1-373d-435e-9640-4eb70c349500

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

lemma quadX (c n : ℝ) (u : V3) (p : V4) :
    quadratic (gDown c n u) p =
      (p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) + (1 / n ^ 2 - 1) *
        (lorentzFactor c u * p 0 - lorentzFactor c u * u 0 / c * p 1
          - lorentzFactor c u * u 1 / c * p 2 - lorentzFactor c u * u 2 / c * p 3) ^ 2 := by
  simp only [quadratic, gDown, apply4, minkowskiMetric, fourFlow, Fin.sum_univ_four]
  simp
  ring

lemma boostX (c : ℝ) (u : V3) (v : V4) (h0 : u ≠ 0) :
    apply4 (lorentzBoost c u) v = ![
      lorentzFactor c u * v 0 + lorentzFactor c u * u 0 / c * v 1 + lorentzFactor c u * u 1 / c * v 2 + lorentzFactor c u * u 2 / c * v 3,
      lorentzFactor c u * u 0 / c * v 0 + (1 + (lorentzFactor c u - 1) * u 0 * u 0 / dot3 u u) * v 1 + (lorentzFactor c u - 1) * u 0 * u 1 / dot3 u u * v 2 + (lorentzFactor c u - 1) * u 0 * u 2 / dot3 u u * v 3,
      lorentzFactor c u * u 1 / c * v 0 + (lorentzFactor c u - 1) * u 1 * u 0 / dot3 u u * v 1 + (1 + (lorentzFactor c u - 1) * u 1 * u 1 / dot3 u u) * v 2 + (lorentzFactor c u - 1) * u 1 * u 2 / dot3 u u * v 3,
      lorentzFactor c u * u 2 / c * v 0 + (lorentzFactor c u - 1) * u 2 * u 0 / dot3 u u * v 1 + (lorentzFactor c u - 1) * u 2 * u 1 / dot3 u u * v 2 + (1 + (lorentzFactor c u - 1) * u 2 * u 2 / dot3 u u) * v 3] := by
  funext i
  fin_cases i <;> simp [apply4, lorentzBoost, h0, Fin.sum_univ_four]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem solution (c n : ℝ) (u : V3) (v : V4)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    quadratic (gDown c n u) (apply4 (lorentzBoost c u) v) =
      (v 0) ^ 2 / n ^ 2 - ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hn0 : n ≠ 0 := by linarith
  by_cases h0 : u = 0
  · subst h0
    have hg : lorentzFactor c 0 = 1 := by simp [lorentzFactor, dot3]
    have hb : lorentzBoost c 0 = 1 := by simp [lorentzBoost]
    rw [quadX, hb]
    simp [apply4, Matrix.one_apply, Fin.sum_univ_four, hg]
    field_simp
    ring
  · have hDpos : 0 < dot3 u u := by
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
        by_contra h; push Not at h; exact h0 (funext h)
      unfold dot3
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
    have hR : lorentzFactor c u ^ 2 * (c ^ 2 - dot3 u u) = c ^ 2 := by
      have h1 : 0 < 1 - dot3 u u / c ^ 2 := by
        rw [sub_pos, div_lt_one (by positivity)]; exact hu
      have hs := Real.sq_sqrt h1.le
      have e : c ^ 2 - dot3 u u = (1 - dot3 u u / c ^ 2) * c ^ 2 := by field_simp
      unfold lorentzFactor
      rw [div_pow, one_pow, hs, e, ← mul_assoc, one_div_mul_cancel h1.ne', one_mul]
    have hD0 : dot3 u u ≠ 0 := hDpos.ne'
    rw [boostX c u v h0, quadX]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    simp only [dot3, Fin.sum_univ_three] at hR hD0 ⊢
    generalize lorentzFactor c u = g at hR ⊢
    generalize hDd : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = D at hD0 hR ⊢
    linear_combination (norm := skip) ((-c^2*n^2*(u 0)^4*(v 1)^2 - 2*c^2*n^2*(u 0)^3*(u 1)*(v 1)*(v 2) - 2*c^2*n^2*(u 0)^3*(u 2)*(v 1)*(v 3) - c^2*n^2*(u 0)^2*(u 1)^2*(v 1)^2 - c^2*n^2*(u 0)^2*(u 1)^2*(v 2)^2 - 2*c^2*n^2*(u 0)^2*(u 1)*(u 2)*(v 2)*(v 3) - c^2*n^2*(u 0)^2*(u 2)^2*(v 1)^2 - c^2*n^2*(u 0)^2*(u 2)^2*(v 3)^2 - 2*c^2*n^2*(u 0)*(u 1)^3*(v 1)*(v 2) - 2*c^2*n^2*(u 0)*(u 1)^2*(u 2)*(v 1)*(v 3) - 2*c^2*n^2*(u 0)*(u 1)*(u 2)^2*(v 1)*(v 2) - 2*c^2*n^2*(u 0)*(u 2)^3*(v 1)*(v 3) - c^2*n^2*(u 1)^4*(v 2)^2 - 2*c^2*n^2*(u 1)^3*(u 2)*(v 2)*(v 3) - c^2*n^2*(u 1)^2*(u 2)^2*(v 2)^2 - c^2*n^2*(u 1)^2*(u 2)^2*(v 3)^2 - 2*c^2*n^2*(u 1)*(u 2)^3*(v 2)*(v 3) - c^2*n^2*(u 2)^4*(v 3)^2 + c^2*(u 0)^4*(v 0)^2 + 2*c^2*(u 0)^2*(u 1)^2*(v 0)^2 + 2*c^2*(u 0)^2*(u 2)^2*(v 0)^2 + c^2*(u 1)^4*(v 0)^2 + 2*c^2*(u 1)^2*(u 2)^2*(v 0)^2 + c^2*(u 2)^4*(v 0)^2 + g^2*(-c^2*n^2*(u 0)^4*(v 0)^2 - 2*c^2*n^2*(u 0)^2*(u 1)^2*(v 0)^2 - 2*c^2*n^2*(u 0)^2*(u 2)^2*(v 0)^2 - c^2*n^2*(u 1)^4*(v 0)^2 - 2*c^2*n^2*(u 1)^2*(u 2)^2*(v 0)^2 - c^2*n^2*(u 2)^4*(v 0)^2 + c^2*(u 0)^4*(v 0)^2 + 2*c^2*(u 0)^2*(u 1)^2*(v 0)^2 + 2*c^2*(u 0)^2*(u 2)^2*(v 0)^2 + c^2*(u 1)^4*(v 0)^2 + 2*c^2*(u 1)^2*(u 2)^2*(v 0)^2 + c^2*(u 2)^4*(v 0)^2 + n^2*(u 0)^6*(v 0)^2 + 3*n^2*(u 0)^4*(u 1)^2*(v 0)^2 + 3*n^2*(u 0)^4*(u 2)^2*(v 0)^2 + 3*n^2*(u 0)^2*(u 1)^4*(v 0)^2 + 6*n^2*(u 0)^2*(u 1)^2*(u 2)^2*(v 0)^2 + 3*n^2*(u 0)^2*(u 2)^4*(v 0)^2 + n^2*(u 1)^6*(v 0)^2 + 3*n^2*(u 1)^4*(u 2)^2*(v 0)^2 + 3*n^2*(u 1)^2*(u 2)^4*(v 0)^2 + n^2*(u 2)^6*(v 0)^2 - (u 0)^6*(v 0)^2 - 3*(u 0)^4*(u 1)^2*(v 0)^2 - 3*(u 0)^4*(u 2)^2*(v 0)^2 - 3*(u 0)^2*(u 1)^4*(v 0)^2 - 6*(u 0)^2*(u 1)^2*(u 2)^2*(v 0)^2 - 3*(u 0)^2*(u 2)^4*(v 0)^2 - (u 1)^6*(v 0)^2 - 3*(u 1)^4*(u 2)^2*(v 0)^2 - 3*(u 1)^2*(u 2)^4*(v 0)^2 - (u 2)^6*(v 0)^2)) / (c^4*n^2*D^2)) * hR
    field_simp
    subst hDd
    ring
