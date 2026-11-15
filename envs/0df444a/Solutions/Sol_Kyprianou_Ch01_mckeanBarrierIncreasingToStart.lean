-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanBarrierIncreasingToStart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:03:20.376477+00:00
-- url     : https://prove2.me/submissions/ef39ddb3-aa78-4dca-a7c4-52fbc2a9ee0d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
private theorem mckeanIncreasingAux
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi)))
    (ha : a ≤ x) (hx : x ≤ b) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      K - Real.exp x := by
  have hd : 0 < 1 + phi := by linarith
  have hp : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hd
  have he : Real.exp b = K * phi / (1 + phi) := by
    rw [hb, Real.exp_log hp]
  have hrel : Real.exp b * (1 + phi) = K * phi := by
    rw [he]
    field_simp <;> ring
  have hlt : Real.exp b < K := by
    rw [he]
    apply (div_lt_iff₀ hd).2
    nlinarith
  have hxexp : Real.exp x ≤ Real.exp b := Real.exp_le_exp.mpr hx
  have hgap : 0 ≤ K - Real.exp x := by linarith
  have hcoef : Real.exp x ≤ phi * (K - Real.exp x) := by
    have hh := mul_le_mul_of_nonneg_right hxexp (le_of_lt hd)
    nlinarith [hrel, hh]
  let u : ℝ := x - a
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : 1 + phi * u ≤ Real.exp (phi * u) := by
    nlinarith [Real.add_one_le_exp (phi * u)]
  have hu2 : 1 - u ≤ Real.exp (-u) := by
    nlinarith [Real.add_one_le_exp (-u)]
  have h1 := mul_le_mul_of_nonneg_left hu1 hgap
  have h2 := mul_le_mul_of_nonneg_left hu2
    (le_of_lt (Real.exp_pos x))
  have h3 := mul_le_mul_of_nonneg_right hcoef hu
  have hbase : K - Real.exp x * Real.exp (-u) ≤
      (K - Real.exp x) * Real.exp (phi * u) := by
    nlinarith [h1, h2, h3]
  have h4 := mul_le_mul_of_nonneg_right hbase
    (le_of_lt (Real.exp_pos (-phi * u)))
  have hcancel : Real.exp (phi * u) * Real.exp (-phi * u) = 1 := by
    rw [← Real.exp_add]
    simp
  have h5 :
      (K - Real.exp x) *
          (Real.exp (phi * u) * Real.exp (-phi * u)) =
        K - Real.exp x := by rw [hcancel]; ring
  have h6 :
      (K - Real.exp x * Real.exp (-u)) * Real.exp (-phi * u) ≤
        K - Real.exp x := by
    nlinarith [h4, h5]
  have hea : Real.exp a = Real.exp x * Real.exp (-u) := by
    dsimp [u]
    rw [← Real.exp_add]
    congr 1
    ring
  simpa [u, hea] using h6


theorem solution
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi)))
    (ha : a ≤ x) (hx : x ≤ b) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      K - Real.exp x := by
  exact mckeanIncreasingAux K phi x b a hK hphi hb ha hx
