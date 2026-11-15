-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanBarrierGlobalMax
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:03:13.653279+00:00
-- url     : https://prove2.me/submissions/f0375a25-369d-459f-ae5a-12d79e505e34

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
private theorem mckeanGlobalAux
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi))) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      (K - Real.exp b) * Real.exp (-phi * (x - b)) := by
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
  have hgap : 0 ≤ K - Real.exp b := by linarith
  have hcoef : Real.exp b = phi * (K - Real.exp b) := by
    nlinarith [hrel]
  let u : ℝ := a - b
  have hu1 : (1 - phi * u) * Real.exp (phi * u) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (-phi * u))
      (le_of_lt (Real.exp_pos (phi * u)))
    have hcancel : Real.exp (-phi * u) * Real.exp (phi * u) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [h]
  have hu2 : 1 + u ≤ Real.exp u := by
    nlinarith [Real.add_one_le_exp u]
  have hmul := mul_le_mul_of_nonneg_left hu2
    (le_of_lt (mul_pos hphi (Real.exp_pos (phi * u))))
  have ham : (1 + phi) * Real.exp (phi * u) ≤
      1 + phi * Real.exp u * Real.exp (phi * u) := by
    nlinarith [hu1, hmul]
  have hscaled := mul_le_mul_of_nonneg_left ham hgap
  have heCoef :
      Real.exp b * Real.exp u * Real.exp (phi * u) =
        phi * (K - Real.exp b) * Real.exp u *
          Real.exp (phi * u) := by
    simpa only [mul_assoc] using
      congrArg (fun v : ℝ => v * Real.exp u * Real.exp (phi * u)) hcoef
  have hbase : (K - Real.exp b * Real.exp u) * Real.exp (phi * u) ≤
      K - Real.exp b := by
    nlinarith [hscaled, heCoef]
  have heA : Real.exp a = Real.exp b * Real.exp u := by
    dsimp [u]
    rw [← Real.exp_add]
    congr 1
    ring
  have heFactor :
      Real.exp (-phi * (x - a)) =
        Real.exp (-phi * (x - b)) * Real.exp (phi * u) := by
    dsimp [u]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heA, heFactor]
  calc
    (K - Real.exp b * Real.exp u) *
        (Real.exp (-phi * (x - b)) * Real.exp (phi * u)) =
      ((K - Real.exp b * Real.exp u) * Real.exp (phi * u)) *
        Real.exp (-phi * (x - b)) := by ring
    _ ≤ (K - Real.exp b) * Real.exp (-phi * (x - b)) := by
      exact mul_le_mul_of_nonneg_right hbase
        (le_of_lt (Real.exp_pos _))



theorem solution
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi))) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      (K - Real.exp b) * Real.exp (-phi * (x - b)) := by
  exact mckeanGlobalAux K phi x b a hK hphi hb
