-- Prove2me | solution 1 for N25.siegelIndex25_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:26.295373+00:00
-- url     : https://prove2.me/submissions/aa99d30b-2946-4c12-a105-c38b076e644a

import Mathlib

set_option autoImplicit false

namespace N25

theorem _root_.solution (B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (g : ℤ) (hg : ¬(25 : ℤ) ∣ g) :
    (25 : ℤ) ∣ g * B 0 0 → ¬(25 : ℤ) ∣ g * B 0 1 := by
  intro hr hs
  apply hg
  have hh := dvd_sub (dvd_mul_of_dvd_left hr (B 1 1)) (dvd_mul_of_dvd_left hs (B 1 0))
  have hd := B.prop
  rw [Matrix.det_fin_two] at hd
  have he : (g * B 0 0) * B 1 1 - (g * B 0 1) * B 1 0 = g := by
    linear_combination g * hd
  rwa [he] at hh

end N25
