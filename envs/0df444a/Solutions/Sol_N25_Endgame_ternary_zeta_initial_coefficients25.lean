-- Prove2me | solution 1 for N25.Endgame.ternary_zeta_initial_coefficients25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:25.806633+00:00
-- url     : https://prove2.me/submissions/25741a44-ba56-4591-9609-f0ed504fa0c7

import Definitions.Def_N25_GenusFourNumerator

set_option autoImplicit false

namespace N25.Endgame

/-- The first coefficients of a full zeta identity, including its constant term. -/
theorem _root_.solution
    (L : Polynomial ℤ) (A : ℕ → ℤ)
    (hzero : L.coeff 0 = 1)
    (h : (1 - PowerSeries.X) * (1 - PowerSeries.C (3 : ℤ) * PowerSeries.X) *
      PowerSeries.mk A = (L : PowerSeries ℤ)) :
    A 0 = 1 ∧ L.coeff 1 = A 1 - 4 * A 0 ∧
      L.coeff 2 = A 2 - 4 * A 1 + 3 * A 0 ∧
      L.coeff 3 = A 3 - 4 * A 2 + 3 * A 1 ∧
      L.coeff 4 = A 4 - 4 * A 3 + 3 * A 2 := by
  have hexp : (1 - PowerSeries.X) * (1 - PowerSeries.C (3 : ℤ) * PowerSeries.X) *
      PowerSeries.mk A = PowerSeries.mk A -
        (PowerSeries.C 4 * PowerSeries.mk A) * PowerSeries.X ^ 1 +
        (PowerSeries.C 3 * PowerSeries.mk A) * PowerSeries.X ^ 2 := by
    norm_num
    ring
  rw [hexp] at h
  have hc (n : ℕ) := congrArg (PowerSeries.coeff n) h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4
  exact ⟨h0.trans hzero, h1.symm, h2.symm, h3.symm, h4.symm⟩

end N25.Endgame
