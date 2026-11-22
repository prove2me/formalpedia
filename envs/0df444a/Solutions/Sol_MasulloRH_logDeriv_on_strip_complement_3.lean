-- Prove2me | solution 3 for MasulloRH.logDeriv_on_strip_complement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-22T14:39:49.185927+00:00
-- url     : https://prove2.me/submissions/57aeaae7-bed7-4350-b7bf-8bd8eb6a34cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_logDeriv_analytic_verified_region
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Theorems.Thm_MasulloRH_cofinal_signed_critical_band_certificates

set_option autoImplicit false

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (_hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) : AnalyticAt ℂ zetaLogDeriv s := by
  obtain ⟨hstrip, hpole⟩ := hs
  have hr : 1 / 2 < s.re := by linarith
  by_cases hregion : |s.im| ≤ 100000 ∨ 1 ≤ s.re
  · exact logDeriv_analytic_verified_region s hr hpole hregion
  obtain ⟨hhigh, hlt⟩ := not_or.mp hregion
  have ha := analyticOn_riemannZeta s hpole
  apply ha.deriv.div ha
  intro hz
  let z : ZetaZerosInTraceStrip (1 / 2) :=
    ⟨s, hz, by linarith, lt_of_not_ge hlt, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  obtain ⟨T, hT⟩ := exists_nat_gt |s.im|
  obtain ⟨H, hH, E, B, hE, hB, hdisj, hsep, hcount⟩ :=
    cofinal_signed_critical_band_certificates T
  have hTH : (T : ℝ) ≤ H := by exact_mod_cast hH
  exact hr.ne' (critical_zero_band_of_signed_brackets 100000 H E B hE hB hdisj hsep hcount z
    (lt_of_not_ge hhigh) (hT.le.trans hTH))
