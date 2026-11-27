-- Prove2me | solution 1 for MasulloRH.quarter_shift_zeta_zero_height_profile
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:16:37.165799+00:00
-- url     : https://prove2.me/submissions/8c3e89e9-db2e-437d-89f4-7adca3992aee

import Theorems.Thm_MasulloRH_twenty_five_rational_translates_gaussian_all_windows
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter Topology MasulloRH MasulloRH.ThetaDerivativeCertificate
open MasulloRH.GaussianApproximation

theorem solution (s : ℂ) (hl : 1/2 < s.re) (hr : s.re < 1) (hz : riemannZeta s = 0) :
    Real.exp ((s.re^2-s.im^2)/2) * (4*(s.re-1/2)*(1-s.re)) ≤ 1/32000000000 := by
  let F (b : ℝ) := Real.exp ((s.re^2-s.im^2)/2) * ((b^2-(s.re-3/4)^2)/b)
  have hd : |s.re-3/4| < 1/4 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have ev : ∀ᶠ b in 𝓝[<] (1/4:ℝ), F b ≤ 1/32000000000 := by
    filter_upwards [Ioo_mem_nhdsLT hd] with b hb
    obtain ⟨hd',hb'⟩ := hb
    have zero := MasulloRH.fixed_gaussian_energy_lower_at_every_zeta_zero (3/4) b
      (by linarith) (by linarith) (fun i : Fin 25 => (coeff i:ℂ)) (fun i => (shift i:ℝ)) s hd' hz
    have h := MasulloRH.twenty_five_rational_translates_gaussian_all_windows.1
      (3/4) b (by linarith) (by linarith)
    exact zero.trans h.le
  have hc : ContinuousAt F (1/4:ℝ) := by unfold F;fun_prop (disch := norm_num)
  have bound : F (1/4) ≤ 1/32000000000 :=
    le_of_tendsto (hc.continuousWithinAt (s:=Iio (1/4:ℝ))).tendsto ev
  have eq : ((1/4:ℝ)^2-(s.re-3/4)^2)/(1/4) = 4*(s.re-1/2)*(1-s.re) := by ring
  simpa only [F,eq] using bound
