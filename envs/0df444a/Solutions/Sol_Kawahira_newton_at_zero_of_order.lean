-- Prove2me | solution 1 for Kawahira.newton_at_zero_of_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:48:36.644965+00:00
-- url     : https://prove2.me/submissions/c2fd15fe-97cf-40b1-a89d-25d4875dbeba

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_logQuotient_hasDerivAt_of_factor

open Complex Topology
open Kawahira

theorem solution (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    newton g a = a ∧ deriv (newton g) a = 1 - 1 / (m : ℂ) := by
  obtain ⟨q, hq, hqa, hgq⟩ := hg.analyticOrderAt_eq_natCast.mp horder
  have hgq' : g =ᶠ[𝓝 a] fun z => (z - a) ^ m * q z := by
    filter_upwards [hgq] with z hz
    simpa [smul_eq_mul] using hz
  obtain ⟨hzero, hderiv⟩ :=
    Kawahira.logQuotient_hasDerivAt_of_factor g q a m hm hq hqa hgq'
  constructor
  · simp [newton, hzero]
  · change deriv (fun z => z - g z / deriv g z) a = 1 - 1 / (m : ℂ)
    exact ((hasDerivAt_id a).sub hderiv).deriv
