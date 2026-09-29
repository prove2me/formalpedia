-- Prove2me | solution 2 for Kawahira.index_eq_one_div_one_sub_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:04:27.262188+00:00
-- url     : https://prove2.me/submissions/e5edc49d-2002-4d2a-a6e8-33184a2f9e8c

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_holomorphicIndex_eventuallyEq_of_factor

open Complex Topology Filter
open Kawahira

theorem solution (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (hfix : g a = a) (hlam : deriv g a ≠ 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = 1 / (1 - deriv g a) := by
  let h : ℂ → ℂ := fun z => z - g z
  have hh : AnalyticAt ℂ h a := analyticAt_id.sub hg
  have hha : h a = 0 := by simp [h, hfix]
  have hhderiv : deriv h a = 1 - deriv g a := by
    exact ((hasDerivAt_id a).sub hg.differentiableAt.hasDerivAt).deriv
  have hhderiv_ne : deriv h a ≠ 0 := by
    rw [hhderiv]
    exact sub_ne_zero.mpr hlam.symm
  have horder : analyticOrderAt h a = (1 : ℕ∞) :=
    hh.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hha hhderiv_ne
  obtain ⟨q, hq, hqa, hfactor⟩ := hh.analyticOrderAt_eq_natCast.mp horder
  have hfactor' : (fun z => z - g z) =ᶠ[𝓝 a] fun z => (z - a) * q z := by
    filter_upwards [hfactor] with z hz
    simpa [h, smul_eq_mul] using hz
  have hqa_eq : q a = 1 - deriv g a := by
    have hlocal : h =ᶠ[𝓝 a] fun z => (z - a) * q z := by
      filter_upwards [hfactor] with z hz
      simpa [smul_eq_mul] using hz
    have hderiv := hlocal.deriv_eq
    rw [hhderiv] at hderiv
    have hprod := ((hasDerivAt_id a).sub_const a).mul hq.differentiableAt.hasDerivAt
    have hprod_deriv : deriv (fun z => (z - a) * q z) a = q a := by
      change deriv ((fun x : ℂ => x - a) * q) a = q a
      simpa only [id_eq, one_mul, sub_self, zero_mul, add_zero] using hprod.deriv
    rw [hprod_deriv] at hderiv
    exact hderiv.symm
  filter_upwards [Kawahira.holomorphicIndex_eventuallyEq_of_factor g q a hq hqa hfactor']
      with r hr
  rw [hr, hqa_eq]
  simp [div_eq_mul_inv]
