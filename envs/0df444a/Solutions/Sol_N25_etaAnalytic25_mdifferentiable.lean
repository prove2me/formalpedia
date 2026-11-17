-- Prove2me | solution 1 for N25.etaAnalytic25_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:35.454208+00:00
-- url     : https://prove2.me/submissions/848845b3-b77a-478c-b875-48b22ccdeaaa

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun

set_option autoImplicit false

open scoped Manifold

namespace N25

theorem _root_.solution (g : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (etaAnalytic25 g) := by
  intro τ
  have hp : 0 < (25 * (τ : ℂ)).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 25) τ.im_pos
  have hd := ((ModularCurve.SiegelUnit.differentiableOn_siegelFun 25 g 0).1
    (25 * (τ : ℂ)) hp).differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hp)
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℂ => ModularCurve.siegelFun 25 g 0 z) (25 * (τ : ℂ)) :=
    hd.mdifferentiableAt
  exact (hm.comp τ ((mdifferentiable_const.mul UpperHalfPlane.mdifferentiable_coe) τ)).neg

end N25
