-- Prove2me | solution 1 for MTT.Cohomology.integral_class_unique
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T16:53:17.191616+00:00
-- url     : https://prove2.me/submissions/f0fe6cec-cef9-44ca-9783-a936a8844b82

import Definitions.Def_MTT_Cohomology
import Theorems.Thm_MTT_Cohomology_evaluation_faithful

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (φ ψ : Hc N (k - 2) ℂ)
    (hφ : IntegralClass f φ) (hψ : IntegralClass f ψ) :
    φ = ψ :=
  MTT.Cohomology.evaluation_faithful φ ψ fun j r hj => by rw [hφ j r hj, hψ j r hj]
