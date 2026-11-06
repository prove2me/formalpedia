-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.frequencyGauss_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:53:33.233221+00:00
-- url     : https://prove2.me/submissions/1fa05cbf-2f2c-445c-8394-fb77d35eed1a

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
namespace OAI.SevenEighths.ProbeGauss
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  exact gaussSum_mulShift_eq ξ ψ (Units.mk0 h hh)
end OAI.SevenEighths.ProbeGauss
