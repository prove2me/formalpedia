-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.frequencyGauss_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:20.196426+00:00
-- url     : https://prove2.me/submissions/fd4c265f-6386-401c-bdda-892e5c17bd4a

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss
import Theorems.Thm_OAI_SevenEighths_ProbeGauss_frequencyGauss_nonzero
import Theorems.Thm_OAI_SevenEighths_ProbeGauss_frequencyGauss_zero_nonprincipal

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
namespace OAI.SevenEighths.ProbeGauss
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) (h : F) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  by_cases hh : h = 0
  · subst h
    rw [frequencyGauss_zero_nonprincipal ξ ψ hξ, MulChar.map_zero, zero_mul]
  · exact frequencyGauss_nonzero ξ ψ hh
end OAI.SevenEighths.ProbeGauss
