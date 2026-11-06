-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.frequencyGauss_zero_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:21.083003+00:00
-- url     : https://prove2.me/submissions/5ff1b81f-2d25-4d61-9853-47b87b74b6d0

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
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) :
    frequencyGauss ξ ψ 0 = 0 := by
  simpa [frequencyGauss] using MulChar.sum_eq_zero_of_ne_one hξ
end OAI.SevenEighths.ProbeGauss
