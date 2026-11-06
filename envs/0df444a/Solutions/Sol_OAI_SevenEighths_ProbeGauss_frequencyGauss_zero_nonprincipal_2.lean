-- Prove2me | solution 2 for OAI.SevenEighths.ProbeGauss.frequencyGauss_zero_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:56.779117+00:00
-- url     : https://prove2.me/submissions/c149e9b9-d8e9-40af-9a31-ff663696948b

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

theorem solution {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) :
    frequencyGauss ξ ψ 0 = 0 := by
  unfold frequencyGauss
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one hξ
