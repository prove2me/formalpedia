-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.mixed_monomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:38.451531+00:00
-- url     : https://prove2.me/submissions/84588194-87a8-43df-b1d3-259ad1653282

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
end OAI.SevenEighths.CubicDyadicDecay
