-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.poisson_small_power_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:14.319699+00:00
-- url     : https://prove2.me/submissions/74126386-e395-49d0-874f-5c105d91f046

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_poisson_scale_identity

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring
end OAI.SevenEighths.CubicDyadicDecay
