-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.secondary_monomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:39.201036+00:00
-- url     : https://prove2.me/submissions/1f127f7e-9656-40d8-bd7f-835201a3cd2f

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
theorem _root_.solution (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
end OAI.SevenEighths.CubicDyadicDecay
