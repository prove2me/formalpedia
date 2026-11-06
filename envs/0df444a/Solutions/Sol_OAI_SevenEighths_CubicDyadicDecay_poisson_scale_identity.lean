-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.poisson_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:33.402773+00:00
-- url     : https://prove2.me/submissions/0d92fbf7-3a83-417c-9fc9-22149a5458d3

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
theorem _root_.solution (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  ring
end OAI.SevenEighths.CubicDyadicDecay
