-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.monomial_descendant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:19.832951+00:00
-- url     : https://prove2.me/submissions/67bb258a-c2d1-4f3d-a56b-96001562eadc

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_descent_factor_le_one

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _
end OAI.SevenEighths.CubicDyadicDecay
