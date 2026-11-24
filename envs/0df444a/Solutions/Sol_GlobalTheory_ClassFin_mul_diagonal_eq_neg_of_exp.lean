-- Prove2me | solution 1 for GlobalTheory.ClassFin.mul_diagonal_eq_neg_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:04.430775+00:00
-- url     : https://prove2.me/submissions/fb33605a-24b9-447d-aadf-4d9a79ba1599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) (d d' : ι → ℝ)
    (h : diagonal (fun i => (Real.exp (d' i) : ℂ)) * y * diagonal (fun i => (Real.exp (d i) : ℂ)) = y) :
    y * diagonal (fun i => (d i : ℂ)) = -(diagonal (fun i => (d' i : ℂ)) * y) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at hij
  rw [neg_apply, mul_diagonal, diagonal_mul]
  by_cases hy : y i j = 0
  · simp [hy]
  · have h1 : ((Real.exp (d' i) : ℝ) : ℂ) * (Real.exp (d j) : ℝ) = 1 := by
      apply mul_left_cancel₀ hy
      linear_combination hij
    have h2 : Real.exp (d' i + d j) = 1 := by
      rw [Real.exp_add]
      exact_mod_cast h1
    have h3 : d' i + d j = 0 := by simpa using h2
    have h4 : (d' i : ℂ) + (d j : ℂ) = 0 := by exact_mod_cast h3
    linear_combination (y i j) * h4
end GlobalTheory.ClassFin
