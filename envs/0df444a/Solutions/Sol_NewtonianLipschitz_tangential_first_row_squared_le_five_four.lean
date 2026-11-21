-- Prove2me | solution 1 for NewtonianLipschitz.tangential_first_row_squared_le_five_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:59:48.826032+00:00
-- url     : https://prove2.me/submissions/9c4a98a1-5ccb-4979-a744-512f526ea591

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Theorems.Thm_NewtonianLipschitz_tangential_denominator_fifth_power_ge_twelve

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v t : ℝ) (ht : t = u ^ 2 + v ^ 2) :
    (3 * (u + v)) ^ 2 ≤
      ((5 / 4 : ℝ) ^ 2) * (1 + t) ^ 5 := by
  have ht0 : 0 ≤ t := by
    rw [ht]
    positivity
  have hcs : (u + v) ^ 2 ≤ 2 * t := by
    rw [ht]
    nlinarith [sq_nonneg (u - v)]
  have hfirst : (3 * (u + v)) ^ 2 ≤ 18 * t := by
    nlinarith [hcs]
  have hradial := tangential_denominator_fifth_power_ge_twelve t ht0
  have hsecond :
      18 * t ≤ ((5 / 4 : ℝ) ^ 2) * (1 + t) ^ 5 := by
    nlinarith [hradial, ht0]
  exact hfirst.trans hsecond
end NewtonianLipschitz
