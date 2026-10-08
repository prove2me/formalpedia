-- Prove2me | solution 1 for MazurTransfer.order49_point_map_two_nsmul_ne_zero_of_order_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:01:00.637836+00:00
-- url     : https://prove2.me/submissions/8ee032ce-4b1a-41ed-8507-19a388d158dd

import Mathlib
open Polynomial
namespace MazurTransfer.Order49PointNonvanishingHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert











































private theorem two_nsmul_ne_zero_of_order_fortyNine
    {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 49) :
    (2 : ℕ) • P ≠ 0 := by
  intro hzero
  have hdvd : (49 : ℕ) ∣ 2 := by
    rw [← hP]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzero
  norm_num at hdvd























end MazurTorsion.Kubert

end MazurTransfer.Order49PointNonvanishingHelpers

theorem solution {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 49) :
    (2 : ℕ) • P ≠ 0 := by
  apply MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.two_nsmul_ne_zero_of_order_fortyNine <;> assumption
#print axioms solution
