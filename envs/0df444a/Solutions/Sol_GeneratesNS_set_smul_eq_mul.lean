-- Prove2me | solution 1 for GeneratesNS.set_smul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:16:27.285266+00:00
-- url     : https://prove2.me/submissions/227ec978-10bf-4665-b961-4dad25291525

import Mathlib

section
-- module Solutions.OAIQ093_PR.GrowthZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the kernel, and growth exponent zero

`three_two_kernel_poly_growth`, and that a group of growth exponent zero is finite.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative


lemma set_smul_eq_mul_oai {G: Type*} [Group G] (g: G) (A: Set G): g • A = {g} * A := by
  ext a
  rw [Set.mem_smul_set]
  rw [Set.mem_mul]
  simp

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.set_smul_eq_mul_oai.{u_1} := @GeneratesNS.set_smul_eq_mul_oai.{u_1}
