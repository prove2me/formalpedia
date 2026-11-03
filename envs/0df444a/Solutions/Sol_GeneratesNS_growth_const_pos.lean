-- Prove2me | solution 1 for GeneratesNS.growth_const_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:47:00.761556+00:00
-- url     : https://prove2.me/submissions/58e660f4-8c90-405c-aaae-e212c5153b25

import Mathlib
import Definitions.Def_OAIQ093D016

section
-- module Solutions.OAIQ093_PR.GrowthZero
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
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
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

/-- The constant in a polynomial growth bound is positive: `a = 0` would force `S ^ 1 = ∅`,
contradicting `1 ∈ S`. -/
lemma growth_const_pos_oai {d a : ℕ} (ha: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d): 0 < a := by
  by_contra!
  simp at this
  rw [this] at ha
  have hg_one := ha 1 (by omega)
  simp at hg_one
  have one_mem := hGS.one_mem
  rw [hg_one] at one_mem
  simp at one_mem

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.growth_const_pos_oai.{u_1} := @GeneratesNS.growth_const_pos_oai.{u_1}
