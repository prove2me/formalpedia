-- Prove2me | solution 1 for GeneratesNS.word_norm_list_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:22:01.740826+00:00
-- url     : https://prove2.me/submissions/651c0bf1-a45d-4ff4-9317-4f625de32ce8

import Mathlib
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D007

section
-- module Solutions.OAIQ093_PR.Defs_WordMetric
attribute [-instance] _root_.GeneratesNS.LipschitzH.add _root_.GeneratesNS.LipschitzH.addMonoid _root_.GeneratesNS.LipschitzH.instAddCommGroup _root_.GeneratesNS.LipschitzH.instAddCommMonoid _root_.GeneratesNS.LipschitzH.zero _root_.GeneratesNS.LipschitzH_DecidableEq _root_.GeneratesNS.LipschitzH_normed _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.WordDist.instBorelSpace _root_.GeneratesNS.WordDist.instBorelSpaceAddOpp _root_.GeneratesNS.WordDist.instMeasurableSpace _root_.GeneratesNS.WordDist.instMeasureableSpaceOpp _root_.GeneratesNS.WordDist.measureSpace _root_.GeneratesNS.countable_G _root_.GeneratesNS.countable_add_G _root_.GeneratesNS.discreteTopology _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.instContinuousInvG _root_.GeneratesNS.instContinuousMulG _root_.GeneratesNS.instFunLikeLipschitzHGReal _root_.GeneratesNS.instIsTopologicalGroupG _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.lipschitzHVectorSpace _root_.GeneratesNS.lipschitzSMul _root_.GeneratesNS.myNegInvariant _root_.GeneratesNS.my_add_haar_right_invariant _root_.GeneratesNS.negLipschitzH _root_.GeneratesNS.nonempty_basis _root_.GeneratesNS.subLipschithZ _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.GeneratesNS.LipschitzH.add_apply _root_.GeneratesNS.LipschitzH.finset_sum_apply _root_.GeneratesNS.LipschitzH_apply _root_.GeneratesNS.ae_eq_everywhere _root_.GeneratesNS.lipschitz_add_tofun _root_.GeneratesNS.lipschitz_neg_tofun _root_.GeneratesNS.lipschitz_smul_tofun _root_.GeneratesNS.lipschitz_sub_tofun _root_.GeneratesNS.zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
@[expose]
instance.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS


lemma word_norm_list_prod_le_oai (l: List G): WordNorm (l.prod) ≤ (l.map WordNorm).sum := by
  induction l with
  | nil =>
    simp [word_norm_one]
  | cons head tail ih =>
    simp
    grw [word_norm_mul_le]
    grw [ih]


end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.word_norm_list_prod_le_oai.{u_1} := @GeneratesNS.word_norm_list_prod_le_oai.{u_1}
