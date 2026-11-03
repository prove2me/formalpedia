-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:32:03.388995+00:00
-- url     : https://prove2.me/submissions/4653871d-985b-4d98-829b-97d91291e704

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D012
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_good_affine_templates_support_le_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubexponentialBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite algebra of subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem subexponential_lower_const {c : ℝ} (hc : 0 < c) :
    HasSubexponentialLowerBound (fun _ => c) := by
  intro ε hε
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have he := ht.eventually (gt_mem_nhds hc)
  simpa only [Function.comp_def, id_eq, neg_mul] using he.mono (fun _ h => h.le)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem HasSubexponentialLowerBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialLowerBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePackingAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial losses and logarithmic errors in path packing -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

/-- Every fixed affine function of the logarithmic path error is sublinear. -/
theorem eventually_logarithmic_error_le (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, a * (1 + Real.log (2 + r)) + b ≤ ε * r := by
  have hadd : Tendsto (fun r : ℝ => 2 + r) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop (x - 2)] with r hr
    linarith
  have hlog : Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hadd
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hconst : Tendsto (fun r : ℝ => (a + b) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun r : ℝ => (a * (1 + Real.log (2 + r)) + b) / r)
      atTop (𝓝 0) := by
    have h := (hlog.const_mul a).add hconst
    convert h using 1
    · funext r; ring
    · simp
  filter_upwards [(tendsto_order.mp hlim).2 ε hε, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  exact ((div_lt_iff₀ hr0).mp hr).le

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceVolumeComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential volume comparison along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

theorem subexponential_upper_polynomial {D : ℝ} (hD : 0 < D) (k : ℕ) :
    HasSubexponentialUpperBound (fun r => D * (1 + r) ^ k) := by
  intro ε hε
  filter_upwards [eventually_logarithmic_error_le (k : ℝ) (Real.log D) hε,
    eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h1 : 0 < 1 + r := by positivity
  apply (Real.log_le_iff_le_exp (mul_pos hD (pow_pos h1 k))).mp
  rw [Real.log_mul hD.ne' (pow_ne_zero _ h1.ne'), Real.log_pow]
  have hlog : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log h1 (by linarith)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlog hk]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponentialOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebra of losses along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {scale : ℕ → ℝ}

theorem HasSubexponentialUpperBoundSeq.pow {f : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hs : Tendsto scale atTop atTop)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n) (k : ℕ) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using sequence_subexponential_upper_const hs 1
  | succ k ih =>
    simpa only [pow_succ] using ih.mul hf (hf0.mono (fun _ h => pow_nonneg h k))

theorem HasSubexponentialUpperBoundSeq.add {f g : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hs : Tendsto scale atTop atTop) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n + g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε),
    sequence_subexponential_upper_const hs 2 (ε / 2) (half_pos hε)] with n hn hm htwo
  have he : Real.exp (ε * scale n) =
      Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (ε / 2 * scale n)]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequenceVanishingRate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing exponential rates are subexponential -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem sequence_subexponential_exp_of_vanishing_rate
    {scale η : ℕ → ℝ} (hscale0 : ∀ n, 0 ≤ scale n)
    (hη : Tendsto η atTop (𝓝 0)) :
    HasSubexponentialUpperBoundSeq scale (fun n => Real.exp (η n * scale n)) := by
  intro ε hε
  filter_upwards [hη.eventually (eventually_lt_nhds hε)] with n hn
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn.le (hscale0 n))

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

/-- A polynomial correction to exponential contraction can be absorbed
uniformly at a time bounded by twice the logarithm of the initial size. -/
theorem exists_logarithmic_contraction_time {C : ℝ} (hC : 0 ≤ C) (b : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ R : ℝ, 0 ≤ R →
      let t := 2 * Real.log (2 + R) + a
      1 ≤ t ∧ C * (1 + t) ^ b * Real.exp (-t) * R ≤ 1 := by
  have hp : Tendsto (fun t : ℝ => t ^ b * Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b : ℝ) (1 / 2) (by norm_num)
  have hs : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [eventually_ge_atTop (z - 1)] with t ht
    linarith
  have heq (t : ℝ) : C * (1 + t) ^ b * Real.exp (-t / 2) =
      (C * Real.exp (1 / 2)) * ((1 + t) ^ b * Real.exp (-(1 / 2) * (1 + t))) := by
    have hh : Real.exp (-t / 2) = Real.exp (1 / 2) * Real.exp (-(1 / 2) * (1 + t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hh]
    ring
  have ht : Tendsto (fun t : ℝ => C * (1 + t) ^ b * Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [heq, Function.comp_def, mul_zero] using
      (hp.comp hs).const_mul (C * Real.exp (1 / 2))
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  let a := max a₀ 1
  refine ⟨a, (by dsimp [a] <;> positivity), fun R hR => ?_⟩
  let t := 2 * Real.log (2 + R) + a
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have ha1 : 1 ≤ a := le_max_right _ _
  have ha : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by dsimp [t] <;> positivity
  have ht1 : 1 ≤ t := by dsimp [t] <;> linarith
  have hta : a₀ ≤ t := (le_max_left _ _).trans (by dsimp [t] <;> linarith)
  have hcoef : C * (1 + t) ^ b * Real.exp (-t / 2) ≤ 1 := (ha₀ t hta).le
  have hsmall : Real.exp (-t / 2) * R ≤ 1 := by
    calc
      Real.exp (-t / 2) * R ≤ Real.exp (-Real.log (2 + R)) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply Real.exp_le_exp.mpr
        dsimp [t]
        linarith
      _ = R / (2 + R) := by rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  refine ⟨ht1, ?_⟩
  have hnonneg : 0 ≤ C * (1 + t) ^ b * Real.exp (-t / 2) := by positivity
  calc
    C * (1 + t) ^ b * Real.exp (-t) * R =
        (C * (1 + t) ^ b * Real.exp (-t / 2)) * (Real.exp (-t / 2) * R) := by
      have hh : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hh]
      ring
    _ ≤ (C * (1 + t) ^ b * Real.exp (-t / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hsmall hnonneg
    _ ≤ 1 := by simpa using hcoef

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

/-- Conjugation costs at most twice the conjugating length. -/
theorem dist_one_conjugate_le (a x : G) :
    dist 1 (a * x * a⁻¹) ≤ 2 * dist 1 a + dist 1 x := by
  have hi : dist 1 a⁻¹ = dist 1 a := by
    simpa only [mul_one, mul_inv_cancel, dist_comm] using (dist_mul_left a 1 a⁻¹).symm
  calc
    dist 1 (a * x * a⁻¹) ≤ dist 1 (a * x) + dist 1 a⁻¹ := dist_one_mul_le _ _
    _ ≤ (dist 1 a + dist 1 x) + dist 1 a⁻¹ := add_le_add (dist_one_mul_le _ _) le_rfl
    _ = _ := by rw [hi]; ring

/-- Exponential contraction up to a polynomial, together with a bounded
unit neighborhood and linear conjugating paths, implies logarithmic distortion. -/
theorem logarithmic_distortion_of_contracting_flow
    {V : Type} [NormedAddCommGroup V]
    (Exp : V → G) (d : ℝ → G) (T : ℝ → V → V)
    {C L B : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖)
    (hpath : ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t)
    (hlocal : ∀ v, ‖v‖ ≤ 1 → dist 1 (Exp v) ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨a, ha, htime⟩ := exists_logarithmic_contraction_time hC b
  let c := (2 * L * a + B) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ c := by dsimp [c] <;> positivity
  refine ⟨4 * L + c + 1, by positivity, fun v => ?_⟩
  let t := 2 * Real.log (2 + ‖v‖) + a
  obtain ⟨ht1, hsize⟩ := htime ‖v‖ (norm_nonneg v)
  have ht : 0 ≤ t := le_trans zero_le_one ht1
  have hunit : ‖T t v‖ ≤ 1 := (hcontract v t ht).trans hsize
  have hlog : Real.log 2 ≤ Real.log (2 + ‖v‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg v])
  have hconst : 2 * L * a + B ≤ c * Real.log (2 + ‖v‖) := by
    calc
      2 * L * a + B = c * Real.log 2 := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc
  calc
    dist 1 (Exp v) = dist 1 (d t * Exp (T t v) * (d t)⁻¹) := by rw [← hconj v t ht]
    _ ≤ 2 * dist 1 (d t) + dist 1 (Exp (T t v)) := dist_one_conjugate_le _ _
    _ ≤ 2 * (L * t) + B := add_le_add (by gcongr; exact hpath t ht1) (hlocal _ hunit)
    _ = 4 * L * Real.log (2 + ‖v‖) + (2 * L * a + B) := by dsimp [t] <;> ring
    _ ≤ (4 * L + c + 1) * Real.log (2 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast <;> ring

/-- Every continuous one-parameter homomorphism has a linear metric bound
for times at least one, using only boundedness of its compact unit interval. -/
theorem continuous_flow_linear_growth
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num))
    simpa [hd0] using h
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, fun t ht => ?_⟩
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htn : t ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one t).le
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (by linarith : 0 ≤ t)) 1
  have hs : t / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hnr.le, (div_le_one hnr).mpr htn⟩
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have heq : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  calc
    dist 1 (d t) = dist 1 (d (t / n) ^ n) := congrArg (dist 1) heq
    _ ≤ (n : ℝ) * dist 1 (d (t / n)) := dist_one_pow_le _ _
    _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_left hlocal hnr.le
    _ ≤ (2 * C) * t := by nlinarith

/-- For a continuous exponential chart and continuous contracting flow,
polynomially corrected contraction implies an actual logarithmic distance bound.
The compact unit-ball bound and the flow-length bound are derived in the proof. -/
theorem logarithmic_distortion_of_continuous_flow
    {V : Type} [NormedAddCommGroup V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) (T : ℝ → V → V)
    {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨L, hL, hpath⟩ := continuous_flow_linear_growth d hd hd0 hmul
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) 1).bddAbove_image
    (continuous_const.dist hExp).continuousOn
  have hB0 : 0 ≤ B := (dist_nonneg (x := (1 : G)) (y := Exp 0)).trans
    (hB (mem_image_of_mem _ (by simp : (0 : V) ∈ closedBall 0 1)))
  apply logarithmic_distortion_of_contracting_flow Exp d T hC hL hB0 b hconj hcontract hpath
  intro v hv
  apply hB
  exact mem_image_of_mem _ (by simpa only [mem_closedBall, dist_zero_right] using hv)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

/-- The polynomial exponential gives a uniform increment bound on any fixed
bounded set of nilpotent logarithms. -/
theorem norm_exp_sub_one_le_of_pow_eq_zero [NormOneClass A]
    (x : A) {c : ℕ} (hx : x ^ (c + 1) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ‖x‖ ≤ M) :
    ‖NormedSpace.exp x - 1‖ ≤ (c : ℝ) * (1 + M) ^ c := by
  rw [exp_eq_finite_sum_of_pow_eq_zero x hx, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖((k + 1).factorial : ℝ)⁻¹ • x ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + M) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hi : ‖((k + 1).factorial : ℝ)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ = ‖((k + 1).factorial : ℝ)⁻¹‖ * ‖x ^ (k + 1)‖ := norm_smul _ _
        _ ≤ 1 * ‖x ^ (k + 1)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ ≤ (1 + M) ^ (k + 1) := by
          rw [one_mul]
          exact (norm_pow_le _ _).trans
            (pow_le_pow_left₀ (norm_nonneg _) (by linarith) (k + 1))
        _ ≤ (1 + M) ^ c := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hk)
    _ = _ := by simp

end Algebra

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent corrections in a contracting weight flow

The nilpotent part of the infinitesimal action gives a polynomial bound
for its actual analytic exponential. Coupled with scalar exponential
contraction, it gives logarithmic metric distortion of the weight chart.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Split the scalar weight from the nilpotent part in the actual analytic
exponential of the infinitesimal generator. -/
theorem exp_smul_sub_one
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (N : A) (t : ℝ) :
    NormedSpace.exp (t • (N - 1)) = Real.exp (-t) • NormedSpace.exp (t • N) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute ((-t) • (1 : A)) (t • N) := by
    change ((-t) • (1 : A)) * (t • N) = (t • N) * ((-t) • (1 : A))
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes (-t) (t • N)
  have he : NormedSpace.exp ((-t) • (1 : A)) = Real.exp (-t) • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) (-t)).symm
  rw [show t • (N - 1) = (-t) • (1 : A) + t • N by module,
    NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

/-- The actual exponential of a nilpotent operator has polynomial growth
in its real parameter, with an explicit uniform coefficient. -/
theorem norm_exp_smul_nilpotent_le
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (N : A) {c : ℕ} (hN : N ^ (c + 1) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • N)‖ ≤
      ((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c := by
  have hpow : (t • N) ^ (c + 1) = 0 := by simp [smul_pow, hN]
  have hbound : ‖NormedSpace.exp (t • N) - 1‖ ≤
      (c : ℝ) * (1 + t * ‖N‖) ^ c := by
    apply norm_exp_sub_one_le_of_pow_eq_zero _ hpow (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hbase : 1 + t * ‖N‖ ≤ (1 + ‖N‖) * (1 + t) := by
    nlinarith [norm_nonneg N]
  have hpoly : (1 + t * ‖N‖) ^ c ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase c
  have hone : 1 ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg N]))
      (one_le_pow₀ (by linarith))
  calc
    ‖NormedSpace.exp (t • N)‖ ≤ ‖NormedSpace.exp (t • N) - 1‖ + ‖(1 : A)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (c : ℝ) * (1 + t * ‖N‖) ^ c + 1 := by simpa only [norm_one] using add_le_add hbound le_rfl
    _ ≤ (c : ℝ) * ((1 + ‖N‖) ^ c * (1 + t) ^ c) +
        ((1 + ‖N‖) ^ c * (1 + t) ^ c) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hone
    _ = _ := by ring

/-- The infinitesimal nilpotent correction, with its actual operator
exponential, has exactly the polynomially corrected contraction needed above. -/
theorem norm_contracted_nilpotent_flow_le
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (v : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-t) • (NormedSpace.exp (t • N)) v‖ ≤
      (((c : ℝ) + 1) * (1 + ‖N‖) ^ c) * (1 + t) ^ c * Real.exp (-t) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * ‖(NormedSpace.exp (t • N)) v‖ ≤
        Real.exp (-t) * (‖NormedSpace.exp (t • N)‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) *
        ((((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c) * ‖v‖) := by
      gcongr
      exact norm_exp_smul_nilpotent_le N hN ht
    _ = _ := by ring

/-- A continuous weight chart with a nilpotent correction in its contracting
action is logarithmically distorted. This is the individual weight-space
estimate, before taking bounded products of generator directions. -/
theorem logarithmic_distortion_of_nilpotent_flow
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp (Real.exp (-t) • (NormedSpace.exp (t • N)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  exact logarithmic_distortion_of_continuous_flow Exp hExp d hd hd0 hmul
    (fun t v => Real.exp (-t) • (NormedSpace.exp (t • N)) v)
    (C := ((c : ℝ) + 1) * (1 + ‖N‖) ^ c) (by positivity) c hconj
    (fun v _ ht => norm_contracted_nilpotent_flow_le N hN v ht)

/-- The same distortion conclusion stated directly for a generator whose
nilpotent part is `N` and whose real weight is `-1`. -/
theorem logarithmic_distortion_of_weight_generator
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • (N - 1))) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  apply logarithmic_distortion_of_nilpotent_flow Exp hExp d hd hd0 hmul N hN
  intro v t ht
  have hh := hconj v t ht
  rw [exp_smul_sub_one N t] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion in Cartan root spaces

Generalized root spaces determine the nilpotent correction to the scalar
weight action. A compatible group conjugation identity then gives logarithmic
distortion.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

attribute [local instance] OAI.PolycyclicRecognition.rootNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.rootNormedSpace
attribute [local instance] OAI.PolycyclicRecognition.rootNontrivial
theorem rootAction_nilpotent_correction (h : H) :
    _root_.IsNilpotent (rootAction H χ h - χ h • 1) := by
  have hn := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, ?_⟩
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hk
  simpa only [map_pow, map_sub, Algebra.algebraMap_eq_smul_one,
    map_smul, map_one, map_zero, rootAction] using hm

/-- Each nonzero real root has a direction where its value is `-1`. -/
theorem exists_contracting_root_direction (hχ : χ.IsNonZero) :
    ∃ h : H, χ h = -1 := by
  have hn : ∃ h : H, χ h ≠ 0 := by
    by_contra! hn
    apply hχ
    exact funext hn
  obtain ⟨h, hh⟩ := hn
  refine ⟨(-(χ h)⁻¹) • h, ?_⟩
  rw [map_smul]
  change -(χ h)⁻¹ * χ h = -1
  rw [neg_mul, inv_mul_cancel₀ hh]

/-- Logarithmic distortion follows for an integrated nonzero root chart.
No semisimplicity or diagonal adjoint action is assumed. -/
theorem root_logarithmic_distortion
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • rootAction H χ h)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  let N := rootAction H χ h + 1
  have hnil : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨k, hk⟩ := hnil
  have hk' : N ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  apply logarithmic_distortion_of_weight_generator Exp hExp d hd hd0 hmul N hk'
  simpa only [N, add_sub_cancel_right] using hconj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

set_option maxHeartbeats 1000000 in
/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions
set_option maxHeartbeats 1000000 in
/-- The nilpotence exponent is uniformly bounded by the root-space dimension. -/
theorem rootAction_residual_pow_eq_zero (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ (rootSpace H χ) = 0 := by
  let A : Module.End ℝ (rootSpace H χ) := toEnd ℝ H (rootSpace H χ) h - χ h • 1
  have hn : _root_.IsNilpotent A := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  have hp : A ^ finrank ℝ (rootSpace H χ) = 0 := by
    simpa only [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] using
      A.aeval_self_charpoly
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hp
  simpa only [A, map_pow, map_sub, map_smul, map_one, map_zero, rootAction] using hm

set_option maxHeartbeats 1000000 in
/-- One polynomial controls the residual operator for every Cartan parameter. -/
theorem exists_rootResidual_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : H,
      ‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) := by
  let d := finrank ℝ (rootSpace H χ)
  let b := Module.finBasis ℝ H
  let f := ((rootResidualLinear H χ).comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  let K := ‖f‖
  have hK : 0 ≤ K := norm_nonneg f
  refine ⟨((d : ℝ) + 1) * (1 + K) ^ d * 2 ^ d, by positivity, ?_⟩
  intro h
  have hb : ‖rootAction H χ h - χ h • 1‖ ≤ K * ‖(Module.finBasis ℝ H).equivFun h‖ := by
    have hf : f (b.equivFun h) = rootAction H χ h - χ h • 1 := by
      change rootResidualLinear H χ (b.equivFun.symm (b.equivFun h)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    simpa only [hf] using f.le_opNorm (b.equivFun h)
  have hp : (rootAction H χ h - χ h • 1) ^ (d + 1) = 0 := by
    rw [pow_succ, rootAction_residual_pow_eq_zero, zero_mul]
  have he := norm_exp_smul_nilpotent_le (rootAction H χ h - χ h • 1) hp (t := 1) zero_le_one
  simp only [one_smul, one_add_one_eq_two] at he
  calc
    _ ≤ ((d : ℝ) + 1) * (1 + ‖rootAction H χ h - χ h • 1‖) ^ d * 2 ^ d := he
    _ ≤ ((d : ℝ) + 1) * ((1 + K) * (1 + ‖(Module.finBasis ℝ H).equivFun h‖)) ^ d * 2 ^ d := by
      gcongr
      nlinarith [norm_nonneg (b.equivFun h)]
    _ = _ := by rw [mul_pow]; ring

set_option maxHeartbeats 1000000 in
/-- Restoring the scalar character gives the full root action estimate. -/
theorem exists_rootAction_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : H) (v : rootSpace H χ),
      ‖(NormedSpace.exp (rootAction H χ h)) v‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * Real.exp (χ h) * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_rootResidual_exp_bound H χ
  refine ⟨C, hC, fun h v => ?_⟩
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (χ h) *
        (‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ * ‖v‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (χ h) *
        (C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * ‖v‖) := by
      gcongr
      exact hbound h
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm obtained from weighted nilpotent boxes

For a bracket-word basis, each generator occurs with a positive integral
multiplicity. Unimodularity says that the corresponding weighted sum of
characters is zero. The support exponent of a segment is the maximum, over
these bases, of the weighted positive parts of the characters. This finite
data yields the support norm identities.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I B : Type} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

namespace SupportDatum

variable (D : SupportDatum W I B)

theorem segmentSupport_pos {w : W} (hw : w ≠ 0) : 0 < D.segmentSupport w := by
  exact lt_of_le_of_ne (D.segmentSupport_nonneg w)
    (Ne.symm fun h => hw ((D.segmentSupport_eq_zero_iff w).mp h))

end SupportDatum
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem basisTemplateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (b : B) :
    D.basisTemplateSupport ((fun x => x + w) '' E) b = D.basisTemplateSupport E b := by
  simp only [basisTemplateSupport, D.weightSupport_translate hE hne, mul_add,
    Finset.sum_add_distrib, D.balanced, add_zero]

theorem templateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) : D.templateSupport ((fun x => x + w) '' E) = D.templateSupport E := by
  simp only [templateSupport, D.basisTemplateSupport_translate hE hne]

omit [FiniteDimensional ℝ W] in
theorem basisTemplateSupport_le (E : Set W) (b : B) :
    D.basisTemplateSupport E b ≤ D.templateSupport E :=
  Finset.le_sup' (f := D.basisTemplateSupport E) (Finset.mem_univ b)

omit [FiniteDimensional ℝ W] in
theorem templateSupport_le {E : Set W} {r : ℝ}
    (h : ∀ b, D.basisTemplateSupport E b ≤ r) : D.templateSupport E ≤ r :=
  Finset.sup'_le _ _ fun b _ => h b

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra exponentials as actual group elements

The unit-valued exponential keeps the inverse explicit. This bridges the
operator conjugation identity to a faithful group representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem algebraExpUnit_add_of_commute {x y : A} (hxy : Commute x y) :
    algebraExpUnit (x + y) = algebraExpUnit x * algebraExpUnit y := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hxy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

theorem represented_root_exp_conjugation (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) =
      algebraExpUnit (t • j h) * algebraExpUnit (j v) * (algebraExpUnit (t • j h))⁻¹ := by
  change algebraExpUnit (representedRootVector H χ j
    ((NormedSpace.exp (t • rootAction H χ h)) v)) = _
  rw [represented_root_flow]
  exact algebraExpUnit_conj (algebraExpUnit (t • j h)) (j v)

theorem represented_root_exp_inverse_conjugation
    (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j v) = algebraExpUnit (-(t • j h)) *
      algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) *
        (algebraExpUnit (-(t • j h)))⁻¹ := by
  rw [represented_root_exp_conjugation, algebraExpUnit_neg]
  simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- In an integrated faithful representation, logarithmic root distortion
requires only the exponential matching data. -/
theorem represented_root_logarithmic_distortion
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1) (d : ℝ → G) (hd : Continuous d)
    (hExpρ : ∀ v, ρ (Exp v) = algebraExpUnit (j v))
    (hdρ : ∀ t, ρ (d t) = algebraExpUnit (-(t • j h))) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  have hd0 : d 0 = 1 := by
    apply hρ
    simp only [hdρ, zero_smul, neg_zero, algebraExpUnit_zero, map_one]
  have hmul : ∀ s t, d (s + t) = d s * d t := by
    intro s t
    apply hρ
    rw [map_mul, hdρ, hdρ, hdρ]
    have hc : Commute (-(s • j h)) (-(t • j h)) := by
      exact (((Commute.refl (j h)).smul_left s).smul_right t).neg_left.neg_right
    rw [← algebraExpUnit_add_of_commute hc]
    congr 1
    module
  apply root_logarithmic_distortion H χ Exp hExp h hh d hd hd0 hmul
  intro v t _
  apply hρ
  simp only [map_mul, map_inv, hExpρ, hdρ]
  exact represented_root_exp_inverse_conjugation H χ j h t v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PublishedRootDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual root distortion from the published linear realization

All contraction, continuity, and conjugation premises of the root-space
distortion theorem are now discharged for the ambient Lie group. Only the
already recorded faithful exponential-realization input remains assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every actual nonzero Cartan root space is logarithmically distorted
in the ambient metric. -/
theorem root_distortion_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : rootSpace H χ,
      dist 1 (Exp v) ≤ D * Real.log (2 + ‖(rootCoordinates H χ) v‖) := by
  let : TopologicalSpace (rootSpace H χ) :=
    (rootNormedAddCommGroup H χ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let d : ℝ → G := fun t => Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  have hEr : Continuous (fun v : rootSpace H χ => Exp v) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (ρ (Exp v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  have hd : Continuous d := by
    apply hind.continuous_iff.mpr
    change Continuous (fun t : ℝ => (ρ (Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) :
      Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch, map_neg, map_smul]
    exact Units.continuous_val.comp (algebraExpUnit_continuous.comp
      (continuous_id.smul continuous_const).neg)
  exact represented_root_logarithmic_distortion H χ j ρ hρ
    (fun v => Exp v) hEr h hh d hd (fun v => hmatch v)
    (fun t => by simp only [d, hmatch, map_neg, map_smul])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootSwitchBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient bounds for root switches at a Cartan position

Conjugating a root displacement back from its Cartan position removes its
scalar weight, up to the proved polynomial nilpotent correction. Applying
actual root distortion gives the logarithmic switch estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

/-- A switch on a translated right-positioned sheet is measured by its
conjugate displacement. -/
theorem dist_right_switch {G : Type} [Group G] [PseudoMetricSpace G]
    [IsIsometricSMul G G] (x n d : G) :
    dist (x * d) (x * n * d) = dist 1 (d⁻¹ * n * d) := by
  calc
    _ = dist d (n * d) := by simpa only [mul_assoc] using dist_mul_left x d (n * d)
    _ = _ := by simpa only [inv_mul_cancel, mul_assoc] using
      (dist_mul_left d⁻¹ d (n * d)).symm

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- The ambient switch estimate, retaining the full nilpotent correction
and the exponential scalar contraction at the Cartan position. -/
theorem root_switch_bound_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (x : G) (h : H) (v : rootSpace H χ),
      dist (x * Exp h) (x * Exp v * Exp h) ≤
        D * Real.log (2 + C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^
          finrank ℝ (rootSpace H χ) * Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖) := by
  obtain ⟨D, hD, hdist⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  obtain ⟨C, hC, hbound⟩ := exists_rootAction_exp_bound H χ
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  refine ⟨C, D, hC, hD, ?_⟩
  intro x h v
  let w : rootSpace H χ := NormedSpace.exp (rootAction H χ (-h)) v
  have hw : Exp w = (Exp h)⁻¹ * Exp v * Exp h := by
    have hneg : j ((-h : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = -j h := by
      change j (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
      exact map_neg j _
    have hr := represented_root_exp_conjugation H χ j (-h) 1 v
    simp only [one_smul, hneg] at hr
    apply hρ
    rw [map_mul, map_mul, map_inv, hmatch, hmatch, hmatch]
    change algebraExpUnit (j (w : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [algebraExpUnit_neg] at hr
    simpa only [w, inv_inv] using hr
  have hn : ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖ := by
    have hb := hbound (-h) v
    change ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun (-h)‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (χ (-h)) * ‖(rootCoordinates H χ) v‖ at hb
    simpa only [map_neg, norm_neg] using hb
  rw [dist_right_switch, ← hw]
  apply (hdist w).trans
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (by linarith [hn])) hD.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceRootSwitch
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear root switches with subexponential coordinate bounds

At a contact facet the exponential root amplitude cancels its scalar
contraction. The remaining polynomial correction contributes only a
sublinear distance, uniformly in the translated sheet and position.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

theorem sublinear_root_switch_sequence
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ (x : G) (h : H) (t : ℝ),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        |t| * Real.exp (-χ h) ≤ R n →
        dist (x * Exp h)
          (x * Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤ ε * scale n := by
  obtain ⟨C, D, hC, hD, hb⟩ :=
    root_switch_bound_of_published_realization T H χ hχ Exp hExp realize
  let d := finrank ℝ (rootSpace H χ)
  let P := fun n => C * (1 + RH n) ^ d * R n * ‖(rootCoordinates H χ) v‖
  have hbase : HasSubexponentialUpperBoundSeq scale (fun n => 1 + RH n) :=
    (sequence_subexponential_upper_const hs 1).add hRH hs
  have hbase0 : ∀ n, 0 ≤ 1 + RH n := fun n => by linarith [hRH0 n]
  have hpow := hbase.pow hs (Eventually.of_forall hbase0) d
  have hP : HasSubexponentialUpperBoundSeq scale P :=
    (((sequence_subexponential_upper_const hs C).mul hpow
      (Eventually.of_forall (fun _ => hC.le))).mul hR
      (Eventually.of_forall (fun n => mul_nonneg hC.le (pow_nonneg (hbase0 n) d)))).mul
      (sequence_subexponential_upper_const hs _)
      (Eventually.of_forall (fun n => mul_nonneg
        (mul_nonneg hC.le (pow_nonneg (hbase0 n) d)) (hR0 n)))
  have hsum := (sequence_subexponential_upper_const hs 2).add hP hs
  intro ε hε
  filter_upwards [hsum (ε / D) (div_pos hε hD)] with n hn
  intro x h t hh ht
  have hinside : C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
      Real.exp (-χ h) * ‖(rootCoordinates H χ) (t • v)‖ ≤ P n := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ = C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
          (|t| * Real.exp (-χ h)) * ‖(rootCoordinates H χ) v‖ := by ring
      _ ≤ C * (1 + RH n) ^ d * R n * ‖(rootCoordinates H χ) v‖ := by
        gcongr
        exact mul_nonneg hC.le (pow_nonneg (hbase0 n) d)
      _ = _ := rfl
  have hlog : Real.log (2 + P n) ≤ (ε / D) * scale n := by
    have hP0 : 0 ≤ P n := mul_nonneg
      (mul_nonneg (mul_nonneg hC.le (pow_nonneg (hbase0 n) d)) (hR0 n)) (norm_nonneg _)
    exact (Real.log_le_log (by linarith) hn).trans_eq (Real.log_exp _)
  calc
    _ ≤ D * Real.log (2 + C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
        Real.exp (-χ h) * ‖(rootCoordinates H χ) (t • v)‖) := hb x h (t • v)
    _ ≤ D * Real.log (2 + P n) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.log_le_log (by positivity) (by linarith)
    _ ≤ D * ((ε / D) * scale n) := mul_le_mul_of_nonneg_left hlog hD.le
    _ = ε * scale n := by field_simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FacetRootSwitch
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Co-location of neighboring sheets at a contact facet -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Vanishing enlargement of the allowed generator amplitude is absorbed
at the exact facet height. The estimate is uniform in every initial sheet. -/
theorem facet_root_switch_sublinear
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R η : ℕ → ℝ) (q : ℝ)
    (hs : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 ≤ scale n)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ (x : G) (h : H) (t : ℝ),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n → χ h = q * scale n →
        |t| ≤ R n * Real.exp ((q + η n) * scale n) →
        dist (x * Exp h)
          (x * Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤ ε * scale n := by
  let Rc := fun n => R n * Real.exp (η n * scale n)
  have hRc0 : ∀ n, 0 ≤ Rc n := fun n => mul_nonneg (hR0 n) (Real.exp_pos _).le
  have hRc : HasSubexponentialUpperBoundSeq scale Rc :=
    hR.mul (sequence_subexponential_exp_of_vanishing_rate hscale0 hη)
      (Eventually.of_forall hR0)
  intro ε hε
  filter_upwards [sublinear_root_switch_sequence T H χ hχ Exp hExp realize v
    scale RH Rc hs hRH0 hRc0 hRH hRc ε hε] with n hn
  intro x h t hh hfacet ht
  apply hn x h t hh
  calc
    |t| * Real.exp (-χ h) ≤
        (R n * Real.exp ((q + η n) * scale n)) * Real.exp (-χ h) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = Rc n := by
      rw [mul_assoc, ← Real.exp_add, hfacet]
      congr 2
      ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FacetPivotBridgeRate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing rate for the actual bridge at the facet pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

theorem distance_rate_tendsto_zero
    {X : Type} [PseudoMetricSpace X] (scale : ℕ → ℝ) (hs : ∀ n, 0 < scale n)
    (a b : ℕ → X)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, dist (a n) (b n) ≤ ε * scale n) :
    Tendsto (fun n => dist (a n) (b n) / scale n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hnear (ε / 2) (by positivity)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg dist_nonneg (hs n).le)]
  exact ((div_le_iff₀ (hs n)).mpr hn).trans_lt (half_lt_self hε)

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- No bridge estimate is postulated: root distortion at the exact facet
height supplies a nonnegative error rate tending to zero, uniformly over
the initial source state. -/
theorem exists_facet_pivot_bridge_rate
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (pivot : H) (scale R η t : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((χ pivot + η n) * scale n)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n x, dist (x * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ δ n * scale n := by
  let B := ‖(finBasis ℝ H).equivFun pivot‖
  let RH := fun n => (B + 1) * (1 + scale n) ^ 1
  have hB : 0 ≤ B := norm_nonneg _
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < B + 1) 1).along_sequence hs
  let left := fun n => Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let right := fun n => Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * left n
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      dist (left n) (right n) ≤ ε * scale n := by
    intro ε hε
    filter_upwards [facet_root_switch_sublinear T H χ hχ Exp hExp realize v
      scale RH R η (χ pivot) hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη ε hε] with n hn
    have hsize : ‖(finBasis ℝ H).equivFun (scale n • pivot)‖ ≤ RH n := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg (hscale n).le]
      change scale n * B ≤ (B + 1) * (1 + scale n) ^ 1
      nlinarith [hscale n]
    have hfacet : χ (scale n • pivot) = χ pivot * scale n := by
      rw [map_smul, smul_eq_mul, mul_comm]
    simpa only [left, right, one_mul, SetLike.val_smul] using
      hn 1 (scale n • pivot) (t n) hsize hfacet (ht n)
  let δ := fun n => dist (left n) (right n) / scale n
  refine ⟨δ, fun n => div_nonneg dist_nonneg (hscale n).le,
    distance_rate_tendsto_zero scale hscale left right hnear, ?_⟩
  intro n x
  have he : δ n * scale n = dist (left n) (right n) :=
    div_mul_cancel₀ _ (hscale n).ne'
  rw [he, mul_assoc, dist_mul_left]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInvariantOrbit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a label in a finite linear group

Embedding a vector in the Euclidean product of all its group translates
provides an invariant strictly convex norm without changing the topology or
norm instances on the original height space.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W E : Type} [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ] (e : W →ₗ[ℝ] E)

omit [Fintype Γ] in
theorem finiteOrbitEmbedding_injective (he : Function.Injective e) :
    Function.Injective (finiteOrbitEmbedding Γ e) := by
  intro w u h
  apply he
  have hh := congrArg (fun f : PiLp 2 (fun _ : Γ => E) => f 1) h
  simpa using hh

theorem finiteOrbitEmbedding_norm (g : Γ) (w : W) :
    ‖finiteOrbitEmbedding Γ e (g.val w)‖ = ‖finiteOrbitEmbedding Γ e w‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  change (∑ k : Γ, ‖e ((k * g).val w)‖ ^ 2) = ∑ k : Γ, ‖e (k.val w)‖ ^ 2
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HyperplaneReflection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reflection forced by agreement on a facet -/

noncomputable section
namespace PolycyclicRecognition

open scoped RealInnerProductSpace

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem fixed_hyperplane_image_normal
    (A : W ≃ₗᵢ[ℝ] W) (v : W) (hv : v ≠ 0)
    (hfix : ∀ w, ⟪w, v⟫ = 0 → A w = w) :
    ∃ c : ℝ, A v = c • v := by
  let c := ⟪A v, v⟫ / ‖v‖ ^ 2
  let w := A v - c • v
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hw : ⟪w, v⟫ = 0 := by
    dsimp only [w]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp only [c]
    simp [hn]
  have hvw : ⟪v, w⟫ = 0 := (real_inner_comm v w).symm.trans hw
  have haw : ⟪A v, w⟫ = 0 := by
    rw [← hfix w hw, A.inner_map_map]
    exact hvw
  have hww : ⟪w, w⟫ = 0 := by
    conv_lhs => lhs; rw [show w = A v - c • v from rfl]
    rw [inner_sub_left, inner_smul_left, haw, hvw]
    simp
  have hw0 : w = 0 := inner_self_eq_zero.mp hww
  exact ⟨c, sub_eq_zero.mp hw0⟩

/-- A nonidentity orthogonal map fixing a hyperplane reverses its normal.
This is the linear step in the neighboring-label reflection argument. -/
theorem orthogonal_map_fixing_hyperplane_negates_normal
    (A : W ≃ₗᵢ[ℝ] W) (v : W) (hv : v ≠ 0)
    (hfix : ∀ w, ⟪w, v⟫ = 0 → A w = w)
    (hne : A ≠ LinearIsometryEquiv.refl ℝ W) : A v = -v := by
  obtain ⟨c, hc⟩ := fixed_hyperplane_image_normal A v hv hfix
  have hnorm : |c| = 1 := by
    have he := A.norm_map v
    rw [hc, norm_smul, Real.norm_eq_abs] at he
    nlinarith [norm_pos_iff.mpr hv]
  rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
  · have hav : A v = v := by simpa [h] using hc
    apply (hne ?_).elim
    ext x
    let d := ⟪x, v⟫ / ‖v‖ ^ 2
    have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
    have hw : ⟪x - d • v, v⟫ = 0 := by
      rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
      dsimp only [d]
      simp [hn]
    have he := hfix (x - d • v) hw
    rw [map_sub, map_smul, hav] at he
    exact sub_left_inj.mp he
  · simpa [h] using hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteLabelReflection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A reflected direction for two distinct finite labels agreeing on a facet

The invariant Euclidean norm is pulled back from the finite orbit embedding,
only inside the proof. The height space keeps its original norm and topology.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped RealInnerProductSpace

variable {W E : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Distinct finite labels fixing the same affine facet have an outward
direction on which their images are opposite. The hypothesis here is just
agreement of their linear parts along the facet kernel. -/
theorem exists_reflected_direction_of_finite_labels_of_embedding
    (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ]
    (e : W →ₗ[ℝ] E) (he : Function.Injective e)
    (A C : Γ) (hne : A ≠ C) (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfix : ∀ w, ℓ w = 0 → A.val w = C.val w) :
    ∃ v : W, 0 < ℓ v ∧ C.val v = -A.val v := by
  let L := finiteOrbitEmbedding Γ e
  let : NormedAddCommGroup W := NormedAddCommGroup.induced W _ L
    (finiteOrbitEmbedding_injective Γ e he)
  let : NormedSpace ℝ W := NormedSpace.induced ℝ W _ L
  let : InnerProductSpace ℝ W := InnerProductSpace.induced L
  let R : W ≃ₗᵢ[ℝ] W :=
    { (A⁻¹ * C).val with
      norm_map' := finiteOrbitEmbedding_norm Γ e (A⁻¹ * C) }
  let v := (InnerProductSpace.toDual ℝ W).symm ℓ.toContinuousLinearMap
  have hvℓ (w : W) : ⟪v, w⟫ = ℓ w :=
    InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro h
    apply hℓ
    ext w
    rw [← hvℓ, h]
    simp
  have hvpos : 0 < ℓ v := by
    rw [← hvℓ]
    exact real_inner_self_pos.mpr hv
  have hrfix (w : W) (hw : ⟪w, v⟫ = 0) : R w = w := by
    have hwℓ : ℓ w = 0 := by rw [← hvℓ, real_inner_comm]; exact hw
    change A.val.symm (C.val w) = w
    rw [← hfix w hwℓ, LinearEquiv.symm_apply_apply]
  have hrne : R ≠ LinearIsometryEquiv.refl ℝ W := by
    intro h
    apply hne
    apply Subtype.ext
    ext w
    have hw := LinearIsometryEquiv.congr_fun h w
    change A.val.symm (C.val w) = w at hw
    exact (congrArg A.val hw).symm.trans (by simp)
  have hvR := orthogonal_map_fixing_hyperplane_negates_normal R v hv hrfix hrne
  refine ⟨v, hvpos, ?_⟩
  have hh := congrArg A.val hvR
  change A.val (A.val.symm (C.val v)) = A.val (-v) at hh
  simpa using hh

/-- No Euclidean structure on the height space is required: its finite
dimension supplies the auxiliary injective map used in the proof. -/
theorem exists_reflected_direction_of_finite_labels
    (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Finite Γ]
    (A C : Γ) (hne : A ≠ C) (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfix : ∀ w, ℓ w = 0 → A.val w = C.val w) :
    ∃ v : W, 0 < ℓ v ∧ C.val v = -A.val v := by
  let := Fintype.ofFinite Γ
  let e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) :=
    (Module.finBasis ℝ W).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  exact exists_reflected_direction_of_finite_labels_of_embedding Γ e.toLinearMap
    e.injective A C hne ℓ hℓ hfix

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineFacetAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine agreement on a facet determines the tangential linear part -/

namespace PolycyclicRecognition

variable {W V : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Agreement on a relative neighborhood of a facet point implies agreement
of linear parts on the entire parallel hyperplane. -/
theorem linear_eq_on_kernel_of_affine_facet_agreement
    (A C : W →ₗ[ℝ] V) (b₁ b₂ : V) (ℓ : W →ₗ[ℝ] ℝ)
    (p : W) {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A q + b₁ = C q + b₂) :
    ∀ w, ℓ w = 0 → A w = C w := by
  have hp := hagree p rfl (by simpa using hρ)
  intro w hw
  let t := ρ / (2 * (‖w‖ + 1))
  have ht : 0 < t := div_pos hρ (by positivity)
  have htw : ‖t • w‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖w‖ + 1))).mpr
    nlinarith [norm_nonneg w]
  have he := hagree (p + t • w) (by simp [hw]) (by simpa using htw)
  simp only [map_add, map_smul] at he
  have he' : t • A w = t • C w := by
    calc
      t • A w = (A p + t • A w + b₁) - (A p + b₁) := by abel
      _ = (C p + t • C w + b₂) - (C p + b₂) := by rw [he, hp]
      _ = t • C w := by abel
  exact smul_right_injective _ ht.ne' he'

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InwardFacetSegment
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A short inward segment for finitely many facet inequalities -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W I : Type} [AddCommGroup W] [Module ℝ W] [Fintype I]

/-- A direction pointing inward at every active constraint stays in the
polyhedron for one common positive interval. -/
theorem exists_inward_facet_interval
    (α : I → W →ₗ[ℝ] ℝ) (c : I → ℝ) (p v : W)
    (hp : ∀ i, α i p ≤ c i)
    (hv : ∀ i, α i p = c i → 0 ≤ α i v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ i, α i (p - t • v) ≤ c i := by
  classical
  let bound : Option I → ℝ := fun o => o.elim 1 fun i =>
    if α i v < 0 then (c i - α i p) / (1 - α i v) else 1
  have hb : ∀ o, 0 < bound o := by
    intro o
    cases o with
    | none => exact zero_lt_one
    | some i =>
      dsimp only [bound, Option.elim_some]
      split_ifs with h
      · have hlt : α i p < c i := lt_of_le_of_ne (hp i) (by
          intro he
          exact (not_le_of_gt h) (hv i he))
        exact div_pos (sub_pos.mpr hlt) (by linarith)
      · exact zero_lt_one
  let ε := Finset.univ.inf' Finset.univ_nonempty bound
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun o _ => hb o)
  refine ⟨ε, hε, ?_⟩
  intro t ht i
  simp only [map_sub, map_smul, smul_eq_mul]
  by_cases hn : α i v < 0
  · have hbound : ε ≤ (c i - α i p) / (1 - α i v) := by
      have hh := Finset.inf'_le (f := bound) (Finset.mem_univ (some i))
      simpa only [bound, Option.elim_some, ite_eq_left hn] using hh
    have hh := (le_div_iff₀ (by linarith : 0 < 1 - α i v)).mp
      (ht.2.trans hbound)
    nlinarith [ht.1]
  · have := hp i
    nlinarith [mul_nonneg ht.1 (le_of_not_gt hn)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ReflectedSegmentSupport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponent gain from two reflected segments

The reflection-doubling identity follows from finite balanced support data
and gives the support gain for a pair of reflected segments.
-/

noncomputable section
namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [FiniteDimensional ℝ W] in
private theorem compact_segment (w : W) : IsCompact (segment ℝ 0 w) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
    (continuous_id.smul continuous_const))

omit [Nonempty B] in
theorem weightSupport_union {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) (hneF : F.Nonempty) (i : I) :
    D.weightSupport (E ∪ F) i = max (D.weightSupport E i) (D.weightSupport F i) := by
  obtain ⟨x, hx, he⟩ := D.exists_weightSupport_point hE hneE i
  obtain ⟨y, hy, hf⟩ := D.exists_weightSupport_point hF hneF i
  obtain ⟨z, hz, hu⟩ := D.exists_weightSupport_point (hE.union hF)
    (hneE.mono subset_union_left) i
  apply le_antisymm
  · rw [hu]
    rcases hz with hz | hz
    · exact (D.weight_le_weightSupport hE hz i).trans (le_max_left _ _)
    · exact (D.weight_le_weightSupport hF hz i).trans (le_max_right _ _)
  · apply max_le
    · rw [he]
      exact D.weight_le_weightSupport (hE.union hF) (Or.inl hx) i
    · rw [hf]
      exact D.weight_le_weightSupport (hE.union hF) (Or.inr hy) i

omit [Nonempty B] in
theorem weightSupport_opposite_segments (w : W) (i : I) :
    D.weightSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) i =
      max 0 (D.weight i w) + max 0 (D.weight i (-w)) := by
  rw [D.weightSupport_union (compact_segment w) ⟨0, left_mem_segment ..⟩
    (compact_segment (-w)) ⟨0, left_mem_segment ..⟩,
    D.weightSupport_segment, D.weightSupport_segment, map_neg]
  rcases le_total 0 (D.weight i w) with h | h
  · simp [h]
  · simp [h]

omit [Nonempty B] in
theorem basisTemplateSupport_opposite_segments (w : W) (b : B) :
    D.basisTemplateSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) b =
      2 * D.basisSupport b w := by
  simp only [basisTemplateSupport, D.weightSupport_opposite_segments,
    mul_add, Finset.sum_add_distrib]
  change D.basisSupport b w + D.basisSupport b (-w) = _
  rw [D.basisSupport_neg]
  ring

theorem templateSupport_opposite_segments (w : W) :
    D.templateSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) =
      2 * D.segmentSupport w := by
  apply le_antisymm
  · apply D.templateSupport_le
    intro b
    rw [D.basisTemplateSupport_opposite_segments]
    exact mul_le_mul_of_nonneg_left (D.basisSupport_le b w) (by norm_num)
  · obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun b => D.basisSupport b w)
    change 2 * Finset.univ.sup' _ _ ≤ _
    rw [hb, ← D.basisTemplateSupport_opposite_segments]
    exact D.basisTemplateSupport_le _ b

/-- Opposite images have twice the single-segment volume exponent. -/
theorem reflected_segment_support
    (A C : PolycyclicRecognition.templateSymmetryGroup D) {w : W}
    (hw : w ≠ 0) (hreflect : C.val w = -A.val w) :
    D.templateSupport (A.val '' segment ℝ 0 w) = D.segmentSupport w ∧
    D.templateSupport (C.val '' segment ℝ 0 w) = D.segmentSupport w ∧
    D.templateSupport ((A.val '' segment ℝ 0 w) ∪ (C.val '' segment ℝ 0 w)) =
      2 * D.segmentSupport w ∧ 0 < D.segmentSupport w := by
  have him (L : W ≃ₗ[ℝ] W) : L '' segment ℝ 0 w = segment ℝ 0 (L w) := by
    change L.toLinearMap.toAffineMap '' segment ℝ 0 w = _
    rw [image_segment]
    simp
  have ha := A.property (segment ℝ 0 w) (compact_segment w)
    ⟨0, left_mem_segment ..⟩ (convex_segment 0 w)
  have hc := C.property (segment ℝ 0 w) (compact_segment w)
    ⟨0, left_mem_segment ..⟩ (convex_segment 0 w)
  rw [D.templateSupport_segment] at ha hc
  refine ⟨ha, hc, ?_, D.segmentSupport_pos hw⟩
  rw [him A.val, him C.val, hreflect, D.templateSupport_opposite_segments]
  rw [him A.val, D.templateSupport_segment] at ha
  rw [ha]

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FacetReflectionTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reflected source and target templates

Starting from distinct finite affine labels agreeing near a facet, construct
an inward source segment and prove all the support identities in equation
(reflection-doubling) of `labels.tex`.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W I B J : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B] [Fintype J]

theorem exists_reflection_templates
    (D : SupportDatum W I B) (A C : templateSymmetryGroup D) (hne : A ≠ C)
    (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (b₁ b₂ p : W)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A.val q + b₁ = C.val q + b₂) :
    ∃ w : W, ℓ w < 0 ∧ C.val w = -A.val w ∧
      ((fun x => x + p) '' segment ℝ 0 w) ⊆ {x | ∀ j, α j x ≤ c j} ∧
      let E := (fun x => x + p) '' segment ℝ 0 w
      let E₁ := A.val '' segment ℝ 0 w
      let E₂ := C.val '' segment ℝ 0 w
      0 < D.templateSupport E ∧ D.templateSupport E₁ = D.templateSupport E ∧
        D.templateSupport E₂ = D.templateSupport E ∧
        D.templateSupport (E₁ ∪ E₂) = 2 * D.templateSupport E := by
  have hfix := linear_eq_on_kernel_of_affine_facet_agreement A.val.toLinearMap
    C.val.toLinearMap b₁ b₂ ℓ p hρ hagree
  obtain ⟨v, hv, href⟩ := exists_reflected_direction_of_finite_labels
    (templateSymmetryGroup D) A C hne ℓ hℓ hfix
  obtain ⟨ε, hε, hinside⟩ := exists_inward_facet_interval α c p v hp (by
    intro j hj
    obtain ⟨t, ht, he⟩ := hactive j hj
    rw [he, LinearMap.smul_apply, smul_eq_mul]
    exact (mul_pos ht hv).le)
  let w := -(ε • v)
  have hwℓ : ℓ w < 0 := by
    dsimp only [w]
    rw [map_neg, map_smul, smul_eq_mul]
    exact neg_neg_of_pos (mul_pos hε hv)
  have hw : w ≠ 0 := by
    intro he
    rw [he, map_zero] at hwℓ
    exact (lt_irrefl 0) hwℓ
  have hwref : C.val w = -A.val w := by
    simp [w, href]
  have hset : ((fun x => x + p) '' segment ℝ 0 w) ⊆
      {x | ∀ j, α j x ≤ c j} := by
    rintro x ⟨y, hy, rfl⟩ j
    rw [segment_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hte : t * ε ∈ Icc (0 : ℝ) ε :=
      ⟨mul_nonneg ht.1 hε.le, by nlinarith [ht.2]⟩
    have hh := hinside (t * ε) hte j
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [w, smul_zero, zero_add, smul_neg, smul_smul]
    abel_nf
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hsource := D.templateSupport_translate hc ⟨0, left_mem_segment ..⟩ p
  rw [D.templateSupport_segment] at hsource
  obtain ⟨ha, hb, hu, hpos⟩ := D.reflected_segment_support A C hw hwref
  refine ⟨w, hwℓ, hwref, hset, ?_⟩
  simpa only [hsource] using And.intro hpos (And.intro ha (And.intro hb hu))

/-- Near a point with only parallel active constraints, the entire contact
hyperplane remains in the polyhedron. -/
theorem exists_relative_facet_neighborhood
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (p : W) (ℓ : W →ₗ[ℝ] ℝ)
    (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ →
      ∀ j, α j q ≤ c j := by
  have hevent (j : J) : ∀ᶠ q in nhds p,
      α j p ≠ c j → α j q < c j := by
    by_cases hj : α j p = c j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hj))
    · have hc := (α j).continuous_of_finiteDimensional
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds (lt_of_le_of_ne (hp j) hj)]
        with q hq
      exact fun _ => hq
  obtain ⟨ρ, hρ, hnear⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hevent)
  refine ⟨ρ, hρ, ?_⟩
  intro q hq hn j
  by_cases hj : α j p = c j
  · obtain ⟨t, _, ht⟩ := hactive j hj
    rw [ht, LinearMap.smul_apply, hq, ← LinearMap.smul_apply, ← ht, hj]
  · exact (hnear (by simpa only [dist_eq_norm] using hn) j hj).le

/-- The reflected source segment contradicts the support inequality obtained
from actual coupled bundles. This is the finite-dimensional last step. -/
theorem affine_labels_eq_of_template_comparison
    (D : SupportDatum W I B) (A C : templateSymmetryGroup D)
    (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (b₁ b₂ p : W)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A.val q + b₁ = C.val q + b₂)
    (hcompare : ∀ E : Set W, IsCompact E → Convex ℝ E →
      E ⊆ {x | ∀ j, α j x ≤ c j} → p ∈ E →
      D.templateSupport ((A.val '' ((fun x => x - p) '' E)) ∪
        (C.val '' ((fun x => x - p) '' E))) ≤ D.templateSupport E) : A = C := by
  by_contra hne
  obtain ⟨w, _, _, hinside, hpos, _, _, hdouble⟩ :=
    exists_reflection_templates D A C hne ℓ hℓ b₁ b₂ p α c hp hactive hρ hagree
  let E := (fun x => x + p) '' segment ℝ 0 w
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hE : IsCompact E := hc.image (continuous_id.add continuous_const)
  have hconv : Convex ℝ E := (convex_segment (0 : W) w).affine_image
    ((AffineMap.id ℝ W) + AffineMap.const ℝ W p)
  have hpE : p ∈ E := ⟨0, left_mem_segment .., zero_add p⟩
  have hsub : (fun x => x - p) '' E = segment ℝ 0 w := by
    ext x
    simp only [E, mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [add_sub_cancel_right] using hz
    · intro hx
      exact ⟨x + p, ⟨x, hx, rfl⟩, add_sub_cancel_right x p⟩
  have hle := hcompare E hE hconv hinside hpE
  rw [hsub, hdouble] at hle
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialChartCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial logarithm bounds for the actual scaled coordinate charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Unit letter weights give the ordinary bracket length. -/
theorem bracketWordExponent_one {I : Type} [Fintype I] [DecidableEq I]
    (w : FreeMagma I) : bracketWordExponent (fun _ => 1) w = bracketWordLength w := by
  induction w using FreeMagma.rec with
  | of i => simp [bracketWordLength]
  | mul u v hu hv =>
      change bracketWordExponent (fun _ => 1) (u * v) = _
      rw [bracketWordExponent_mul, hu, hv]
      simp only [bracketWordLength, Nat.cast_add]

/-- Integer coordinate weights make the logarithm of every bounded chart
point polynomially bounded in the actual scale, in any fixed reference
basis. This estimate does not assume a limiting group or metric. -/
theorem norm_polynomial_chart_log_le
    {L J K : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J] [Fintype K]
    (b : Basis J ℝ L) (b₀ : Basis K ℝ L) (cost : J → ℕ)
    (p : ℕ) (hp : ∀ j, cost j ≤ p)
    {r : ℝ} (hr : 1 ≤ r) (z : J → ℝ) :
    ‖b₀.equivFun ((exponentialRescaleBasis b (fun j => (cost j : ℝ)) (Real.log r)).equivFun.symm z)‖ ≤
      (∑ j, ‖b₀.equivFun (b j)‖) * ‖z‖ * (1 + r) ^ p := by
  have hr0 : 0 < r := by linarith
  rw [Basis.equivFun_symm_apply, map_sum]
  apply (norm_sum_le _ _).trans
  have hterm (j : J) :
      ‖b₀.equivFun (z j • exponentialRescaleBasis b (fun j => (cost j : ℝ)) (Real.log r) j)‖ ≤
        ‖b₀.equivFun (b j)‖ * ‖z‖ * (1 + r) ^ p := by
    simp only [exponentialRescaleBasis, Basis.unitsSMul_apply, Units.smul_def,
      Units.val_mk0, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (Real.log r * (cost j : ℝ)) = r ^ cost j := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
    rw [hexp]
    have hpow : r ^ cost j ≤ (1 + r) ^ p :=
      (pow_le_pow_left₀ hr0.le (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (hp j))
    have hz := norm_le_pi_norm z j
    rw [Real.norm_eq_abs] at hz
    nlinarith [mul_le_mul hz hpow (pow_nonneg hr0.le _) (norm_nonneg z),
      norm_nonneg (b₀.equivFun (b j))]
  calc
    _ ≤ ∑ j, ‖b₀.equivFun (b j)‖ * ‖z‖ * (1 + r) ^ p :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedGoodSetSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profile neighborhoods selected from a supported weak limit -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- Each open neighborhood of a supported profile has a fixed positive
mass along every sufficiently late member of the weakly convergent family. -/
theorem eventual_positive_mass_of_supported_weak_limit
    {X ι : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, c ≤ ((μs i : Measure X) U).toReal := by
  have hp : 0 < (μ : Measure X) U :=
    (Measure.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)
  have hfin : (μ : Measure X) U ≠ ∞ := measure_ne_top _ _
  have hr : 0 < ((μ : Measure X) U).toReal := ENNReal.toReal_pos hp.ne' hfin
  let c := ((μ : Measure X) U).toReal / 2
  have hc : 0 < c := half_pos hr
  have hlt : ENNReal.ofReal c < (μ : Measure X) U :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfin).mpr (half_lt_self hr)
  have he := eventually_lt_of_lt_liminf
    (hlt.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hU))
  refine ⟨c, hc, he.mono ?_⟩
  intro i hi
  exact ((ENNReal.ofReal_lt_iff_lt_toReal hc.le (measure_ne_top _ _)).mp hi).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DiagonalProfileSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A diagonal of supported laws with subexponential retained mass

Each outer parameter has its own limiting law and supported profile. The
inner scale is chosen after the outer parameter, with arbitrary eventual
side conditions. This preserves positive mass at every selected scale.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem exists_diagonal_supported_neighborhoods
    {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (samples : ℕ → ℕ → ProbabilityMeasure A) (profile : ℕ → ℕ → A → X)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure X)
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (samples j n) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 (ν j)))
    (f : ℕ → X) (hf : ∀ j, f j ∈ (ν j : Measure X).support)
    (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j)) (hfU : ∀ j, f j ∈ U j)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (n : ℕ → ℕ) (B : ℕ → Set A),
      (∀ j, P j (n j)) ∧ Tendsto (fun j => scale j (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧ (∀ j, 0 < ((samples j (n j) : Measure A) (B j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale j (n j))
        (fun j => ((samples j (n j) : Measure A) (B j)).toReal) ∧
      ∀ j a, a ∈ B j → profile j (n j) a ∈ U j := by
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e] <;> positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose c hc hmass using fun j =>
    eventual_positive_mass_of_supported_weak_limit (hν j) (hf j) (hU j) (hfU j)
  have hchoose j : ∃ n, P j n ∧ (j : ℝ) + 1 ≤ scale j n ∧
      Real.exp (-e j * scale j n) ≤
        ((ProbabilityMeasure.map (samples j n) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure X) (U j)).toReal := by
    have hexp := ((subexponential_lower_const (hc j)).along_sequence (hs j)) (e j) (he j)
    obtain ⟨n, hn, hr, hm, he'⟩ := ((hP j).and
      (((hs j).eventually (eventually_ge_atTop ((j : ℝ) + 1))).and
        ((hmass j).and hexp))).exists
    exact ⟨n, hn, hr, he'.trans hm⟩
  choose n hn hr hm using hchoose
  let B : ℕ → Set A := fun j => profile j (n j) ⁻¹' U j
  have hmap j : ((ProbabilityMeasure.map (samples j (n j)) (f := (profile j (n j))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure X)
      (U j)).toReal = ((samples j (n j) : Measure A) (B j)).toReal := by
    rw [show (ProbabilityMeasure.map (samples j (n j)) (f := (profile j (n j))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure X) =
      Measure.map (profile j (n j)) (samples j (n j) : Measure A) from rfl,
      Measure.map_apply (hp j (n j)) (hU j).measurableSet]
  have hm' j : Real.exp (-e j * scale j (n j)) ≤
      ((samples j (n j) : Measure A) (B j)).toReal := by simpa only [hmap] using hm j
  have hr0 j : 0 ≤ scale j (n j) := le_trans (by positivity) (hr j)
  have hscale : Tendsto (fun j => scale j (n j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (le_add_of_nonneg_right zero_le_one).trans (hr j))
      tendsto_natCast_atTop_atTop
  refine ⟨n, B, hn, hscale, fun j => (hp j (n j)) (hU j).measurableSet,
    fun j => (Real.exp_pos _).trans_le (hm' j), ?_, ?_⟩
  · intro δ hδ
    filter_upwards [helim.eventually (gt_mem_nhds hδ)] with j hj
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hj.le) (hr0 j))).trans
      (hm' j)
  · intro j a ha
    exact ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCellProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profiles in the original Haar cells

The good sets remain subsets of the original recurrence cells, and their
probability estimate is exactly a relative Haar-volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem cellProbabilityMeasure_apply_toReal
    {N : Type} [MeasurableSpace N] (μ : Measure N)
    (Q B : Set N) (hQ0 : μ Q ≠ 0) (hQfin : μ Q ≠ ∞) (hB : MeasurableSet B) :
    ((cellProbabilityMeasure μ Q hQ0 hQfin : Measure N) B).toReal =
      (μ (B ∩ Q)).toReal / (μ Q).toReal := by
  change (((μ Q)⁻¹ • μ.restrict Q) B).toReal = _
  rw [Measure.smul_apply, Measure.restrict_apply hB]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DiagonalCellProfilePairs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal's two profiles retain subexponential relative Haar mass -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The concrete coordinate balls absorb every later compact path set. -/
theorem compact_eventually_subset_coordinate_balls
    {V : Type} [PseudoMetricSpace V] (x : V) (C : Set V) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, C ⊆ Metric.closedBall x ((n : ℝ) + 1) := by
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall x
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventually_ge_atTop r)] with n hn
  exact hr.trans (Metric.closedBall_subset_closedBall (by linarith))

theorem exists_diagonal_good_cell_profile_pairs
    {V W A : Type} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : ℕ → Set V) (hK : ∀ j, IsCompact (K j))
    (hcover : ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, C ⊆ K j)
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (μ : Measure A) (Q : ℕ → ℕ → Set A)
    (hQ : ∀ j n, MeasurableSet (Q j n))
    (hQ0 : ∀ j n, μ (Q j n) ≠ 0) (hQfin : ∀ j n, μ (Q j n) ≠ ∞)
    (profile : ℕ → ℕ → A → S × S)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (cellProbabilityMeasure μ (Q j n) (hQ0 j n) (hQfin j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g))
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (u n : ℕ → ℕ) (B : ℕ → Set A),
      Tendsto u atTop atTop ∧ (∀ j, P (u j) (n j)) ∧
      Tendsto (fun j => scale (u j) (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧
      (∀ j, B j ⊆ Q (u j) (n j)) ∧
      (∀ j, 0 < (μ (B j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
        (fun j => (μ (B j)).toReal / (μ (Q (u j) (n j))).toReal) ∧
      ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, ∀ a ∈ B j, ∀ z ∈ C,
        ‖(profile (u j) (n j) a).1.val z - g.1.val z‖ < 2 / ((j : ℝ) + 1) ∧
        ‖(profile (u j) (n j) a).2.val z - g.2.val z‖ < 2 / ((j : ℝ) + 1) := by
  let : ∀ j, CompactSpace (K j) := fun j => isCompact_iff_compactSpace.mp (hK j)
  let res : ∀ j, C(S, C(K j, W)) := fun j =>
    ⟨fun g => g.val.comp ⟨Subtype.val, continuous_subtype_val⟩,
      (ContinuousMap.continuous_precomp ⟨Subtype.val, continuous_subtype_val⟩).comp
        continuous_subtype_val⟩
  let observe : ∀ j, C(S × S, C(K j, W) × C(K j, W)) := fun j =>
    ⟨fun g => (res j g.1, res j g.2), ((res j).continuous.comp continuous_fst).prodMk
      ((res j).continuous.comp continuous_snd)⟩
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e] <;> positivity
  have hclose j : ∀ᶠ m in atTop, ‖observe j (f m) - observe j g‖ < e j := by
    have ht := (((observe j).continuous.tendsto g).comp hfg).sub
      (tendsto_const_nhds (x := observe j g))
    have htn : Tendsto (fun m => ‖observe j (f m) - observe j g‖) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self, norm_zero] using ht.norm
    exact htn.eventually (gt_mem_nhds (he j))
  have hu j : ∃ m, j ≤ m ∧ ‖observe j (f m) - observe j g‖ < e j :=
    ((eventually_ge_atTop j).and (hclose j)).exists
  choose u hule huc using hu
  have hut : Tendsto u atTop atTop := tendsto_atTop_mono hule tendsto_id
  let U : ℕ → Set (S × S) := fun j =>
    (observe j) ⁻¹' Metric.ball (observe j (f (u j))) (e j)
  have hU j : IsOpen (U j) := Metric.isOpen_ball.preimage (observe j).continuous
  have hfU j : f (u j) ∈ U j := by
    change dist (observe j (f (u j))) (observe j (f (u j))) < e j
    simpa only [dist_self] using he j
  obtain ⟨n, B, hn, hr, hB, hBpos, hmass, happ⟩ := exists_diagonal_supported_neighborhoods
    (fun j => scale (u j)) (fun j => hs (u j))
    (fun j n => cellProbabilityMeasure μ (Q (u j) n) (hQ0 (u j) n) (hQfin (u j) n)) (fun j => profile (u j)) (fun j => hp (u j))
    (fun j => ν (u j)) (fun j => hν (u j)) (fun j => f (u j)) (fun j => hf (u j))
    U hU hfU (fun j => P (u j)) (fun j => hP (u j))
  let Good := fun j => B j ∩ Q (u j) (n j)
  have hmassEq j :
      ((cellProbabilityMeasure μ (Q (u j) (n j)) (hQ0 (u j) (n j)) (hQfin (u j) (n j)) :
        Measure A) (B j)).toReal = (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal :=
    cellProbabilityMeasure_apply_toReal μ _ _ _ _ (hB j)
  have hGoodmass : HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
      (fun j => (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal) := by
    simpa only [hmassEq] using hmass
  have hGoodpos j : 0 < (μ (Good j)).toReal := by
    have h := hBpos j
    rw [hmassEq] at h
    exact (div_pos_iff.mp h).resolve_right (fun hn => (ENNReal.toReal_nonneg).not_gt hn.1) |>.1
  refine ⟨u, n, Good, hut, hn, hr, fun j => (hB j).inter (hQ (u j) (n j)),
    fun _ => inter_subset_right, hGoodpos, hGoodmass, ?_⟩
  intro C hC
  filter_upwards [hcover C hC] with j hj
  intro a ha z hz
  have hzK := hj hz
  have hab : ‖observe j (profile (u j) (n j) a) - observe j (f (u j))‖ < e j := by
    simpa only [U, mem_preimage, Metric.mem_ball, dist_eq_norm] using happ j a ha.1
  have htriangle := norm_add_le
    (observe j (profile (u j) (n j) a) - observe j (f (u j)))
    (observe j (f (u j)) - observe j g)
  rw [sub_add_sub_cancel] at htriangle
  have hb : ‖observe j (profile (u j) (n j) a) - observe j g‖ < 2 / ((j : ℝ) + 1) := by
    apply htriangle.trans_lt
    dsimp only [e] at hab huc
    rw [show (2 : ℝ) / ((j : ℝ) + 1) =
      1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) by ring]
    exact add_lt_add hab (huc j)
  have hfst : ‖res j (profile (u j) (n j) a).1 - res j g.1‖ ≤
      ‖observe j (profile (u j) (n j) a) - observe j g‖ := norm_fst_le (observe j (profile (u j) (n j) a) - observe j g)
  have hsnd : ‖res j (profile (u j) (n j) a).2 - res j g.2‖ ≤
      ‖observe j (profile (u j) (n j) a) - observe j g‖ := norm_snd_le (observe j (profile (u j) (n j) a) - observe j g)
  exact ⟨((res j (profile (u j) (n j) a).1 - res j g.1).norm_coe_le_norm ⟨z, hzK⟩).trans_lt
    (hfst.trans_lt hb), ((res j (profile (u j) (n j) a).2 - res j g.2).norm_coe_le_norm
      ⟨z, hzK⟩).trans_lt (hsnd.trans_lt hb)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AffineProfileBoundary
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending affine profiles to a polytope's boundary -/

namespace PolycyclicRecognition

open Set
open scoped Topology

variable {V W Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Affineness over the interior already determines the profile over the
closed convex cell, including the contact facet. Surjectivity of height is
retained, so closure commutes with its inverse image. -/
theorem affine_profile_on_closed_cell
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (C : Set W) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hint : (interior C).Nonempty)
    (f : V → Y) (hf : Continuous f) (A : W →L[ℝ] Y) (b : Y)
    (haffine : ∀ z, q z ∈ interior C → f z = A (q z) + b) :
    ∀ z, q z ∈ C → f z = A (q z) + b := by
  have hzero : IsClosed {z : V | f z = A (q z) + b} :=
    isClosed_eq hf ((A.continuous.comp hq).add continuous_const)
  have hcl : closure (q ⁻¹' interior C) = q ⁻¹' C := by
    rw [← (q.isOpenMap_of_finiteDimensional hqsurj).preimage_closure_eq_closure_preimage hq,
      hC.closure_interior_eq_closure_of_nonempty_interior hint, hclosed.closure_eq]
  have hsub : closure (q ⁻¹' interior C) ⊆ {z : V | f z = A (q z) + b} :=
    closure_minimal haffine hzero
  rw [hcl] at hsub
  exact hsub

omit [NormedSpace ℝ V] [NormedSpace ℝ Y] in
/-- Once the linear label is fixed, evaluating at one eventually affine
point determines the limiting offset; no separate boundedness assumption
on the offsets is needed. -/
theorem affine_offset_tendsto
    (f : ℕ → C(V, Y)) (g : C(V, Y)) (hf : Filter.Tendsto f Filter.atTop (nhds g))
    (z : V) (a : Y) (b : ℕ → Y)
    (h : ∀ᶠ n in Filter.atTop, f n z = a + b n) :
    Filter.Tendsto b Filter.atTop (nhds (g z - a)) := by
  have ht := ((continuous_eval_const z).tendsto g |>.comp hf).sub_const a
  apply ht.congr'
  filter_upwards [h] with n hn
  change f n z - a = b n
  rw [hn, add_sub_cancel_left]

/-- A limiting label on expanding interior domains extends to the closed
cell. Only pointwise eventual membership is needed for the exhaustion. -/
theorem affine_profile_limit_on_closed_cell
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (C : Set W) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hint : (interior C).Nonempty)
    (f : ℕ → C(V, Y)) (g : C(V, Y)) (hf : Filter.Tendsto f Filter.atTop (nhds g))
    (A : W →L[ℝ] Y) (b : ℕ → Y) (c : Y)
    (hb : Filter.Tendsto b Filter.atTop (nhds c))
    (haffine : ∀ z, q z ∈ interior C → ∀ᶠ n in Filter.atTop, f n z = A (q z) + b n) :
    ∀ z, q z ∈ C → g z = A (q z) + c := by
  apply affine_profile_on_closed_cell q hq hqsurj C hC hclosed hint g g.continuous A c
  intro z hz
  have hleft := (continuous_eval_const z).tendsto g |>.comp hf
  have hright := Filter.Tendsto.const_add (A (q z)) hb
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [haffine z hz] with n hn
  exact hn.symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DiagonalAffineCellProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine limits and retained cell mass on one diagonal -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An exhausting family of interior affine identities, convergent offsets,
and supported joint laws produce the actual common good sets needed by the
reflection-volume argument, including points over the boundary. -/
theorem exists_diagonal_affine_cell_profiles
    {V W N : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace N]
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (cell : Set W) (hconv : Convex ℝ cell) (hclosed : IsClosed cell)
    (hint : (interior cell).Nonempty)
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : ℕ → Set V) (hK : ∀ j, IsCompact (K j))
    (hcover : ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, C ⊆ K j)
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (μ : Measure N) (Q : ℕ → ℕ → Set N)
    (hQ : ∀ j n, MeasurableSet (Q j n))
    (hQ0 : ∀ j n, μ (Q j n) ≠ 0) (hQfin : ∀ j n, μ (Q j n) ≠ ∞)
    (profile : ℕ → ℕ → N → S × S) (hp : ∀ j n, Measurable (profile j n))
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q j n) (hQ0 j n) (hQfin j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g))
    (A₁ A₂ : W →L[ℝ] W) (b₁ b₂ : ℕ → W)
    (haff₁ : ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, (f j).1.val z = A₁ (q z) + b₁ j)
    (haff₂ : ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, (f j).2.val z = A₂ (q z) + b₂ j)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (c₁ c₂ : W) (u n : ℕ → ℕ) (Good : ℕ → Set N),
      Tendsto u atTop atTop ∧ (∀ j, P (u j) (n j)) ∧
      Tendsto (fun j => scale (u j) (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (Good j)) ∧ (∀ j, Good j ⊆ Q (u j) (n j)) ∧
      (∀ j, 0 < (μ (Good j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
        (fun j => (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal) ∧
      ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, ∀ x ∈ Good j, ∀ z ∈ C,
        q z ∈ cell →
        ‖(profile (u j) (n j) x).1.val z - (A₁ (q z) + c₁)‖ ≤ 2 / ((j : ℝ) + 1) ∧
        ‖(profile (u j) (n j) x).2.val z - (A₂ (q z) + c₂)‖ ≤ 2 / ((j : ℝ) + 1) := by
  have hlim₁ : Tendsto (fun j => (f j).1.val) atTop (𝓝 g.1.val) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto g).comp hfg
  have hlim₂ : Tendsto (fun j => (f j).2.val) atTop (𝓝 g.2.val) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto g).comp hfg
  obtain ⟨w₀, hw₀⟩ := hint
  obtain ⟨z₀, hz₀⟩ := hqsurj w₀
  let c₁ := g.1.val z₀ - A₁ (q z₀)
  let c₂ := g.2.val z₀ - A₂ (q z₀)
  have hb₁ : Tendsto b₁ atTop (𝓝 c₁) :=
    affine_offset_tendsto _ _ hlim₁ z₀ (A₁ (q z₀)) b₁ (haff₁ z₀ (hz₀ ▸ hw₀))
  have hb₂ : Tendsto b₂ atTop (𝓝 c₂) :=
    affine_offset_tendsto _ _ hlim₂ z₀ (A₂ (q z₀)) b₂ (haff₂ z₀ (hz₀ ▸ hw₀))
  have hg₁ := affine_profile_limit_on_closed_cell q hq hqsurj cell hconv hclosed ⟨w₀, hw₀⟩
    (fun j => (f j).1.val) g.1.val hlim₁ A₁ b₁ c₁ hb₁ haff₁
  have hg₂ := affine_profile_limit_on_closed_cell q hq hqsurj cell hconv hclosed ⟨w₀, hw₀⟩
    (fun j => (f j).2.val) g.2.val hlim₂ A₂ b₂ c₂ hb₂ haff₂
  obtain ⟨u, n, Good, hu, hn, hr, hGood, hGoodQ, hGoodpos, hmass, happ⟩ :=
    exists_diagonal_good_cell_profile_pairs S K hK hcover scale hs μ Q hQ hQ0 hQfin
      profile hp ν hν f g hf hfg P hP
  refine ⟨c₁, c₂, u, n, Good, hu, hn, hr, hGood, hGoodQ, hGoodpos, hmass, ?_⟩
  intro C hC
  filter_upwards [happ C hC] with j hj
  intro x hx z hz hcell
  simpa only [hg₁ z hcell, hg₂ z hcell] using
    And.intro (hj x hx z hz).1.le (hj x hx z hz).2.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteModeProfileChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generator choices in the independent profile chains -/

noncomputable section
namespace PolycyclicRecognition

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

/-- Along a further increasing subsequence a finite generator index is
constant. This leaves an already converging profile law unchanged. -/
theorem exists_constant_mode_subsequence {I : Type} [Finite I] (mode : ℕ → I) :
    ∃ i : I, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, mode (φ n) = i := by
  have he : ∃ i : I, ∃ᶠ n in atTop, mode n = i := by
    by_contra h
    push Not at h
    have hall : ∀ᶠ n in atTop, ∀ i, mode n ≠ i := eventually_all.mpr h
    obtain ⟨n, hn⟩ := hall.exists
    exact hn (mode n) rfl
  obtain ⟨i, hi⟩ := he
  obtain ⟨φ, hφ, hconst⟩ := extraction_of_frequently_atTop hi
  exact ⟨i, φ, hφ, hconst⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SublinearSheetLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear sheet distance forces equality of limiting profiles -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

variable {G W Z : Type} [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- This compares the actual two suffixes with the same center and chart.
Only their source distance at the chosen chart point must be sublinear. -/
theorem rescaled_profile_limits_eq_of_sublinear_sheet_distance
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (x k l : ℕ → G) (chart : ℕ → Z → G) (z : ℕ → Z) (f g : W)
    (hf : Tendsto (fun n => rescaledMapProfile (J n) (x n) (k n)
      (Real.log (scale n)) (chart n) (z n)) atTop (𝓝 f))
    (hg : Tendsto (fun n => rescaledMapProfile (J n) (x n) (l n)
      (Real.log (scale n)) (chart n) (z n)) atTop (𝓝 g))
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      dist (x n * k n * chart n (z n)) (x n * l n * chart n (z n)) ≤ ε * scale n) :
    f = g := by
  have hb (ε : ℝ) (hε : 0 < ε) : dist f g ≤ (K : ℝ) * ε := by
    apply le_of_tendsto (hf.dist hg)
    filter_upwards [hnear ε hε] with n hn
    have he : dist
        (rescaledMapProfile (J n) (x n) (k n) (Real.log (scale n)) (chart n) (z n))
        (rescaledMapProfile (J n) (x n) (l n) (Real.log (scale n)) (chart n) (z n)) =
        (scale n)⁻¹ * dist (J n (x n * k n * chart n (z n)))
          (J n (x n * l n * chart n (z n))) := by
      simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
        sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv,
        Real.exp_log (hscale n), abs_of_pos (hscale n)]
    rw [he]
    calc
      _ ≤ (scale n)⁻¹ * ((K : ℝ) *
          dist (x n * k n * chart n (z n)) (x n * l n * chart n (z n))) :=
        mul_le_mul_of_nonneg_left ((hJ n).dist_le_mul _ _) (inv_nonneg.mpr (hscale n).le)
      _ ≤ (scale n)⁻¹ * ((K : ℝ) * (ε * scale n)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn K.coe_nonneg)
          (inv_nonneg.mpr (hscale n).le)
      _ = (K : ℝ) * ε := by field_simp [(hscale n).ne']
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hh := hb (ε / ((K : ℝ) + 1)) (div_pos hε hden)
  have hquot : (K : ℝ) * (ε / ((K : ℝ) + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  simpa only [zero_add] using hh.trans hquot

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GoodSheetProfileAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good sets suffice to compare the limiting values on two sheets -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology NNReal

/-- A good set may have vanishing relative probability. Its nonemptiness,
vanishing profile errors, and the actual short source bridge still identify
the two limiting profile values. -/
theorem good_sheet_profile_values_eq
    {G W Z A : Type} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (x : ℕ → G) (k l : ℕ → A → G) (chart : ℕ → Z → G) (z : Z)
    (Good : ℕ → Set A) (hne : ∀ n, (Good n).Nonempty)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (f g : W)
    (happrox : ∀ᶠ n in atTop, ∀ a ∈ Good n,
      ‖rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n)) (chart n) z - f‖ ≤ ε n ∧
      ‖rescaledMapProfile (J n) (x n) (l n a) (Real.log (scale n)) (chart n) z - g‖ ≤ ε n)
    (hnear : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ a ∈ Good n,
      dist (x n * k n a * chart n z) (x n * l n a * chart n z) ≤ η * scale n) : f = g := by
  choose a ha using hne
  have hf : Tendsto (fun n => rescaledMapProfile (J n) (x n) (k n (a n))
      (Real.log (scale n)) (chart n) z) atTop (𝓝 f) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [happrox, hε.eventually (gt_mem_nhds hη)] with n hn he
    exact (show dist _ f ≤ ε n from by simpa only [dist_eq_norm] using (hn (a n) (ha n)).1).trans_lt he
  have hg : Tendsto (fun n => rescaledMapProfile (J n) (x n) (l n (a n))
      (Real.log (scale n)) (chart n) z) atTop (𝓝 g) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [happrox, hε.eventually (gt_mem_nhds hη)] with n hn he
    exact (show dist _ g ≤ ε n from by simpa only [dist_eq_norm] using (hn (a n) (ha n)).2).trans_lt he
  exact rescaled_profile_limits_eq_of_sublinear_sheet_distance J hJ scale hscale x
    (fun n => k n (a n)) (fun n => l n (a n)) chart (fun _ => z) f g hf hg
    (fun η hη => (hnear η hη).mono fun n hn => hn (a n) (ha n))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceSectionTileVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The per-tile Haar exponent along the sampled profile scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise

theorem sequence_subexponential_exp_error
    {scale ε : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) :
    HasSubexponentialUpperBoundSeq scale (fun n => Real.exp (ε n * scale n)) := by
  intro η hη
  filter_upwards [hε.eventually (eventually_lt_nhds hη),
    hs.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hs
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn.le hs)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ShrinkingProfileDomains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The contracted profile domains exhaust the interior cell -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Inverse dilation of a fixed interior point remains in the cell when
its scalar tends to one. No boundary regularity is required. -/
theorem eventually_mem_shrinking_cell
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {cell : Set W} {w : W} (hw : w ∈ interior cell)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ) :
    ∀ᶠ j in atTop, w ∈ (fun v => (1 - c * δ j) • v) '' cell := by
  have ht : Tendsto (fun j => 1 - c * δ j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hδ.const_mul c)
  have hv : Tendsto (fun j => (1 - c * δ j)⁻¹ • w) atTop (𝓝 w) := by
    simpa only [inv_one, one_smul] using (ht.inv₀ one_ne_zero).smul
      (tendsto_const_nhds (x := w))
  filter_upwards [hv.eventually (mem_interior_iff_mem_nhds.mp hw),
    ht.eventually_ne one_ne_zero] with j hj hn
  exact ⟨(1 - c * δ j)⁻¹ • w, hj, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hn, one_smul]⟩

/-- The same exhaustion holds when each row is known affine only on the
open contracted cell, as in the local affinity theorem. -/
theorem eventually_affine_of_shrinking_interiors
    {V W Y : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Add Y] (q : V → W) (cell : Set W) (f : ℕ → V → Y)
    (A : W → Y) (b : ℕ → Y) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ)
    (haff : ∀ j z, q z ∈ (fun w => (1 - c * δ j) • w) '' interior cell →
      f j z = A (q z) + b j) :
    ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, f j z = A (q z) + b j := by
  intro z hz
  have hz' : q z ∈ interior (interior cell) := by simpa only [interior_interior] using hz
  exact (eventually_mem_shrinking_cell hz' hδ c).mono (fun j hj => haff j z hj)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordBoxComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing boxes with varying maximizing word bases

Only the target basis needs to maximize its costs. A small change in the
costs of the finite word list introduces exactly its exponential error.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- Vanishing errors in the costs and subexponential box radii admit one
subexponential envelope in a single fixed maximizing basis. -/
theorem exists_sequence_word_box_envelope
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (cost : S → ℝ) (β : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val)
    (scale ε R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hε : Tendsto ε atTop (𝓝 0))
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (newCost : S → ℝ) (γ : WordBasisSelections X S),
        (∀ w, newCost w ≤ cost w + ε n) → ∀ v : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
          (fun j => newCost (γ.val j)) (scale n)).equivFun v‖ ≤ R n →
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) (scale n)).equivFun v‖ ≤ V n := by
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant X S b₀
  let V := fun n => D * Real.exp (ε n * scale n) * R n
  have hV : HasSubexponentialUpperBoundSeq scale V :=
    ((sequence_subexponential_upper_const hscale D).mul
      (sequence_subexponential_exp_error hscale hε) (Eventually.of_forall (fun _ => hD))).mul
      hR (Eventually.of_forall (fun n => mul_nonneg hD (Real.exp_pos _).le))
  refine ⟨V, fun n => mul_nonneg (mul_nonneg hD (Real.exp_pos _).le) (hR0 n), hV, ?_⟩
  intro n newCost γ hc v hv
  exact (hcompare cost newCost β γ hβ (hscale0 n) hc v).trans
    (mul_le_mul_of_nonneg_left hv (mul_nonneg hD (Real.exp_pos _).le))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WordChartHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact height scaling in nilpotent word charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A linear height that kills brackets scales exactly in the word-length
chart. This is independent of a choice of graded limit: all nontrivial
bracket words have zero height, while each letter has weight one. -/
theorem word_length_chart_height
    {I L W : Type} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hbracket : ∀ x y : L, h ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 0 < r) (z : Fin (finrank ℝ L) → ℝ) :
    h ((exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)).equivFun.symm z) =
      r • h ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
  have hb (j : Fin (finrank ℝ L)) : h (br j) = r • h (b j) := by
    simp only [br, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, map_smul]
    have he := WordBasisSelections.eval_words X S β j
    change evalBracketWord X (β.val j) = b j at he
    rw [← he]
    cases hw : (β.val j : FreeMagma I) with
    | of i => simp only [bracketWordLength, Nat.cast_one, mul_one, Real.exp_log hr]
    | mul u v =>
        change Real.exp (Real.log r * (bracketWordLength (u * v) : ℝ)) •
          h ⁅evalBracketWord X u, evalBracketWord X v⁆ =
            r • h ⁅evalBracketWord X u, evalBracketWord X v⁆
        rw [hbracket, smul_zero, smul_zero]
  change h (br.equivFun.symm z) = r • h (b.equivFun.symm z)
  rw [Basis.equivFun_symm_apply, map_sum, Basis.equivFun_symm_apply, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, hb, smul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartPivot
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial size and exact height of a scaled word-chart pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- The pivot logarithm has one fixed polynomial envelope in the physical
scale, for the actual fixed word chart and coordinate. -/
theorem wordChartPivot_polynomial_bound {L I : Type} [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (z : Fin (finrank ℝ L) → ℝ) :
    ∃ A : ℝ, ∃ p : ℕ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      ‖b₀.equivFun (wordChartPivot X S β r z)‖ ≤ A * (1 + r) ^ p := by
  let b := WordBasisSelections.basis X S β
  let p := ∑ j, bracketWordLength (β.val j : FreeMagma I)
  let A := (∑ j, ‖b₀.equivFun (b j)‖) * ‖z‖
  refine ⟨A, p, by dsimp [A] <;> positivity, ?_⟩
  intro r hr
  have hh := norm_polynomial_chart_log_le b b₀
    (fun j => bracketWordLength (β.val j : FreeMagma I)) p
    (fun j => by
      dsimp only [p]
      exact Finset.single_le_sum (f := fun j => bracketWordLength (β.val j : FreeMagma I)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hr z
  simpa only [wordChartPivot, bracketWordExponent_one, max_eq_left (Real.log_nonneg hr)] using hh

/-- The pivot's height is exactly linear in physical scale. -/
theorem wordChartPivot_height {L W I : Type} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 1 ≤ r) (z : Fin (finrank ℝ L) → ℝ) :
    h (wordChartPivot X S β r z) =
      r • h ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  simpa only [wordChartPivot, bracketWordExponent_one, max_eq_left (Real.log_nonneg hr)] using
    word_length_chart_height X S β h hh (lt_of_lt_of_le zero_lt_one hr) z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGoodFacetAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contact-facet equality for the diagonal's nonempty good sheets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G W A I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
include T in
/-- At a facet, even good sets of vanishing relative mass force equality of
the two limiting affine values. Their nonemptiness suffices for this step. -/
theorem good_word_profiles_agree_on_facet
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (words : Finset (FreeMagma I)) (β : WordBasisSelections X words)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale R η t : ℕ → ℝ)
    (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp
      ((M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z) + η n) * scale n))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (x : ℕ → G) (k : ℕ → A → G)
    (Good : ℕ → Set A) (hne : ∀ n, (Good n).Nonempty)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (f g : W)
    (happrox : ∀ᶠ n in atTop, ∀ a ∈ Good n,
      ‖rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n))
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z - f‖ ≤ ε n ∧
      ‖rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (Real.log (scale n)) (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z - g‖ ≤ ε n) :
    f = g := by
  obtain ⟨B, d, hB, hpos⟩ := wordChartPivot_polynomial_bound X words β (finBasis ℝ H) z
  let RH := fun n => (B + 1) * (1 + scale n) ^ d
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale1 n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < B + 1) d).along_sequence hscale
  have hq n : ‖(finBasis ℝ H).equivFun (wordChartPivot X words β (scale n) z)‖ ≤ RH n :=
    (hpos _ (hscale1 n)).trans (by
      dsimp only [RH]
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg (by linarith [hscale1 n]) _))
  let χ : H →ₗ[ℝ] ℝ := (cartanHeightWeight T H (M.weight i)).comp
    ((heightProjection T.character).comp H.subtype)
  have hχ (h : H) : χ h = M.weight i h := cartanHeightWeight_projection T H (M.weight i) h
  have hbr (h k : H) : χ ⁅h, k⁆ = 0 := by
    change cartanHeightWeight T H (M.weight i)
      (heightProjection T.character (⁅h, k⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, T.height_lie, map_zero]
  have hfacet n : M.weight i (wordChartPivot X words β (scale n) z) =
      M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z) * scale n := by
    simpa only [hχ, smul_eq_mul, mul_comm] using
      wordChartPivot_height X words β χ hbr (hscale1 n) z
  apply good_sheet_profile_values_eq J hJ scale
    (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) x k
    (fun n a => k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (fun n v => Exp (wordChartPivot X words β (scale n) v : H)) z Good hne ε hε f g happrox
  intro τ hτ
  filter_upwards [facet_root_switch_sublinear T H (M.weight i) (M.weight_nonzero i)
    Exp hExp realize ⟨M.letter i, M.letter_root i⟩ scale RH R η
    (M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z))
    hscale (fun n => le_trans zero_le_one (hscale1 n)) hRH0 hR0 hRH hR hη τ hτ] with n hn
  intro a _
  simpa only [mul_assoc] using hn (x n * k n a)
    (wordChartPivot X words β (scale n) z) (t n) (hq n) (hfacet n) (ht n)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGoodRootNeighborLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-neighbor label equality from the diagonal's retained good sets

The relative Haar mass may decay subexponentially. No positive limiting
fraction or supported point of the full sampling law is required.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type} [Fintype J]

set_option maxHeartbeats 1000000 in
theorem good_root_neighbor_labels_eq
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ cell)
    (i : Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ j, α j (eW (heightProjection T.character pivot)) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (offset₁ offset₂ : W)
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (R : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier) (η t : ℕ → ℝ)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((M.weight i pivot + η n) * scale n))
    (hstep : ∀ n, F.inclusionN (k n) =
      ExpG (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hgood : ∀ Q : Set (Fin (finrank ℝ H) → ℝ), IsCompact Q →
      ∃ (Good : ℕ → Set F.N.carrier) (ε : ℕ → ℝ),
        (∀ n, MeasurableSet (Good n)) ∧
        (∀ n, Good n ⊆ (fun y => y * k₀ n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1) ∧
        (∀ n, 0 < ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
          (Good n)).toReal) ∧
        HasSubexponentialLowerBoundSeq scale (fun n =>
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal /
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
            ((fun y => y * k₀ n) '' M.groupBox T hunimod eW
              (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)).toReal) ∧
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := fun n => exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
          ((heightProjection T.character).comp H.incl.toLinearMap)
        ∀ᶠ n in atTop, ∀ q ∈ Good n, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ cell →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN q) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₁.val (height (b.equivFun.symm z)) + offset₁)‖ ≤ ε n ∧
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n)) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₂.val (height (b.equivFun.symm z)) + offset₂)‖ ≤ ε n) : A₁ = A₂ := by
  classical
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let ℓ := (M.supportIn T hunimod eW).weight i
  have hweight (v : H) : ℓ (height v) = M.weight i v := by
    change cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) = _
    rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  have hℓ : ℓ ≠ 0 := by
    intro hzero
    apply M.weight_nonzero i
    funext v
    change M.weight i v = 0
    have hz := congrArg (fun f : W →ₗ[ℝ] ℝ => f (height v)) hzero
    simpa only [hweight, LinearMap.zero_apply] using hz
  have hpoint : ∀ j, α j (height pivot) ≤ c j := by
    have hp : height pivot ∈ cell := hpivot
    rw [hpoly] at hp
    exact hp
  obtain ⟨ρ, hρ, hlocal⟩ := exists_relative_facet_neighborhood α c (height pivot) ℓ hpoint hactive
  obtain ⟨δ, hδ0, hδ, hbridge⟩ := exists_facet_pivot_bridge_rate T H (M.weight i)
    (M.weight_nonzero i) ExpG hExpG realize ⟨M.letter i, M.letter_root i⟩ pivot
    scale R η t hscale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) hR0 hR hη ht
  have hagree : ∀ w, ℓ w = ℓ (height pivot) → ‖w - height pivot‖ < ρ →
      A₁.val w + offset₁ = A₂.val w + offset₂ := by
    intro w hw hn
    let v := cartanHeightSection T H (eW.symm w)
    let z := b.equivFun v
    have hz : height (b.equivFun.symm z) = w := by
      change eW (heightProjection T.character
        (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
      simp only [z, LinearEquiv.symm_apply_apply, v,
        cartanHeightSection_height, eW.apply_symm_apply]
    have hz' : (eW.toLinearMap.comp
        ((heightProjection T.character).comp H.incl.toLinearMap))
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z) = w := hz
    have hwcell : w ∈ cell := by rw [hpoly]; exact hlocal w hw hn
    have hwt : M.weight i (b.equivFun.symm z) = M.weight i pivot := by
      rw [← hweight, hz, hw, hweight]
    obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ :=
      hgood {z} isCompact_singleton
    have hne n : (Good n).Nonempty := by
      by_contra hn
      have he : Good n = ∅ := not_nonempty_iff_eq_empty.mp hn
      simpa only [he, measure_empty, ENNReal.toReal_zero, lt_self_iff_false] using hGoodpos n
    have hsame := M.good_word_profiles_agree_on_facet T ExpG hExpG realize X
      (boundedBracketWords d) βD z i scale R η t hscale hscale1 hR0 hR hη
      (by
        change ∀ n, |t n| ≤ R n * Real.exp ((M.weight i (b.equivFun.symm z) + η n) * scale n)
        simpa only [hwt] using ht)
      (fun n g => (π ((p n).val.1 g)).toAdd)
      (fun n => hLip.comp (p n).property.1.1) x (fun _ q => F.inclusionN q)
      Good hne ε hε (A₁.val w + offset₁) (A₂.val w + offset₂) ?_
    · exact hsame
    · filter_upwards [happ] with n hn
      intro q hq
      have hb := hn q hq z (mem_singleton z) (hz ▸ hwcell)
      simpa only [map_mul, hstep, hz', wordChartPivot,
        max_eq_left (Real.log_nonneg (hscale1 n))] using hb
  apply affine_labels_eq_of_template_comparison (M.supportIn T hunimod eW) A₁ A₂ ℓ hℓ
    offset₁ offset₂ (height pivot) α c hpoint hactive hρ hagree
  intro E hE hEconv hEcell hpE
  have hEcell' : E ⊆ cell := by simpa only [hpoly] using hEcell
  apply M.good_affine_templates_support_le_m T F hunimod eW hExpG hinjG realize rem π hLip
    hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    E cell hE hEconv hcell hEcell' pivot hpE A₁ A₂ offset₁ offset₂ βcell hβcell X hDnil
    bD₀ βD hβD aN hm hdim scale hscale hscale1 ν hpath hΛ p x R k₀ k δ hR0 hR hk₀ hk
    hδ0 hδ (Eventually.of_forall (fun n => by
      simpa only [one_mul, hstep] using hbridge n 1))
  intro Q hQ
  obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ := hgood Q hQ
  refine ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, ?_⟩
  filter_upwards [happ] with n hn
  intro q hq z hz hze
  exact hn q hq z hz (hEcell' hze)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanShrinkingBoxEnvelope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing vanishing homothetic enlargements into the box radius -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Topology

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The diagonal's shrinking enlargement changes only a subexponential
radius in one fixed maximizing box. The enlarged basis may vary with scale. -/
theorem exists_homothetic_box_envelope_sequence {N : Type}
    (Exp : cartanRootIdeal H → N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale δ R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (γ : M.Bases),
        M.groupBox T hunimod eW Exp ((fun w => (1 + δ n) • w) '' E) γ (scale n) (R n) ⊆
          M.groupBox T hunimod eW Exp E β (scale n) (V n) := by
  let C := ∑ w : M.wordList, |M.boxCost T hunimod eW E w|
  have hC w : M.boxCost T hunimod eW E w ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w : M.wordList => |M.boxCost T hunimod eW E w|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))
  have heps : Tendsto (fun n => δ n * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hδ.mul_const C
  obtain ⟨V, hV0, hV, hv⟩ := exists_sequence_word_box_envelope M.letter M.wordList b₀
    (M.boxCost T hunimod eW E) β hβ scale (fun n => δ n * C) R hscale hscale0 heps hR0 hR
  refine ⟨V, hV0, hV, ?_⟩
  intro n γ x hx
  obtain ⟨v, he, hb⟩ := hx
  refine ⟨v, he, hv n _ γ ?_ v hb⟩
  intro w
  rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith [hδ0 n])]
  nlinarith [mul_le_mul_of_nonneg_left (hC w) (hδ0 n)]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDiagonalNeighborLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One geometric diagonal for shrinking neighboring sheets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type} [Fintype J]

set_option maxHeartbeats 1000000 in
/-- Supported affine labels along shrinking enlargements agree. The proof
selects the actual Haar cells, their subexponential mass and all geometric
bounds on one diagonal before applying the reflection comparison. -/
theorem diagonal_root_neighbor_labels_eq
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
    (hint : (interior cell).Nonempty)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ cell)
    (i : Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ j, α j (eW (heightProjection T.character pivot)) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW))
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℕ → ℝ) (hscale : ∀ j, Tendsto (scale j) atTop atTop)
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (p : ℕ → ℕ → NormalizedPair G Λ) (x : ℕ → ℕ → G)
    (R : ℕ → ℕ → ℝ) (k₀ k : ℕ → ℕ → F.N.carrier) (η δ : ℕ → ℝ)
    (t : ℕ → ℕ → ℝ) (β : ℕ → ℕ → M.Bases)
    (hR0 : ∀ j n, 0 ≤ R j n)
    (hR : ∀ j, HasSubexponentialUpperBoundSeq (scale j) (R j))
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (hk₀ : ∀ j n, k₀ j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hk : ∀ j n, k j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight i pivot + η j) * scale j n))
    (hstep : ∀ j n, F.inclusionN (k j n) =
      ExpG (t j n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (profile : ℕ → ℕ → F.N.carrier → S × S) (hp : ∀ j n, Measurable (profile j n))
    (hactual : ∀ j n q, q ∈ (fun y => y * k₀ j n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1 → ∀ z,
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale j n))
      (profile j n q).1.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN q)
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
      (profile j n q).2.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN (q * k j n))
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z)
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (scale j n) (k₀ j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g)) (b₁ b₂ : ℕ → W) (shrink : ℝ)
    (haff₁ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = A₁.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
    (haff₂ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = A₂.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : A₁ = A₂ := by
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let q := height.comp b.equivFun.symm.toLinearMap
  have hq : Function.Surjective q := by
    intro w
    refine ⟨b.equivFun (cartanHeightSection T H (eW.symm w)), ?_⟩
    change eW (heightProjection T.character
      (b.equivFun.symm (b.equivFun (cartanHeightSection T H (eW.symm w))) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
    rw [LinearEquiv.symm_apply_apply, cartanHeightSection_height, eW.apply_symm_apply]
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let Q := fun j n => (fun y => y * k₀ j n) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1
  have hQ j n : MeasurableSet (Q j n) ∧ μ (Q j n) ≠ 0 ∧ μ (Q j n) ≠ ∞ :=
    M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀
      cell βcell (scale j n) (k₀ j n)
  let P := fun j n => 1 ≤ scale j n ∧
    R j n ≤ Real.exp ((1 / ((j : ℝ) + 1)) * scale j n)
  have hP j : ∀ᶠ n in atTop, P j n :=
    ((hscale j).eventually (eventually_ge_atTop (1 : ℝ))).and
      (hR j (1 / ((j : ℝ) + 1)) (by positivity))
  obtain ⟨c₁, c₂, u, n, Good, hu, hn, hs, hGood, hGoodQ, hGoodpos, hmass, happ⟩ :=
    exists_diagonal_affine_cell_profiles q q.continuous_of_finiteDimensional hq
      cell hconv hcell.isClosed hint S
      (fun j => Metric.closedBall 0 ((j : ℝ) + 1)) (fun _ => isCompact_closedBall _ _)
      (fun C hC => compact_eventually_subset_coordinate_balls 0 C hC)
      scale hscale μ Q (fun j n => (hQ j n).1) (fun j n => (hQ j n).2.1)
      (fun j n => (hQ j n).2.2) profile hp ν hν f g hf hfg
      A₁.val.toLinearMap.toContinuousLinearMap A₂.val.toLinearMap.toContinuousLinearMap
      b₁ b₂
      (eventually_affine_of_shrinking_interiors q cell (fun j z => (f j).1.val z)
        A₁.val b₁ hδ shrink haff₁)
      (eventually_affine_of_shrinking_interiors q cell (fun j z => (f j).2.val z)
        A₂.val b₂ hδ shrink haff₂) P hP
  let r := fun j => scale (u j) (n j)
  let R' := fun j => R (u j) (n j)
  have hr1 j : 1 ≤ r j := (hn j).1
  have hr0 j : 0 ≤ r j := zero_le_one.trans (hr1 j)
  have hR' : HasSubexponentialUpperBoundSeq r R' := by
    intro ε hε
    filter_upwards [sequence_subexponential_exp_of_vanishing_rate hr0
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hu) ε hε] with j hj
    exact (hn j).2.trans hj
  obtain ⟨V, hV0, hV, hbox⟩ := M.exists_homothetic_box_envelope_sequence T hunimod eW
    (F.ExpN ∘ F.N.equiv) b₀ hcell (hint.mono interior_subset) βcell hβcell
    r (δ ∘ u) R' hs hr0 (fun j => hδ0 (u j)) (hδ.comp hu)
    (fun j => hR0 (u j) (n j)) hR'
  let R'' := fun j => V j + R' j
  have hR''0 j : 0 ≤ R'' j := add_nonneg (hV0 j) (hR0 (u j) (n j))
  have hR'' : HasSubexponentialUpperBoundSeq r R'' := hV.add hR' hs
  have hbox' j γ :
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ (u j)) • w) '' cell) γ (r j) (R' j) ⊆
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (r j) (R'' j) := by
    intro v hv
    obtain ⟨a, ha, he⟩ := hbox j γ hv
    exact ⟨a, ha, he.trans (le_add_of_nonneg_right (hR0 (u j) (n j)))⟩
  apply M.good_root_neighbor_labels_eq T F hunimod eW hExpG hinjG realize rem π hLip hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell pivot hpivot i α c hpoly hactive A₁ A₂ c₁ c₂ βcell hβcell X hDnil bD₀ βD hβD
    aN hm hdim r hs hr1 νD hpath hΛ
    (fun j => p (u j) (n j)) (fun j => x (u j) (n j)) R''
    (fun j => k₀ (u j) (n j)) (fun j => k (u j) (n j)) (η ∘ u)
    (fun j => t (u j) (n j)) hR''0 hR''
    (fun j => hbox' j _ (hk₀ (u j) (n j))) (fun j => hbox' j _ (hk (u j) (n j)))
    (hη.comp hu) (fun j => (ht (u j) (n j)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hV0 j)) (Real.exp_pos _).le))
    (fun j => hstep (u j) (n j))
  intro C hC
  refine ⟨Good, fun j => 2 / ((j : ℝ) + 1), hGood, hGoodQ, hGoodpos, hmass,
    fun _ => by positivity, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
  · filter_upwards [happ C hC] with j hj
    intro a ha z hz hze
    have hraw := hactual (u j) (n j) a (hGoodQ j ha) z
    simpa only [hraw.1, hraw.2, r, q, height, b, LinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe] using hj a ha z hz hze

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanEventualNeighborLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eventual agreement for shrinking-enlargement families -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type} [Fintype J]

set_option maxHeartbeats 1000000 in
/-- Along any shrinking-enlargement family, supported neighboring affine
labels agree eventually. Compactness and the finite symmetry group supply
the converging constant-label subsequence required by the geometric diagonal. -/
theorem eventually_root_neighbor_labels_eq_m_oai
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
    (hint : (interior cell).Nonempty)
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ cell)
    (mode : ℕ → Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : ℕ → templateSymmetryGroup (M.supportIn T hunimod eW))
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℕ → ℝ) (hscale : ∀ j, Tendsto (scale j) atTop atTop)
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (p : ℕ → ℕ → NormalizedPair G Λ) (x : ℕ → ℕ → G)
    (R : ℕ → ℕ → ℝ) (k₀ k : ℕ → ℕ → F.N.carrier) (η δ : ℕ → ℝ)
    (t : ℕ → ℕ → ℝ) (β : ℕ → ℕ → M.Bases)
    (hR0 : ∀ j n, 0 ≤ R j n)
    (hR : ∀ j, HasSubexponentialUpperBoundSeq (scale j) (R j))
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (hk₀ : ∀ j n, k₀ j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hk : ∀ j n, k j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight (mode j) (pivot (mode j)) + η j) * scale j n))
    (hstep : ∀ j n, F.inclusionN (k j n) =
      ExpG (t j n • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (profile : ℕ → ℕ → F.N.carrier → S × S) (hp : ∀ j n, Measurable (profile j n))
    (hactual : ∀ j n q, q ∈ (fun y => y * k₀ j n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1 → ∀ z,
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale j n))
      (profile j n q).1.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN q)
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
      (profile j n q).2.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN (q * k j n))
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z)
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (scale j n) (k₀ j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support) (b₁ b₂ : ℕ → W) (shrink : ℝ)
    (haff₁ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = (A₁ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
    (haff₂ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = (A₂ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : (∀ᶠ j in atTop, A₁ j = A₂ j) := by
  classical
  by_contra h
  have hbad : ∃ᶠ j in atTop, A₁ j ≠ A₂ j := not_eventually.mp h
  obtain ⟨v, hv, hvbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨ab, w, hw, hab⟩ := exists_constant_mode_subsequence (fun j => (mode (v j), A₁ (v j), A₂ (v j)))
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨g, u, hu, hfg⟩ := CompactSpace.tendsto_subseq (fun j => f (v (w j)))
  let a := v ∘ w ∘ u
  have ha : StrictMono a := hv.comp (hw.comp hu)
  have hlabels j : (mode (a j), A₁ (a j), A₂ (a j)) = ab := hab (u j)
  have hmode j : mode (a j) = ab.1 := congrArg Prod.fst (hlabels j)
  have hlabel₁ j : A₁ (a j) = ab.2.1 := congrArg (fun q => q.2.1) (hlabels j)
  have hlabel₂ j : A₂ (a j) = ab.2.2 := congrArg (fun q => q.2.2) (hlabels j)
  have hne : ab.2.1 ≠ ab.2.2 := by
    intro heq
    apply hvbad (w (u 0))
    change A₁ (a 0) = A₂ (a 0)
    rw [hlabel₁ 0, hlabel₂ 0]
    exact heq
  apply hne
  apply M.diagonal_root_neighbor_labels_eq T F hunimod eW hExpG hinjG realize rem π hLip hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell hconv hint (pivot ab.1) (hpivot ab.1) ab.1 α c hpoly (hactive ab.1)
    ab.2.1 ab.2.2 βcell hβcell
    X hDnil bD₀ βD hβD aN hm hdim (fun j => scale (a j)) (fun j => hscale (a j))
    νD hpath hΛ (fun j => p (a j)) (fun j => x (a j)) (fun j => R (a j))
    (fun j => k₀ (a j)) (fun j => k (a j)) (η ∘ a) (δ ∘ a)
    (fun j => t (a j)) (fun j => β (a j)) (fun j => hR0 (a j)) (fun j => hR (a j))
    (fun j => hδ0 (a j)) (hδ.comp ha.tendsto_atTop)
    (fun j => hk₀ (a j)) (fun j => hk (a j)) (hη.comp ha.tendsto_atTop)
    (by intro j n; simpa only [hmode j, Function.comp_apply] using ht (a j) n)
    (by intro j n; simpa only [hmode j, Function.comp_apply] using hstep (a j) n) S (fun j => profile (a j))
    (fun j => hp (a j)) (fun j => hactual (a j)) (ν ∘ a) (fun j => hν (a j)) (f ∘ a) g
    (fun j => hf (a j)) hfg (b₁ ∘ a) (b₂ ∘ a) shrink
  · intro j z hz
    simpa only [hlabel₁ j, Function.comp_apply] using haff₁ (a j) z hz
  · intro j z hz
    simpa only [hlabel₂ j, Function.comp_apply] using haff₂ (a j) z hz

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq_m_oai
