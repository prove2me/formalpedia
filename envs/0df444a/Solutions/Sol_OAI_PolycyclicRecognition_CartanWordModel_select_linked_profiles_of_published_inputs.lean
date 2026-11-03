-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:57:13.712512+00:00
-- url     : https://prove2.me/submissions/3519eb10-7379-4720-b4aa-36728112beee

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D013
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_cartan_independent_raw_chain_concentration

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem exists_slow_sequence_selection (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop, P (k n) n := by
  classical
  choose N hN using fun j => eventually_atTop.mp (hP j)
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun j => N j ≤ n) n
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (N j), eventually_ge_atTop j] with n hn hj
    exact Nat.le_findGreatest hj hn
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop (N 0)] with n hn
  exact hN (k n) n (Nat.findGreatest_spec (P := fun j => N j ≤ n)
    (n := n) (m := 0) (Nat.zero_le _) hn)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConditionedProbeSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping positive probe mass after conditioning the starting sample -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

/-- If joint failures occupy less than half the mass of the starting
profile event, some starting sample in that event retains at least half
of the independent probes. No conditioning on a singleton is used. -/
theorem exists_start_with_half_good_probes
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set X) (bad : Set (X × Y)) (hE : MeasurableSet E) (hbad : MeasurableSet bad)
    (hsmall : (μ.prod ν) bad < (1 / 2 : ℝ≥0∞) * μ E) :
    ∃ x ∈ E, (1 / 2 : ℝ≥0∞) ≤ ν {y | (x, y) ∉ bad} := by
  by_contra hnone
  push Not at hnone
  have hfiber (x : X) (hx : x ∈ E) :
      (1 / 2 : ℝ≥0∞) ≤ ν {y | (x, y) ∈ bad} := by
    by_contra hlt
    have hb : ν {y | (x, y) ∈ bad} < (1 / 2 : ℝ≥0∞) := lt_of_not_ge hlt
    have hs : MeasurableSet {y | (x, y) ∈ bad} :=
      (measurable_const.prodMk measurable_id) hbad
    have hh := ENNReal.add_lt_add hb (hnone x hx)
    change ν {y | (x, y) ∈ bad} + ν ({y | (x, y) ∈ bad}ᶜ) <
      (1 / 2 : ℝ≥0∞) + 1 / 2 at hh
    rw [prob_add_prob_compl hs] at hh
    rw [ENNReal.add_halves] at hh
    exact (lt_irrefl (1 : ℝ≥0∞)) hh
  have hbound : (1 / 2 : ℝ≥0∞) * μ E ≤ (μ.prod ν) bad := by
    rw [Measure.prod_apply hbad]
    calc
      _ = ∫⁻ x, E.indicator (fun _ => (1 / 2 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_indicator hE]
        simp
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ E
        · rw [indicator_of_mem hx]
          exact hfiber x hx
        · rw [indicator_of_notMem hx]
          exact zero_le
  exact (not_lt_of_ge hbound) hsmall

/-- Inner regularity retains a compact positive-volume probe set at that
same starting sample; the original starting-event probability is not lost. -/
theorem exists_start_with_compact_good_probes
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [ν.InnerRegular]
    (E : Set X) (bad : Set (X × Y)) (hE : MeasurableSet E) (hbad : MeasurableSet bad)
    (hsmall : (μ.prod ν) bad < (1 / 2 : ℝ≥0∞) * μ E) :
    ∃ x ∈ E, ∃ K : Set Y, IsCompact K ∧ K ⊆ {y | (x, y) ∉ bad} ∧
      (1 / 4 : ℝ≥0∞) < ν K := by
  obtain ⟨x, hx, hm⟩ := exists_start_with_half_good_probes μ ν E bad hE hbad hsmall
  have hgood : MeasurableSet {y | (x, y) ∉ bad} :=
    ((measurable_const.prodMk measurable_id) hbad).compl
  have hquarter : (1 / 4 : ℝ≥0∞) < 1 / 2 := by
    exact (ENNReal.div_lt_div_iff_right (by norm_num) (by simp)).mpr (by norm_num)
  obtain ⟨K, hK, hc, hmass⟩ := hgood.exists_lt_isCompact (hquarter.trans_le hm)
  exact ⟨x, hx, K, hc, hK, hmass⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConditionedProbeSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shrinking profile tolerances without losing probe volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The tolerance tends to zero by a slow diagonal choice. The starting
profile event may have very small mass; the retained independent probe
set still has measure greater than one quarter. -/
theorem eventually_exists_compact_conditioned_probes
    {X Y : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Y n)] [∀ n, TopologicalSpace (Y n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [∀ n, (ν n).InnerRegular]
    (E : ∀ n, ℕ → Set (X n)) (bad : ∀ n, ℕ → Set (X n × Y n))
    (hE : ∀ n j, MeasurableSet (E n j))
    (hbad : ∀ n j, MeasurableSet (bad n j))
    (hpos : ∀ j, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n in atTop, c ≤ μ n (E n j))
    (hlim : ∀ j, Tendsto (fun n => (μ n).prod (ν n) (bad n j)) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ x ∈ E n (k n), ∃ K : Set (Y n), IsCompact K ∧
        K ⊆ {y | (x, y) ∉ bad n (k n)} ∧ (1 / 4 : ℝ≥0∞) < ν n K := by
  have hsmall (j : ℕ) : ∀ᶠ n in atTop,
      (μ n).prod (ν n) (bad n j) < (1 / 2 : ℝ≥0∞) * μ n (E n j) := by
    obtain ⟨c, hc, he⟩ := hpos j
    have hh : (0 : ℝ≥0∞) < 1 / 2 * c := ENNReal.mul_pos (by norm_num) hc.ne'
    filter_upwards [(hlim j).eventually (gt_mem_nhds hh), he] with n hn hm
    apply hn.trans_le
    simpa only [mul_comm] using (mul_le_mul_right hm (1 / 2))
  obtain ⟨k, hk, hsmallk⟩ := exists_slow_sequence_selection _ hsmall
  refine ⟨k, hk, hsmallk.mono ?_⟩
  intro n hn
  exact exists_start_with_compact_good_probes (μ n) (ν n)
    (E n (k n)) (bad n (k n)) (hE n (k n)) (hbad n (k n)) hn

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProbeSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact good-probe sequences with harmless initial values -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Extend the eventual Fubini selection to sequences defined at every
scale. Initial exceptional scales use the full compact probability space;
the actual good-probe property is retained eventually. -/
theorem choose_compact_good_probe_sequence
    {X : Type} [Nonempty X] {Y : ℕ → Type}
    [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    (ν : ∀ n, ProbabilityMeasure (Y n)) (Good : ∀ n, X → Set (Y n) → Prop)
    (h : ∀ᶠ n in atTop, ∃ x K, IsCompact K ∧ Good n x K ∧
      (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K) :
    ∃ (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, Good n (x n) (K n) := by
  classical
  let success := fun n => ∃ x K, IsCompact K ∧ Good n x K ∧
    (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K
  have hall (n : ℕ) : ∃ x K, IsCompact K ∧
      (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K ∧ (success n → Good n x K) := by
    by_cases hn : success n
    · obtain ⟨x, K, hc, hg, hm⟩ := hn
      exact ⟨x, K, hc, hm, fun _ => hg⟩
    · refine ⟨Classical.choice ‹Nonempty X›, univ, isCompact_univ, ?_, ?_⟩
      · simp only [measure_univ]
        norm_num
      · exact fun hs => (hn hs).elim
  choose x K hc hm hg using hall
  refine ⟨x, K, fun n => ⟨hc n, (hc n).measurableSet, hm n⟩, ?_⟩
  filter_upwards [h] with n hn
  exact hg n hn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProductProbeSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint selection from product-measure concentration

Fubini selection retains a compact set of quarter mass satisfying the
product bounds for all three finite prefix families.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

theorem finite_dependent_bad_union_tendsto_zero
    {X : ℕ → Type} {J : Type} [∀ n, MeasurableSpace (X n)] [Fintype J]
    (μ : ∀ n, Measure (X n)) (bad : ∀ n, J → Set (X n))
    (hlim : ∀ j, Tendsto (fun n => μ n (bad n j)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (⋃ j, bad n j)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _
    (fun _ => zero_le) (fun n => measure_iUnion_fintype_le (μ n) (bad n))
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => hlim j)


theorem dependent_bad_distance_triangle_tendsto_zero
    {X : ℕ → Type} {S : Type} [∀ n, MeasurableSpace (X n)] [PseudoMetricSpace S]
    (μ : ∀ n, Measure (X n)) (f g h : ∀ n, X n → S)
    (hfg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hgh : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (g n x) (h n x)}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (h n x)}) atTop (𝓝 0) := by
  have hb (n : ℕ) : μ n {x | ε ≤ dist (f n x) (h n x)} ≤
      μ n {x | ε / 2 ≤ dist (f n x) (g n x)} +
        μ n {x | ε / 2 ≤ dist (g n x) (h n x)} := by
    apply (measure_mono (fun x hx => ?_)).trans (measure_union_le _ _)
    by_cases hf : ε / 2 ≤ dist (f n x) (g n x)
    · exact Or.inl hf
    · right
      have hh := dist_triangle (f n x) (g n x) (h n x)
      have hx' : ε ≤ dist (f n x) (h n x) := hx
      change ε / 2 ≤ dist (g n x) (h n x)
      linarith [lt_of_not_ge hf]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _ (fun _ => zero_le) hb
  simpa only [zero_add] using (hfg (ε / 2) (half_pos hε)).add (hgh (ε / 2) (half_pos hε))


theorem exists_compact_probes_from_supported_product_profiles
    {X S : Type} [MeasurableSpace X] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure S)
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 limitLaw))
    {f : S} (hf : f ∈ (limitLaw : Measure S).support)
    (U : ℕ → Set S) (hU : ∀ j, IsOpen (U j)) (hfU : ∀ j, f ∈ U j)
    (bad : ∀ n, ℕ → Set (X × Y n)) (hbad : ∀ n j, MeasurableSet (bad n j))
    (hproduct : ∀ j,
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n)) (bad n j))
        atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ x, profile n x ∈ U (k n) ∧ ∃ K : Set (Y n), IsCompact K ∧
        K ⊆ {y | (x, y) ∉ bad n (k n)} ∧ (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K := by
  have hpos (j : ℕ) : ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n in atTop,
      c ≤ (μ : Measure X) (profile n ⁻¹' U j) := by
    obtain ⟨c, hc, he⟩ := eventual_positive_mass_of_supported_weak_limit hlim hf (hU j) (hfU j)
    refine ⟨ENNReal.ofReal c, ENNReal.ofReal_pos.mpr hc, he.mono ?_⟩
    intro n hn
    rw [ProbabilityMeasure.map_apply' μ (hp n).aemeasurable (hU j).measurableSet] at hn
    exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))
  exact eventually_exists_compact_conditioned_probes
    (fun _ => (μ : Measure X)) (fun n => (ν n : Measure (Y n)))
    (fun n j => profile n ⁻¹' U j) bad (fun n j => hp n (hU j).measurableSet) hbad hpos
    hproduct

theorem exists_supported_product_chain_probe_sequence
    {X S C : Type} [Nonempty X] [MeasurableSpace X]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)] [Fintype C]
    {Y : ℕ → Type} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S × S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (S × S))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 limitLaw))
    {f : S × S} (hf : f ∈ (limitLaw : Measure (S × S)).support)
    (chain : ∀ n, X × Y n → C → S) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun q : X × Y n =>
      dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)))
    (hproduct : ∀ i (ε : ℝ), 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q i)
          (if sheet i then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop,
        x n ∈ carrying ∧ dist (profile n (x n)) f < ε n ∧
        ∀ y ∈ K n, ∀ i, dist (chain n (x n, y) i)
          (if sheet i then f.2 else f.1) < 2 * ε n := by
  classical
  let tol := fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)
  have htol (j : ℕ) : 0 < tol j := by dsimp [tol] <;> positivity
  let comparisons := fun n j => ⋃ i : C, {q : X × Y n | tol j ≤
    dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)}
  let bad := fun n j => Prod.fst ⁻¹' carryingᶜ ∪ comparisons n j
  have hcomparisons (n j) : MeasurableSet (comparisons n j) :=
    MeasurableSet.iUnion (fun i => (isClosed_le continuous_const continuous_id).measurableSet.preimage
      (hm n i))
  have hbad (n j) : MeasurableSet (bad n j) :=
    (measurable_fst hcarrying.compl).union (hcomparisons n j)
  have hproduct' (j : ℕ) :
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n)) (bad n j))
        atTop (𝓝 0) := by
    have hh := finite_dependent_bad_union_tendsto_zero
      (fun n => (μ : Measure X).prod (ν n : Measure (Y n)))
      (fun n i => {q | tol j ≤ dist (chain n q i)
        (if sheet i then (profile n q.1).2 else (profile n q.1).1)})
      (fun i => hproduct i (tol j) (htol j))
    have hzero (n : ℕ) : (μ : Measure X).prod (ν n : Measure (Y n))
        (Prod.fst ⁻¹' carryingᶜ) = 0 := by
      rw [show Prod.fst ⁻¹' carryingᶜ = carryingᶜ ×ˢ (univ : Set (Y n)) by
        ext x; simp]
      rw [Measure.prod_prod, hfull, zero_mul]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds hh (fun _ => zero_le)
    intro n
    exact (measure_union_le _ _).trans (by rw [hzero n, zero_add])
  obtain ⟨k, hk, hselect⟩ := exists_compact_probes_from_supported_product_profiles
    μ ν profile hp limitLaw hlim hf (fun j => ball f (tol j))
    (fun _ => isOpen_ball) (fun j => mem_ball_self (htol j)) bad hbad hproduct'
  let ε := fun n => tol (k n)
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  obtain ⟨x, K, hK, hgood⟩ := choose_compact_good_probe_sequence ν
    (fun n x K => dist (profile n x) f < ε n ∧ K ⊆ {y | (x, y) ∉ bad n (k n)})
    (hselect.mono (by
      intro n hn
      obtain ⟨x, hx, K, hc, hs, hm⟩ := hn
      exact ⟨x, K, hc, ⟨hx, hs⟩, hm⟩))
  refine ⟨ε, x, K, fun n => htol (k n), hε, hK, ?_⟩
  filter_upwards [hgood] with n hn
  have hnonempty : (K n).Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1 / 4).trans (hK n).2.2))
  have hcar : x n ∈ carrying := by
    obtain ⟨y, hy⟩ := hnonempty
    by_contra hx
    exact hn.2 hy (Or.inl hx)
  refine ⟨hcar, hn.1, ?_⟩
  intro y hy i
  have hb : dist (chain n (x n, y) i)
      (if sheet i then (profile n (x n)).2 else (profile n (x n)).1) < ε n := by
    apply lt_of_not_ge
    intro hge
    exact hn.2 hy (Or.inr (mem_iUnion.mpr ⟨i, hge⟩))
  have hp' : dist (if sheet i then (profile n (x n)).2 else (profile n (x n)).1)
      (if sheet i then f.2 else f.1) < ε n := by
    split_ifs
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hn.1
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hn.1
  exact (dist_triangle _ _ _).trans_lt (by linarith)

theorem exists_supported_product_affine_probe_sequence
    {X Z W V C : Type} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V] [Fintype C]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    {Y : ℕ → Type} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → C(Z, W) × C(Z, W)) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 limitLaw))
    {f : C(Z, W) × C(Z, W)} (hf : f ∈ (limitLaw : Measure (C(Z, W) × C(Z, W))).support)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : Bool → W)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    (chain : ∀ n, X × Y n → C → C(Z, W)) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun p : X × Y n =>
      dist (chain n p i) (if sheet i then (profile n p.1).2 else (profile n p.1).1)))
    (hproduct : ∀ i (ε : ℝ), 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q i)
          (if sheet i then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        ∀ y ∈ K n, ∀ i z,
          ‖chain n (x n, y) i z - (A (q z) + b (sheet i))‖ < 2 * ε n := by
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_product_chain_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf chain sheet hm hproduct
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  refine ⟨hn.1, ?_, ?_⟩
  · intro s z
    rw [← haffine s z, ← dist_eq_norm]
    apply (ContinuousMap.dist_apply_le_dist z).trans_lt
    have hdist : dist (if s then (profile n (x n)).2 else (profile n (x n)).1)
        (if s then f.2 else f.1) ≤ dist (profile n (x n)) f := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.dist_eq]
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact hdist.trans_lt hn.2.1
  · intro y hy i z
    rw [← haffine (sheet i) z, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist z).trans_lt (hn.2.2 y hy i)

theorem exists_supported_three_product_affine_probe_sequence
    {X Z W V : Type} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    {Y : ℕ → Type} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → C(Z, W) × C(Z, W)) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 limitLaw))
    {f : C(Z, W) × C(Z, W)} (hf : f ∈ (limitLaw : Measure (C(Z, W) × C(Z, W))).support)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : Bool → W)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    {N₀ N₁ N₂ : ℕ}
    (chain₀ : ∀ n, X × Y n → Fin (N₀ + 1) → C(Z, W))
    (chain₁ : ∀ n, X × Y n → Fin (N₁ + 1) → C(Z, W))
    (chain₂ : ∀ n, X × Y n → Fin (N₂ + 1) → C(Z, W))
    (hm₀ : ∀ n j, Measurable (fun p => chain₀ n p j))
    (hm₁ : ∀ n j, Measurable (fun p => chain₁ n p j))
    (hm₂ : ∀ n j, Measurable (fun p => chain₂ n p j))
    (hstart : ∀ n p, chain₂ n p 0 = chain₁ n p (Fin.last N₁))
    (hc₀ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₀ n q j) (profile n q.1).1}) atTop (𝓝 0))
    (hc₁ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₁ n q j) (profile n q.1).2}) atTop (𝓝 0))
    (hc₂ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₂ n q j) (chain₂ n q 0)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₀ n (x n, y) j z - (A (q z) + b false)‖ < 2 * ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₁ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n) ∧
        ∀ y ∈ K n, ∀ j z, ‖chain₂ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n := by
  let C := Fin (N₀ + 1) ⊕ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1))
  let chain : ∀ n, X × Y n → C → C(Z, W) := fun n p =>
    Sum.elim (chain₀ n p) (Sum.elim (chain₁ n p) (chain₂ n p))
  let sheet : C → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hm (n : ℕ) (j : C) : Measurable (fun p => dist (chain n p j)
      (if sheet j then (profile n p.1).2 else (profile n p.1).1)) := by
    rcases j with j | j | j
    · exact continuous_dist.measurable.comp
        ((hm₀ n j).prodMk (((hp n).fst).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₁ n j).prodMk (((hp n).snd).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₂ n j).prodMk (((hp n).snd).comp measurable_fst))
  have hc (j : C) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q j)
          (if sheet j then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0) := by
    rcases j with j | j | j
    · exact hc₀ j ε hε
    · exact hc₁ j ε hε
    · apply dependent_bad_distance_triangle_tendsto_zero
        (fun n => (μ : Measure X).prod (ν n : Measure (Y n)))
        (fun n q => chain₂ n q j)
        (fun n q => chain₁ n q (Fin.last N₁))
        (fun n q => (profile n q.1).2) _ (fun ε hε => hc₁ _ ε hε) ε hε
      intro δ hδ
      simpa only [hstart] using hc₂ j δ hδ
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_product_affine_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf q A b haffine chain sheet hm hc
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  exact ⟨hn.1, hn.2.1,
    fun y hy j z => hn.2.2 y hy (Sum.inl j) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inl j)) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inr j)) z⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualProbeProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable profiles of the sampled probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
/-- A Borel logarithmic prefix, including a tile-selected anchor, gives a
Borel actual profile under the independent product sampling law. -/
theorem CartanFactorModel.measurable_sampledProbeProfile
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (b₀ bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    {Y : Type} [MeasurableSpace Y] (v : Y → cartanRootIdeal H)
    (hv : Measurable (fun y => b₀.equivFun (v y))) :
    Measurable (fun p : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × Y =>
      F.sampledProbeProfile hD J hJ x r bN bD p.1 (v p.2)) := by
  let Ncoords : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → G :=
    fun z => F.inclusionN (F.ExpN (F.N.equiv (b₀.equivFun.symm z)))
  have hNc : Continuous Ncoords :=
    F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp b₀.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  have hNv : Measurable (fun y => F.inclusionN (F.ExpN (F.N.equiv (v y)))) := by
    have hm := hNc.measurable.comp hv
    change Measurable (fun y => F.inclusionN
      (F.ExpN (F.N.equiv (b₀.equivFun.symm (b₀.equivFun (v y)))))) at hm
    simpa only [LinearEquiv.symm_apply_apply] using hm
  have hsample : Continuous (fun y => F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y)))) :=
    F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp bN.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  simpa only [sampledProbeProfile, sampledProbeSuffix, map_mul, Function.comp_def, Pi.mul_apply] using
    (continuous_rescaledContinuousProfile J hJ x r
    (F.profileChart bD) (F.continuous_profileChart hD bD)).measurable.comp
      ((hsample.measurable.comp measurable_fst).mul (hNv.comp measurable_snd))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualChainConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of the actual sampled Cartan profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
/-- The actual profiles of a Borel logarithmic chain concentrate on its
initial profile under the independent probe law. No profile representative
or measurability premise is left to the application. -/
theorem cartan_actual_chain_concentration
    {K : ℕ → Type} [∀ n, MeasurableSpace (K n)] [∀ n, Nonempty (K n)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    {N : ℕ} (vertex : ∀ n, K n → Fin (N + 1) → cartanRootIdeal H)
    (hvertex : ∀ n q j,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (vertex n q j)‖ ≤ Real.exp (scale n * ε n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (hvertexMeas : ∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j)))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (mode : ∀ n, K n → Fin N → Fin M.letterCount)
    (t : ∀ n, K n → Fin N → ℝ) (s : Fin M.letterCount → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (htamp : ∀ j, ∀ᶠ n in atTop, ∀ q,
      |t n q j| ≤ B * Real.exp (scale n * (s (mode n q j) + ε n)))
    (hstep : ∀ n q j, F.inclusionN (F.ExpN (F.N.equiv (vertex n q j.succ))) =
      F.inclusionN (F.ExpN (F.N.equiv (vertex n q j.castSucc))) *
        Exp (t n q j • (M.letter (mode n q j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hinterior : ∀ i, ∃ z ∈ U,
      s i < M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    (ν : ∀ n, ProbabilityMeasure (K n))
    (j : Fin (N + 1)) {η : ℝ} (hη : 0 < η) :
    let profile : ∀ n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × K n) →
      Fin (N + 1) → C((Fin (finrank ℝ H) → ℝ), W) :=
      fun n q j => F.sampledProbeProfile hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0)) q.1 (vertex n q.2 j)
    Tendsto (fun n => (cellProbabilityMeasure volume
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 :
        Measure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)).prod (ν n : Measure (K n))
      {q | η ≤ dist ((profile n q j).restrict Z) ((profile n q 0).restrict Z)})
      atTop (𝓝 0) := by
  dsimp only
  let profile : ∀ n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × K n) →
      Fin (N + 1) → C((Fin (finrank ℝ H) → ℝ), W) :=
    fun n q j => F.sampledProbeProfile hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0)) q.1 (vertex n q.2 j)
  have hp (n : ℕ) (j : Fin (N + 1)) : Measurable (fun q => profile n q j) :=
    F.measurable_sampledProbeProfile hN hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      b₀ (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))
      (fun q => vertex n q j) (hvertexMeas n j)
  let : MeasurableSpace C(Z, W) := borel _
  let : BorelSpace C(Z, W) := ⟨rfl⟩
  have hm (n : ℕ) (j : Fin (N + 1)) : Measurable (fun q =>
      dist ((profile n q j).restrict Z) ((profile n q 0).restrict Z)) := by
    have hr : Measurable (fun f : C((Fin (finrank ℝ H) → ℝ), W) => f.restrict Z) :=
      (ContinuousMap.continuous_restrict Z).measurable
    exact continuous_dist.measurable.comp ((hr.comp (hp n j)).prodMk (hr.comp (hp n 0)))
  exact M.cartan_independent_raw_chain_concentration T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hweights hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε vertex hvertex
    rem hdim p x profile (fun _ _ _ _ _ _ => by
      simp only [profile, CartanFactorModel.sampledProbeProfile_apply])
    U hU hconn hUne hUheight σ hσ mode t s hB htamp hstep hinterior Z hZU ν hm j hη

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLinkedChainConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous concentration for the linked actual chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

/- Coefficients and logarithmic bounds come from the actual linked chains. -/
set_option maxHeartbeats 1000000 in
theorem cartan_linked_chain_concentration
    {K : ℕ → Type} [∀ n, MeasurableSpace (K n)] [∀ n, Nonempty (K n)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ∀ n, K n → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P origin base ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (hinterior : ∀ k i, ∃ z ∈ U,
      (M.supportIn T hunimod eW).weightSupport (Eprobe k) i <
        M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    (ν : ∀ n, ProbabilityMeasure (K n))
    (k : Fin 3) (j : Fin ((P k).length + 1)) {η : ℝ} (hη : 0 < η) :
    let profile : ∀ n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × K n) →
      Fin ((P k).length + 1) → C((Fin (finrank ℝ H) → ℝ), W) :=
      fun n q j => F.sampledProbeProfile hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0)) q.1 (D.vertex k n q.2 j)
    Tendsto (fun n => (cellProbabilityMeasure volume
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 :
        Measure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)).prod (ν n : Measure (K n))
      {q | η ≤ dist ((profile n q j).restrict Z) ((profile n q 0).restrict Z)})
      atTop (𝓝 0) := by
  dsimp only
  have hbound (n) (q) (j) :
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (D.vertex k n q j)‖ ≤ Real.exp (scale n * ε n) := by
    simpa only [bracketWordExponent_const_mul, boxCost] using D.bound k n q j
  have hamp (j : Fin (P k).length) : ∀ᶠ n in atTop, ∀ q,
      |(P k).coefficient n q j| ≤ (P k).amplitude * Real.exp (scale n *
        ((M.supportIn T hunimod eW).weightSupport (Eprobe k) ((P k).mode n j) + ε n)) := by
    filter_upwards [] with n q
    apply ((P k).coefficient_bound n q j).trans
    apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (P k).amplitude_ge_one)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (le_trans zero_le_one (hscale1 n)) (hεpos n)]
  have hstep (n) (q) (j) :
      F.inclusionN (F.ExpN (F.N.equiv (D.vertex k n q j.succ))) =
        F.inclusionN (F.ExpN (F.N.equiv (D.vertex k n q j.castSucc))) *
          Exp ((P k).coefficient n q j •
            (M.letter ((P k).mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    have hs := congrArg F.inclusionN (D.step k n q j)
    rw [map_mul] at hs
    exact hs.trans (congrArg
      (fun z => F.inclusionN (F.ExpN (F.N.equiv (D.vertex k n q j.castSucc))) * z)
      (F.compatibleN ((P k).coefficient n q j • M.letter ((P k).mode n j))))
  exact M.cartan_actual_chain_concentration T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hweights hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε (D.vertex k) hbound
    rem hdim p x hN hD (D.measurable k) U hU hconn hUne hUheight σ hσ
    (fun n _ j => (P k).mode n j) (P k).coefficient
    ((M.supportIn T hunimod eW).weightSupport (Eprobe k))
    (le_trans zero_le_one (P k).amplitude_ge_one) hamp hstep (hinterior k) Z hZU ν j hη

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLinkedProfileSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Select all actual linked prefixes from the original product law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem select_actual_linked_profiles
    {Y : ℕ → Type} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    (scale : ℕ → ℝ) (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ℕ → cartanRootIdeal H) (η : ℕ → ℝ)
    (D : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P
      (fun n _ => origin n) (fun n _ => base n) η)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x : ℕ → G)
    (r : ℕ → ℝ)
    (bN : ℕ → Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : ℕ → Basis (Fin (finrank ℝ H)) ℝ H)
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (μ : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (ν : ∀ n, ProbabilityMeasure (Y n)) [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (carrying : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hcarrying : MeasurableSet carrying) (hfull : (μ : Measure _) carryingᶜ = 0)
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (q : Z → W) (A : W →ₗ[ℝ] W) (b : Bool → W)
    (f : C(Z, W) × C(Z, W)) (hf : f ∈ (limitLaw : Measure _).support)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    (hlim :
      let profile := fun n y =>
        ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
          (origin n)).restrict Z,
         (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
          (base n)).restrict Z)
      Tendsto (fun n => ProbabilityMeasure.map μ (f := (profile n)) ((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable) atTop (𝓝 limitLaw))
    (hconcentration : ∀ k j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure _).prod (ν n : Measure (Y n))
        {p | ε ≤ dist
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) p.1
            (D.vertex k n p.2 j)).restrict Z)
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) p.1
            (D.vertex k n p.2 0)).restrict Z)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (good n)) ∧
      ∀ᶠ n in atTop, sample n ∈ carrying ∧
        (∀ (s : Bool) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (if s then base n else origin n) z - (A (q z) + b s)‖ < ε n) ∧
        ∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (D.vertex k n y j) z - (A (q z) + b (k != 0))‖ < 2 * ε n := by
  let cp : ∀ k n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × Y n) →
      Fin ((P k).length + 1) → C(Z, W) := fun k n p j => (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
    (bN n) (bD n) p.1 (D.vertex k n p.2 j)).restrict Z
  let sp := fun n y =>
    ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
      (origin n)).restrict Z,
     (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
      (base n)).restrict Z)
  have hcp (k n j) : Measurable (fun p => cp k n p j) :=
    (ContinuousMap.continuous_restrict Z).measurable.comp
      (F.measurable_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) b₀ (bN n)
        (bD n) (D.vertex k n · j) (D.measurable k n j))
  have hsp (n) : Measurable (sp n) :=
    (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n)
      (bN n) (bD n) (origin n) Z).prodMk
    (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n)
      (bN n) (bD n) (base n) Z)
  have hs₂ (n p) : cp 2 n p 0 = cp 1 n p (Fin.last (P 1).length) := by
    simp only [cp, D.third_start]
  obtain ⟨ε, sample, good, hε0, hε, hg, he⟩ :=
    exists_supported_three_product_affine_probe_sequence μ ν carrying hcarrying hfull
      sp hsp limitLaw hlim hf q A b haffine (cp 0) (cp 1) (cp 2)
      (hcp 0) (hcp 1) (hcp 2) hs₂
      (by simpa only [cp, sp, D.first_start] using hconcentration 0)
      (by simpa only [cp, sp, D.second_start] using hconcentration 1) (hconcentration 2)
  refine ⟨ε, sample, good, hε0, hε, hg, he.mono ?_⟩
  intro n hn
  refine ⟨hn.1, ?_, ?_⟩
  · intro s z
    cases s
    · simpa [sp] using hn.2.1 false z
    · simpa [sp] using hn.2.1 true z
  · intro y hy k j z
    fin_cases k
    · exact hn.2.2.1 y hy j z
    · exact hn.2.2.2.1 y hy j z
    · exact hn.2.2.2.2 y hy j z

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConcentratedProbeSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good linked probes from the published concentration inputs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem select_linked_profiles_of_published_inputs_oai
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (hinterior : ∀ k i, ∃ z ∈ U,
      (M.supportIn T hunimod eW).weightSupport (Eprobe k) i <
        M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (b : Bool → W) (f : C(Z, W) × C(Z, W))
    (hf : f ∈ (limitLaw : Measure _).support)
    (haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b s)
    (hlim :
      let J := fun n g => (π ((p n).val.1 g)).toAdd
      let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
      let r := fun n => max (Real.log (scale n)) 0
      let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
      let bD := fun n => exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
      Tendsto (fun n => ProbabilityMeasure.map
        (cellProbabilityMeasure volume
          (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
        (f := (fun y =>
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (origin n)).restrict Z,
           (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)) :
    let J := fun n g => (π ((p n).val.1 g)).toAdd
    let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
    let r := fun n => max (Real.log (scale n)) 0
    let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
    let bD := fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
    let q := fun z : Z => eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        sample n ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
        (∀ (s : Bool) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (if s then base n else origin n) z - (A (q z) + b s)‖ < η n) ∧
        ∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (D.vertex k n y j) z - (A (q z) + b (k != 0))‖ < 2 * η n := by
  dsimp only
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  let μ := cellProbabilityMeasure volume cube (coordinate_cube_mass zero_lt_one).1
    (coordinate_cube_mass zero_lt_one).2
  have hfull : (μ : Measure _) cubeᶜ = 0 := by
    change (μ : Measure _) {y | ¬ y ∈ cube} = 0
    apply ae_iff.mp
    filter_upwards [ae_mem_cellProbabilityMeasure volume cube measurableSet_Icc
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2] with y hy
    exact hy
  apply M.select_actual_linked_profiles T F hunimod eW b₀ Eprobe β
    (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
    scale probe P origin base ε D hN hD
    (fun n g => (π ((p n).val.1 g)).toAdd)
    (fun n => (hπ.comp (p n).property.1.1).continuous) x
    (fun n => max (Real.log (scale n)) 0)
    (fun n => M.boxBasis T hunimod eW E β (scale n))
    (fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
      (max (Real.log (scale n)) 0))
    Z μ ν cube measurableSet_Icc hfull limitLaw _ A b f hf haffine hlim
  intro k j η hη
  exact M.cartan_linked_chain_concentration T F hunimod eW hExp realize haarN haarD
    dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
    hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
    scale hscale hmono hscale1 ε hεpos hε Eprobe probe P
    (fun n _ => origin n) (fun n _ => base n) D rem hdim p x hN hD
    U hU hconn hUne hUheight σ hσ hinterior Z hZU ν k j hη

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs_oai := @OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs_oai
