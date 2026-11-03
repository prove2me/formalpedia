-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:54:31.687806+00:00
-- url     : https://prove2.me/submissions/c197dee4-1596-40b2-9460-eae36849a014

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D013
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_concentrated_profile_frames

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting the first quotient restriction to a tile's frame -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]

/-- The quotient orbit point is independent of the chosen overlapping
factorization of the ambient element. -/
theorem quotient_lift_coordinate
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (n : N) (d : D) : act (ι n * κ d) 1 = π n := by
  rw [hact, map_one, mul_one]

/-- A first-sheet quotient bound becomes a translated automorphic image
in the second-sheet frame. The translation may have arbitrary size. -/
theorem quotient_restriction_in_anchor_frame
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (base anchor endpoint : G) (u n₀ : N) (d d₀ : D)
    (hlift : anchor⁻¹ * endpoint = ι u * κ d)
    (hframe : anchor⁻¹ * base = ι n₀ * κ d₀)
    (T : Set Q) (hfirst : act (base⁻¹ * endpoint) 1 ∈ T) :
    π u ∈ π n₀ • (α d₀ '' T) := by
  have heq : act (anchor⁻¹ * endpoint) 1 =
      act (anchor⁻¹ * base) (act (base⁻¹ * endpoint) 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [hlift, quotient_lift_coordinate ι κ π α act hact, hframe, hact] at heq
  rw [heq]
  exact ⟨α d₀ (act (base⁻¹ * endpoint) 1),
    ⟨act (base⁻¹ * endpoint) 1, hfirst, rfl⟩, rfl⟩

end PolycyclicRecognition

end OAI
end

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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

theorem exponent_le_of_sequence_subexponential_bounds
    {scale f g : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hbound : ∀ᶠ n in atTop, f n * Real.exp (scale n * p) ≤ g n * Real.exp (scale n * q)) :
    p ≤ q := by
  by_contra h
  have hpq : q < p := lt_of_not_ge h
  let ε := (p - q) / 4
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨n, hn, hm, hb, hnpos⟩ := ((hf ε hε).and ((hg ε hε).and
    (hbound.and (hs.eventually (eventually_gt_atTop (0 : ℝ)))))).exists
  have he : Real.exp ((p - ε) * scale n) ≤ Real.exp ((q + ε) * scale n) := calc
    _ = Real.exp (-ε * scale n) * Real.exp (scale n * p) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * Real.exp (scale n * p) := mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ ≤ g n * Real.exp (scale n * q) := hb
    _ ≤ Real.exp (ε * scale n) * Real.exp (scale n * q) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := Real.exp_le_exp.mp he
  have hgap : 0 < p - q - 2 * ε := by dsimp [ε] <;> linarith
  have hprod := mul_pos hgap hnpos
  nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponentialOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem sequence_subexponential_lower_const (hs : Tendsto scale atTop atTop)
    {c : ℝ} (hc : 0 < c) : HasSubexponentialLowerBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_lower_const hc).along_sequence hs

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineSheetAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local agreement identifies affine sheet profiles on the whole domain -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous image of a supported sample is supported by its image law. -/
theorem mem_support_map_of_continuous
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (f : X → Y) (hf : Continuous f)
    {x : X} (hx : x ∈ (μ : Measure X).support) :
    f x ∈ (ProbabilityMeasure.map μ (f := f) (by first | exact hf.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure Y).support := by
  apply (Measure.mem_support_iff_forall (f x)).mpr
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  apply lt_of_lt_of_le _ (measure_mono hVU)
  change 0 < Measure.map f (μ : Measure X) V
  rw [Measure.map_apply hf.measurable hV.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV))

/-- Projection of a weak limit of sampled pairs is the weak limit of the
projected samples, with no change of sampling law. -/
theorem sampled_projection_tendsto
    {A X Y : Type} [MeasurableSpace A]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ℕ → ProbabilityMeasure A) (p : ℕ → A → X) (hp : ∀ n, Measurable (p n))
    (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (μ n) (f := (p n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (f : X → Y) (hf : Continuous f) :
    Tendsto (fun n => ProbabilityMeasure.map (μ n) (f := (f ∘ p n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop
      (𝓝 (ProbabilityMeasure.map ν (f := f) (by first | exact hf.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have ht := (ProbabilityMeasure.continuous_map hf).tendsto ν |>.comp hν
  apply ht.congr'
  filter_upwards [] with n
  apply Subtype.ext
  exact Measure.map_map hf.measurable (hp n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FactorProductPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing through a possibly noninjective factor map

Left translations on a semidirect product act separately on its two factor
coordinates. Their product measure is preserved when the action preserves
the first factor's measure. Disjointness is tested after projection to the
ambient metric group, so no injectivity of that projection is required.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]

/-- Product Haar mass is unchanged by these translations. -/
theorem factorTranslate_measure (φ : D →* MulAut N)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (p : N × D) (U : Set (N × D)) :
    (μ.prod ν) (factorTranslate φ p '' U) = (μ.prod ν) U := by
  let e := factorTranslationEquiv φ (fun d => (hφ d).measurable) p
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    ((measurePreserving_mul_left μ p.1).comp (hφ p.2)).prod
      (measurePreserving_mul_left ν p.2)
  have he : e ⁻¹' (e '' U) = U := e.preimage_image U
  have hv := hp.measure_preimage_equiv (e '' U)
  rw [he] at hv
  exact hv.symm

omit [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D] in
/-- The product-coordinate map intertwines translations and ambient multiplication. -/
theorem factorTranslate_projection (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) (p z : N × D) :
    ι (factorTranslate φ p z).1 * κ (factorTranslate φ p z).2 =
      (ι p.1 * κ p.2) * (ι z.1 * κ z.2) := by
  simp only [factorTranslate, map_mul, hc]
  group

variable [MetricSpace G] [IsIsometricSMul G G]

/-- Every finite separated family of ambient projections gives disjoint
translated cells in the product of the factors, even if the factor map has
nontrivial fibers. -/
theorem factor_separated_card_mul_le (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (p : G → N × D) (U region : Set (N × D))
    (hU : MeasurableSet U) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ region) :
    (s.card : ℝ≥0∞) * (μ.prod ν) U ≤ (μ.prod ν) region := by
  classical
  let cell (x : G) := factorTranslate φ (p x) '' U
  have hcell (x : G) : MeasurableSet (cell x) :=
    (factorTranslationEquiv φ (fun d => (hφ d).measurable) (p x)).measurableSet_image.mpr hU
  have hnear (x : G) (hx : x ∈ s) {z : N × D} (hz : z ∈ cell x) :
      dist x (ι z.1 * κ z.2) < ρ / 2 := by
    obtain ⟨u, hu, rfl⟩ := hz
    rw [factorTranslate_projection φ ι κ hc]
    calc
      _ = dist (ι (p x).1 * κ (p x).2)
          ((ι (p x).1 * κ (p x).2) * (ι u.1 * κ u.2)) := by
        exact congrArg (fun y => dist y ((ι (p x).1 * κ (p x).2) * (ι u.1 * κ u.2)))
          (hp x hx).symm
      _ = dist (1 : G) (ι u.1 * κ u.2) := by
        simpa only [mul_one] using
          dist_mul_left (ι (p x).1 * κ (p x).2) (1 : G) (ι u.1 * κ u.2)
      _ < _ := hsmall u hu
  have hd : Set.Pairwise (↑s : Set G) (fun x y => Disjoint (cell x) (cell y)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have h1 := hnear x hx hzx
    have h2 := hnear y hy hzy
    have ht := dist_triangle x (ι z.1 * κ z.2) y
    rw [dist_comm (ι z.1 * κ z.2) y] at ht
    linarith [hsep x hx y hy hxy]
  calc
    (s.card : ℝ≥0∞) * (μ.prod ν) U = (μ.prod ν) (⋃ x ∈ s, cell x) := by
      rw [measure_biUnion_finset hd (fun x _ => hcell x)]
      simp only [cell, factorTranslate_measure φ μ ν hφ, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := measure_mono (iUnion₂_subset hthick)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FactorProductVolumeBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real cardinal bounds for lifts in a product region -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Metric
open scoped ENNReal

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- Fixed positive lifted cells convert a product-volume estimate into a
separated endpoint count. The factor projection need not be injective. -/
theorem factor_separated_card_le_product_volume (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (p : G → N × D) (U : Set (N × D)) (E : Set N) (B : Set D)
    (hU : MeasurableSet U) (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : μ E ≠ ⊤) (hB : ν B ≠ ⊤) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ E ×ˢ B) :
    (s.card : ℝ) ≤ (μ E).toReal * (ν B).toReal / ((μ.prod ν) U).toReal := by
  have hh := factor_separated_card_mul_le φ ι κ hc μ ν hφ s p U (E ×ˢ B)
    hU hp hsmall hsep hthick
  rw [Measure.prod_prod] at hh
  have hfinite : μ E * ν B ≠ ⊤ := ENNReal.mul_ne_top hE hB
  have hr := ENNReal.toReal_mono hfinite hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
  exact (le_div_iff₀ (ENNReal.toReal_pos hU0 hUtop)).mpr hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AnchoredTilePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing tiles whose factor lifts use different anchors

Endpoint sets stay in the common ambient frame. Each tile may choose its
own left-translated factor coordinates without changing its cardinality
or the separation constant.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

theorem factor_anchored_card_le_product_volume (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (anchor : G) (p : G → N × D)
    (U : Set (N × D)) (E : Set N) (B : Set D)
    (hU : MeasurableSet U) (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : μ E ≠ ⊤) (hB : ν B ≠ ⊤) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = anchor⁻¹ * x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ E ×ˢ B) :
    (s.card : ℝ) ≤ (μ E).toReal * (ν B).toReal / ((μ.prod ν) U).toReal := by
  let f : G ↪ G := ⟨fun x => anchor⁻¹ * x, fun _ _ h => mul_left_cancel h⟩
  let p' : G → N × D := fun x => p (anchor * x)
  have hp' : ∀ x ∈ s.map f, ι (p' x).1 * κ (p' x).2 = x := by
    intro x hx
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    change ι (p (anchor * (anchor⁻¹ * x))).1 * κ (p (anchor * (anchor⁻¹ * x))).2 = anchor⁻¹ * x
    rw [mul_inv_cancel_left]
    exact hp x hsx
  have hsep' : ∀ x ∈ s.map f, ∀ y ∈ s.map f, x ≠ y → ρ ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hsy, rfl⟩ := Finset.mem_map.mp hy
    have hne : x ≠ y := fun h => hxy (congrArg f h)
    change ρ ≤ dist (anchor⁻¹ * x) (anchor⁻¹ * y)
    rw [dist_mul_left]
    exact hsep x hsx y hsy hne
  have hthick' : ∀ x ∈ s.map f, factorTranslate φ (p' x) '' U ⊆ E ×ˢ B := by
    intro x hx
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    change factorTranslate φ (p (anchor * (anchor⁻¹ * x))) '' U ⊆ E ×ˢ B
    rw [mul_inv_cancel_left]
    exact hthick x hsx
  simpa only [Finset.card_map] using factor_separated_card_le_product_volume
    φ ι κ hc μ ν hφ (s.map f) p' U E B hU hU0 hUtop hE hB hp' hsmall hsep' hthick'

/-- Common per-tile bounds in independently translated factor frames. -/
theorem sequence_anchored_tile_separated_count
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (tiles : ℕ → ℕ) (s : ∀ n, Fin (tiles n) → Finset G)
    (anchor : ∀ n, Fin (tiles n) → G)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (U : Set (N × D)) (hU : MeasurableSet U)
    (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : ∀ n j, μ (E n j) ≠ ⊤) (hB : ∀ n, ν (B n) ≠ ⊤) {ρ : ℝ}
    (hp : ∀ n j, ∀ x ∈ s n j, ι (p n j x).1 * κ (p n j x).2 = (anchor n j)⁻¹ * x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ s n j, ∀ y ∈ s n j, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ s n j, factorTranslate φ (p n j x) '' U ⊆ E n j ×ˢ B n)
    (A Bvol : ℕ → ℝ)
    (hA : HasSubexponentialUpperBoundSeq scale A)
    (hBvol : HasSubexponentialUpperBoundSeq scale Bvol)
    (hA0 : ∀ n, 0 ≤ A n) (hBvol0 : ∀ n, 0 ≤ Bvol n)
    (P ell : ℝ)
    (hNvol : ∀ n j, (μ (E n j)).toReal ≤ A n * Real.exp ((P - ell) * scale n))
    (hDvol : ∀ n, (ν (B n)).toReal ≤ Bvol n) :
    ∃ loss : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale loss ∧
      (∀ n, 0 ≤ loss n) ∧ ∀ᶠ n in atTop, ∀ j,
        ((s n j).card : ℝ) ≤ loss n * Real.exp ((P - ell) * scale n) := by
  let c := ((μ.prod ν) U).toReal
  have hc0 : 0 < c := ENNReal.toReal_pos hU0 hUtop
  let loss := fun n => A n * Bvol n * c⁻¹
  have hloss : HasSubexponentialUpperBoundSeq scale loss :=
    (hA.mul hBvol (Eventually.of_forall hA0)).mul
      (sequence_subexponential_upper_const hscale c⁻¹)
      (Eventually.of_forall (fun n => mul_nonneg (hA0 n) (hBvol0 n)))
  refine ⟨loss, hloss,
    fun n => mul_nonneg (mul_nonneg (hA0 n) (hBvol0 n)) (inv_nonneg.mpr hc0.le), ?_⟩
  filter_upwards [hthick] with n hn
  intro j
  have hcount := factor_anchored_card_le_product_volume φ ι κ hc μ ν hφ
    (s n j) (anchor n j) (p n j) U (E n j) (B n) hU hU0 hUtop (hE n j) (hB n)
    (hp n j) hsmall (hsep n j) (hn j)
  calc
    _ ≤ (μ (E n j)).toReal * (ν (B n)).toReal / c := hcount
    _ ≤ (A n * Real.exp ((P - ell) * scale n)) * Bvol n / c := by
      apply div_le_div_of_nonneg_right _ hc0.le
      exact mul_le_mul (hNvol n j) (hDvol n) ENNReal.toReal_nonneg
        (mul_nonneg (hA0 n) (Real.exp_pos _).le)
    _ = loss n * Real.exp ((P - ell) * scale n) := by dsimp [loss] <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathConcatenation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse metric bounds under path concatenation

The additive error is retained explicitly. This allows logarithmic-diameter
switches and coarse-speed one-parameter legs to use a fixed finite mesh.
-/

namespace PolycyclicRecognition

open scoped unitInterval

variable {X : Type} [PseudoMetricSpace X] {x y z : X}

theorem PathMetricBound.cast {p : Path x y} {L κ : ℝ} (h : PathMetricBound p L κ)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : PathMetricBound (p.cast hx hy) L κ := h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedPairPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation and paths under an actual normalized pair -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal

variable {G : Type} [Group G] [MetricSpace G] {Λ : ℝ≥0}

/-- The lower metric inequality turns this fixed source separation into
unit separation in the image. -/
theorem normalizedPair_image_dist_gt_one (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {x y : G}
    (hxy : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    1 < dist (p.val.1 x) (p.val.1 y) := by
  have hi : 0 < (Λ : ℝ)⁻¹ := inv_pos.mpr hΛ
  calc
    1 = (Λ : ℝ)⁻¹ * ((Λ : ℝ) * ((Λ : ℝ) + 1)) - Λ := by field_simp <;> ring
    _ < (Λ : ℝ)⁻¹ * dist x y - Λ := sub_lt_sub_right (mul_lt_mul_of_pos_left hxy hi) _
    _ ≤ _ := p.property.1.2.2.1 x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasedImagePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths centered at their actual common starting point -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W : Type} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsTopologicalGroup G] in
theorem basedImage_dist (F : G → G) (a g h : G) :
    dist (basedImage F a g) (basedImage F a h) = dist (F g) (F h) :=
  dist_mul_left _ _ _

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [MetricSpace G] [NormedSpace ℝ W] in
theorem basedImage_height (π : G →* Multiplicative W) (F : G → G) (a g : G) :
    (π (basedImage F a g)).toAdd = (π (F g)).toAdd - (π (F a)).toAdd := by
  simp only [basedImage, map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

omit [IsTopologicalGroup G] in
/-- A based image of a separated source set has the same cardinality and
unit-separated points, by the actual lower quasi-isometry inequality. -/
theorem basedImage_separated_card [DecidableEq G] {Λ : ℝ≥0} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (a : G) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    (s.image (basedImage p.val.1 a)).card = s.card ∧
      ∀ x ∈ s.image (basedImage p.val.1 a),
        ∀ y ∈ s.image (basedImage p.val.1 a), x ≠ y → 1 ≤ dist x y := by
  classical
  have hd (x y : G) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
      1 < dist (basedImage p.val.1 a x) (basedImage p.val.1 a y) := by
    rw [basedImage_dist]
    exact normalizedPair_image_dist_gt_one p hΛ (hsep x hx y hy hne)
  constructor
  · apply Finset.card_image_iff.mpr
    intro x hx y hy he
    by_contra hne
    have hh := hd x y hx hy hne
    rw [he, dist_self] at hh
    linarith
  · intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (hd u v hu hv (fun he => hne (congrArg _ he))).le

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CellProbabilityTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting normalized cell sampling through an injective chart -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Equal relative masses of chart images identify the normalized sampling
laws. This is used with the exact exponential-coordinate Jacobian. -/
theorem map_cellProbabilityMeasure_of_image_ratio
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : Measurable f)
    (C : Set X) (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (himage0 : ν (f '' C) ≠ 0) (himagefin : ν (f '' C) ≠ ∞)
    (hratio : ∀ A : Set X, (ν (f '' A)).toReal / (ν (f '' C)).toReal =
      (μ A).toReal / (μ C).toReal) :
    ProbabilityMeasure.map (cellProbabilityMeasure μ C hC0 hCfin) (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) =
      cellProbabilityMeasure ν (f '' C) himage0 himagefin := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (Measure.map f (cellProbabilityMeasure μ C hC0 hCfin : Measure X) B).toReal = _
  rw [Measure.map_apply hf hB]
  rw [cellProbabilityMeasure_apply_toReal μ C (f ⁻¹' B) hC0 hCfin (hf hB),
    cellProbabilityMeasure_apply_toReal ν (f '' C) B himage0 himagefin hB]
  have himage : f '' (f ⁻¹' B ∩ C) = B ∩ f '' C := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
      exact ⟨hx, x, hxc, rfl⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  rw [← himage]
  exact (hratio (f ⁻¹' B ∩ C)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GoodProfileFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profile control along the actual converging horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Recover the physical-scale image height from the actual normalized
profile, with its prescribed common center. -/
theorem height_bound_of_rescaled_profile
    {G W Z : Type} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x n : G) (s : ℝ) (φ : Z → G) (z : Z) (w : W) {ε : ℝ}
    (h : ‖rescaledMapProfile J x n s φ z - w‖ ≤ ε) :
    ‖J (x * n * φ z) - J x - Real.exp s • w‖ ≤ Real.exp s * ε := by
  have he : J (x * n * φ z) - J x - Real.exp s • w =
      Real.exp s • (rescaledMapProfile J x n s φ z - w) := by
    simp only [rescaledMapProfile, smul_sub, smul_smul,
      mul_inv_cancel₀ (Real.exp_ne_zero s), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos s).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredProfilePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering profile-controlled paths at their actual initial image -/

namespace PolycyclicRecognition

open Set

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Centering costs only the profile error at the initial point. -/
theorem norm_centered_sub_smul_le {u a c w w₀ : W} {r B B₀ : ℝ}
    (hu : ‖u - c - r • w‖ ≤ B) (ha : ‖a - c - r • w₀‖ ≤ B₀) :
    ‖u - a - r • (w - w₀)‖ ≤ B + B₀ := by
  have he : u - a - r • (w - w₀) = (u - c - r • w) - (a - c - r • w₀) := by
    rw [smul_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hu ha)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedProbabilityRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Viewing a supported probability as a probability on its compact support -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

theorem supportedProbabilityRestriction_map
    {X : Type} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    Measure.map Subtype.val (supportedProbabilityRestriction μ K hK hfull : Measure K) = μ := by
  exact (map_comap_subtype_coe hK _).trans
    (Measure.restrict_eq_self_of_ae_mem hfull)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProbeLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retained compact probes in the ambient product Haar coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

/-- Returning a retained compact probe set from a carrying subtype to the
ambient space preserves its exact original probability mass. -/
theorem compact_supported_probe_image
    {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (carrying : Set X) (hc : MeasurableSet carrying)
    (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ carrying)
    (K : Set carrying) (hK : IsCompact K) :
    IsCompact (Subtype.val '' K) ∧ MeasurableSet (Subtype.val '' K) ∧
      Subtype.val '' K ⊆ carrying ∧
      (μ : Measure X) (Subtype.val '' K) =
        (supportedProbabilityRestriction μ carrying hc hfull : Measure carrying) K := by
  have hcompact : IsCompact (Subtype.val '' K : Set X) := hK.image continuous_subtype_val
  refine ⟨hcompact, hcompact.isClosed.measurableSet, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact y.property
  · rw [← supportedProbabilityRestriction_map μ carrying hc hfull,
      Measure.map_apply measurable_subtype_coe hcompact.isClosed.measurableSet]
    rw [preimage_image_eq _ Subtype.val_injective]

theorem cellSubtypeProbability_compact_image
    {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (C : Set X) (hC : MeasurableSet C)
    (hzero : μ C ≠ 0) (hfinite : μ C ≠ ⊤)
    (K : Set C) (hK : IsCompact K) :
    IsCompact (Subtype.val '' K) ∧ MeasurableSet (Subtype.val '' K) ∧
      Subtype.val '' K ⊆ C ∧
      (cellProbabilityMeasure μ C hzero hfinite : Measure X) (Subtype.val '' K) =
        (cellSubtypeProbability μ C hC hzero hfinite : Measure C) K :=
  compact_supported_probe_image (cellProbabilityMeasure μ C hzero hfinite) C hC
    (ae_mem_cellProbabilityMeasure μ C hC hzero hfinite) K hK

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuotientSectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume bounds at arbitrary translated quotient locations

The admissible set only needs separate bounds on its ideal and quotient
coordinates. Its coordinates need not be independent or form a product.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Pointwise ENNReal

variable {N Q : Type} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]

omit [IsTopologicalGroup Q] [SFinite μQ] in
/-- Separate coordinate restrictions bound the actual pushed-forward
measure by the measure of the containing product set. -/
theorem quotientSection_measure_le (E : Set N) (T : Set Q) (B : Set π.ker)
    (hE : ∀ n ∈ E, π n ∈ T ∧ quotientSectionResidual π s hs n ∈ B) :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) E ≤
      μQ T * μI B := by
  let e := quotientSectionHomeomorph π hπ s hs
  rw [e.symm.measurableEmbedding.map_apply]
  calc
    _ ≤ (μQ.prod μI) (T ×ˢ B) := by
      apply measure_mono
      intro p hp
      have hh := hE (e.symm p) hp
      change e (e.symm p) ∈ T ×ˢ B at hh
      simpa only [e.apply_symm_apply] using hh
    _ = _ := Measure.prod_prod T B

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceSectionTileVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {N Q : Type} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulLeftInvariant]

omit [SFinite μQ] in
/-- All tiles share one subexponential loss even though their quotient
translations and automorphisms vary independently. This also proves the
finiteness needed by the separated-cell packing inequality. -/
theorem sequence_section_tile_family_volume_exponent
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {J : ℕ → Type} (E : ∀ n, J n → Set N) (T : ℕ → Set Q) (B : ℕ → Set π.ker)
    (q₀ : ∀ n, J n → Q) (α : ∀ n, J n → Q ≃ Q)
    (P ell : ℝ) (ε U V : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hB : ∀ n, μI (B n) ≠ ⊤)
    (hα : ∀ n j, μQ (α n j '' T n) ≤
      ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) * μQ (T n))
    (hTB : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIB : ∀ n, (μI (B n)).toReal ≤ V n * Real.exp (P * scale n))
    (hE : ∀ n j, ∀ x ∈ E n j, π x ∈ q₀ n j • (α n j '' T n) ∧
      quotientSectionResidual π s hs x ∈ B n) :
    ∃ loss : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale loss ∧
      (∀ n, 0 ≤ loss n) ∧ ∀ n j,
        (Measure.map (quotientSectionHomeomorph π hπ s hs).symm
          (μQ.prod μI)) (E n j) ≠ ⊤ ∧
        ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
          (μQ.prod μI)) (E n j)).toReal ≤
          loss n * Real.exp ((P - ell) * scale n) := by
  let loss := fun n => U n * V n * Real.exp (ε n * scale n)
  have hloss : HasSubexponentialUpperBoundSeq scale loss :=
    (hU.mul hV (Eventually.of_forall hU0)).mul
      (sequence_subexponential_exp_error hscale hε)
      (Eventually.of_forall (fun n => mul_nonneg (hU0 n) (hV0 n)))
  refine ⟨loss, hloss,
    fun n => mul_nonneg (mul_nonneg (hU0 n) (hV0 n)) (Real.exp_pos _).le, ?_⟩
  intro n j
  have hfinite : ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) *
      μQ (T n) * μI (B n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hT n)) (hB n)
  have hbound := quotientSection_measure_le π hπ s hs μQ μI (E n j)
    (q₀ n j • (α n j '' T n)) (B n) (hE n j)
  rw [measure_smul] at hbound
  have hbound' := hbound.trans (mul_le_mul' (hα n j) le_rfl)
  refine ⟨ne_top_of_le_ne_top hfinite hbound', ?_⟩
  have hv : ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
      (μQ.prod μI)) (E n j)).toReal ≤
      Real.exp (-ell * scale n + ε n * scale n) *
        (μQ (T n)).toReal * (μI (B n)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono hfinite hbound'
  calc
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) *
        (μQ (T n)).toReal * (μI (B n)).toReal := hv
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) * U n *
        (V n * Real.exp (P * scale n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hTB n) (Real.exp_nonneg _))
        (hIB n) ENNReal.toReal_nonneg (mul_nonneg (Real.exp_nonneg _) (hU0 n))
    _ = loss n * Real.exp ((P - ell) * scale n) := by
      dsimp only [loss]
      rw [Real.exp_add]
      have he : Real.exp (-ell * scale n) * Real.exp (P * scale n) =
          Real.exp ((P - ell) * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = U n * V n * Real.exp (ε n * scale n) *
            (Real.exp (-ell * scale n) * Real.exp (P * scale n)) := by ring
        _ = _ := by rw [he]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeOffsetPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality from actual lifted cells and section volumes

The first-sheet quotient restriction and the second-sheet ideal restriction
bound all lifted cells. The tile count and source count then cancel their
template exponents, leaving the sign of the quotient trace.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

/-- The covering need not partition the endpoints, and empty tiles are
allowed. A common real cardinal bound still sums over the finite cover. -/
theorem card_le_real_finite_cover {G : Type} {k : ℕ}
    (s : Finset G) (t : Fin k → Finset G)
    (hcover : ∀ x ∈ s, ∃ j, x ∈ t j) {B : ℝ}
    (hbound : ∀ j, ((t j).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ (k : ℝ) * B := by
  classical
  have hsub : s ⊆ Finset.univ.biUnion t := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩
  calc
    (s.card : ℝ) ≤ ((Finset.univ.biUnion t).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j : Fin k, ((t j).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, B := Finset.sum_le_sum (fun j _ => hbound j)
    _ = (k : ℝ) * B := by simp

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- This is the geometric counting endgame: restrictions on actual
quotient and ideal coordinates imply the offset trace inequality.
No point-count estimate or offset-sign assertion is assumed. -/
theorem cone_offset_nonpos_of_lifted_cells
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (anchor : ∀ n, Fin (tiles n) → G)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (q₀ : ∀ n, Fin (tiles n) → Q) (α : ∀ n, Fin (tiles n) → Q ≃ Q)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (anchor n j)⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ ell : ℝ) (ε U V Dvol lower tileLoss : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hα : ∀ n j, μQ (α n j '' T n) ≤
      ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hcoordinates : ∀ n j, ∀ x ∈ E n j,
      π x ∈ q₀ n j • (α n j '' T n) ∧ quotientSectionResidual π σ hs x ∈ I n)
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell ≤ 0 := by
  obtain ⟨A, hA, hA0, hAv⟩ := sequence_section_tile_family_volume_exponent
    π hπ σ hs μQ μI scale hscale E T I q₀ α P₂ ell ε U V hε
    hU hV hU0 hV0 hT hI hα hTvol hIvol hcoordinates
  have hEfinite : ∀ n j, μ (E n j) ≠ ⊤ := by
    intro n j
    simpa only [hμ] using (hAv n j).1
  have hEvol : ∀ n j, (μ (E n j)).toReal ≤ A n * Real.exp ((P₂ - ell) * scale n) := by
    intro n j
    simpa only [hμ] using (hAv n j).2
  obtain ⟨loss, hloss, hloss0, hcount⟩ := sequence_anchored_tile_separated_count φ ι κ hc μ ν hφ
    scale hscale tiles points anchor p E B cell hcell hcell0 hcelltop hEfinite hB
    hp hsmall hsep hthick A Dvol hA hDvol hA0 hDvol0 P₂ ell hEvol hDBound
  have hupper := htileLoss.mul hloss htile0
  have hexponent : P₁ ≤ P₁ - ell := exponent_le_of_sequence_subexponential_bounds
    hscale hlower hupper (by
      filter_upwards [hsource, htiles, hcount] with n hsrc htilesn hcountn
      have hsum := card_le_real_finite_cover (source n) (points n) (hcover n) hcountn
      calc
        lower n * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := hsrc
        _ ≤ (tiles n : ℝ) * (loss n * Real.exp ((P₂ - ell) * scale n)) := hsum
        _ ≤ (tileLoss n * Real.exp (scale n * (P₁ - P₂))) *
            (loss n * Real.exp ((P₂ - ell) * scale n)) :=
          mul_le_mul_of_nonneg_right htilesn
            (mul_nonneg (hloss0 n) (Real.exp_pos _).le)
        _ = (tileLoss n * loss n) * Real.exp (scale n * (P₁ - ell)) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          ring)
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteProfileEnvelope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filling the finitely many exceptional profile scales -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

/-- Eventual uniform control of a finite family can be extended to every
scale without changing the vanishing error sequence on its tail. The size
of the family is allowed to grow with the scale. -/
theorem exists_finite_profile_envelope {J : ℕ → Type} [∀ n, Fintype (J n)]
    (base : ℕ → ℝ≥0) (err : ∀ n, J n → ℝ≥0) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, (base n : ℝ) ≤ η n)
    (he : ∀ᶠ n in atTop, ∀ j, (err n j : ℝ) ≤ η n) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      (∀ n, η n ≤ ε n) ∧ (∀ n, (base n : ℝ) ≤ ε n) ∧
      (∀ n j, (err n j : ℝ) ≤ ε n) := by
  classical
  let upper := fun n => max (base n) (Finset.univ.sup (err n))
  let ε := fun n => max (η n) (upper n : ℝ)
  have hbase (n) : (base n : ℝ) ≤ ε n :=
    (show (base n : ℝ) ≤ (upper n : ℝ) from
      NNReal.coe_le_coe.mpr (le_max_left _ _)).trans (le_max_right _ _)
  have herr (n) (j : J n) : (err n j : ℝ) ≤ ε n := by
    apply (show (err n j : ℝ) ≤ (upper n : ℝ) from ?_).trans (le_max_right _ _)
    exact NNReal.coe_le_coe.mpr ((Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _))
  have heq : ε =ᶠ[atTop] η := by
    filter_upwards [hb, he] with n hbn hen
    apply max_eq_left
    apply max_le hbn
    have hnonneg : 0 ≤ η n := (base n).coe_nonneg.trans hbn
    exact NNReal.coe_le_coe.mp (Finset.sup_le (fun j _ =>
      show err n j ≤ ⟨η n, hnonneg⟩ from hen j))
  exact ⟨ε, hη.congr' heq.symm, fun _ => le_max_left _ _, hbase, herr⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeHeightMultiplier
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Haar character in canonical height coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold BigOperators

/-- A uniform height error controls the Haar multiplier at every anchor.
The location of the translated quotient set never enters the estimate. -/
theorem haar_image_le_of_height_error
    {W Q : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace Q]
    (ell : W →L[ℝ] ℝ) (μ : Measure Q) (α : Q ≃ Q) (S : Set Q)
    (height offset : W) (r ε : ℝ)
    (hvol : μ (α '' S) = ENNReal.ofReal (Real.exp (ell height)) * μ S)
    (herror : ‖height + r • offset‖ ≤ ε) :
    μ (α '' S) ≤ ENNReal.ofReal
      (Real.exp (-ell offset * r + ‖ell‖ * ε)) * μ S := by
  have hle : ell height + r * ell offset ≤ ‖ell‖ * ε := by
    have hh := (le_abs_self (ell (height + r • offset))).trans
      ((ell.le_opNorm (height + r • offset)).trans
        (mul_le_mul_of_nonneg_left herror (norm_nonneg ell)))
    simpa only [map_add, map_smul, smul_eq_mul] using hh
  rw [hvol]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (by linarith))) le_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProfileChainHeightBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative image heights from a common affine profile along the chain -/

noncomputable section
namespace PolycyclicRecognition

variable {G W Z V : Type} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Different affine offsets are retained when comparing the two sheets. -/
theorem relative_height_of_affine_profiles
    (J : G → W) (x k l : G) (r : ℝ) (φ : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b b₀ : W) (z z₀ : Z)
    {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x k r φ z - (A (q z) + b)‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x l r φ z₀ - (A (q z₀) + b₀)‖ ≤ ε₀) :
    ‖J (x * k * φ z) - J (x * l * φ z₀) -
      Real.exp r • (A (q z - q z₀) + (b - b₀))‖ ≤ Real.exp r * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x k r φ z (A (q z) + b) hz)
    (height_bound_of_rescaled_profile J x l r φ z₀ (A (q z₀) + b₀) hz₀)
  have he : (A (q z) + b) - (A (q z₀) + b₀) = A (q z - q z₀) + (b - b₀) := by
    rw [map_sub]
    abel
  simpa only [he, mul_add] using hh

/-- Two different sheets can be centered at the same original image.
Their common affine offset cancels from the relative height estimate. -/
theorem relative_height_of_common_affine_profiles
    (J : G → W) (x k l : G) (r : ℝ) (φ : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z z₀ : Z)
    {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x k r φ z - (A (q z) + b)‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x l r φ z₀ - (A (q z₀) + b)‖ ≤ ε₀) :
    ‖J (x * k * φ z) - J (x * l * φ z₀) -
      Real.exp r • A (q z - q z₀)‖ ≤ Real.exp r * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x k r φ z (A (q z) + b) hz)
    (height_bound_of_rescaled_profile J x l r φ z₀ (A (q z₀) + b) hz₀)
  simpa only [map_sub, add_sub_add_right_eq_sub, mul_add] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeAnchorHaarBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor-frame Haar multiplier from the two actual profile offsets -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

/-- At the common pivot, the linear parts cancel across the two sheets.
The actual anchor-to-base height has the sign needed for quotient volume. -/
theorem anchor_height_error_of_affine_profiles
    {G W V Z : Type} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V]
    (π : G →* Multiplicative W) (F : G → G) (x base anchor : G)
    (r : ℝ) (φ : Z → G) (q : Z → V) (A : V →ₗ[ℝ] W)
    (b₁ b₂ : W) (z₀ : Z) {ε₁ ε₂ : ℝ}
    (hbase : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x base r φ z₀ -
      (A (q z₀) + b₁)‖ ≤ ε₁)
    (hanchor : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x anchor r φ z₀ -
      (A (q z₀) + b₂)‖ ≤ ε₂) :
    ‖(π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd +
      Real.exp r • (b₂ - b₁)‖ ≤ Real.exp r * (ε₁ + ε₂) := by
  have hh := relative_height_of_affine_profiles (fun g => (π (F g)).toAdd)
    x base anchor r φ q A b₁ b₂ z₀ z₀ hbase hanchor
  have he (u v : W) : -v + u + Real.exp r • (b₂ - b₁) =
      u - v - Real.exp r • (b₁ - b₂) := by
    simp only [smul_sub]
    abel
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, he]
  simpa only [sub_self, map_zero, zero_add] using hh

/-- The profile estimate supplies the Haar bound uniformly over any finite
or infinite family of anchors. The quotient set may vary with the scale. -/
theorem anchor_haar_bound_of_affine_profiles
    {G Q W V Z : Type} [Group G] [MeasurableSpace Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [AddCommGroup V] [Module ℝ V]
    (π : G →* Multiplicative W) (F : G → G) (x base anchor : G)
    (r : ℝ) (φ : Z → G) (q : Z → V) (A : V →ₗ[ℝ] W)
    (b₁ b₂ : W) (z₀ : Z) {ε₁ ε₂ : ℝ}
    (hbase : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x base r φ z₀ -
      (A (q z₀) + b₁)‖ ≤ ε₁)
    (hanchor : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x anchor r φ z₀ -
      (A (q z₀) + b₂)‖ ≤ ε₂)
    (ell : W →L[ℝ] ℝ) (μ : Measure Q) (α : Q ≃ Q) (S : Set Q)
    (hvol : μ (α '' S) = ENNReal.ofReal (Real.exp (ell
      (π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd)) * μ S) :
    μ (α '' S) ≤ ENNReal.ofReal (Real.exp
      (-ell (b₂ - b₁) * Real.exp r + (‖ell‖ * (ε₁ + ε₂)) * Real.exp r)) * μ S := by
  have hh := haar_image_le_of_height_error ell μ α S
    (π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd
    (b₂ - b₁) (Real.exp r) (Real.exp r * (ε₁ + ε₂)) hvol
    (anchor_height_error_of_affine_profiles π F x base anchor r φ q A b₁ b₂ z₀ hbase hanchor)
  have he : ‖ell‖ * (Real.exp r * (ε₁ + ε₂)) = (‖ell‖ * (ε₁ + ε₂)) * Real.exp r := by ring
  simpa only [he] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProfileOffsetPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality with the actual affine-profile Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- The sign follows from the two measured affine profiles, the actual
anchor-frame Haar law, and the simultaneous coordinate restrictions on
thickened cells. No offset multiplier estimate is an assumption. -/
theorem cone_offset_nonpos_of_profile_cells
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (q₀ : ∀ n, Fin (tiles n) → Q) (α : ∀ n, Fin (tiles n) → Q ≃ Q)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (η U V Dvol lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hα : ∀ n j, μQ (α n j '' T n) =
      ENNReal.ofReal (Real.exp (ell
        (height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
          f n (center n * base n * chart n (z₀ n)))).toAdd)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hcoordinates : ∀ n j, ∀ x ∈ E n j,
      π x ∈ q₀ n j • (α n j '' T n) ∧ quotientSectionResidual π σ hs x ∈ I n)
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  obtain ⟨η', hη', _, hbase', hanchor'⟩ := exists_finite_profile_envelope
    (fun n => ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
      (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖₊)
    (fun n j => ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
      (anchorSuffix n j) (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖₊)
    η hη hbase hanchor
  let ε := fun n => ‖ell‖ * (η' n + η' n)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, add_zero, mul_zero] using (hη'.add hη').const_mul ‖ell‖
  have hαbound (n j) : μQ (α n j '' T n) ≤ ENNReal.ofReal
      (Real.exp (-ell (b₂ - b₁) * scale n + ε n * scale n)) * μQ (T n) := by
    have hb := anchor_haar_bound_of_affine_profiles height (f n) (center n) (base n)
      (anchorSuffix n j) (Real.log (scale n)) (chart n) q A b₁ b₂ (z₀ n)
      (hbase' n) (hanchor' n j) ell μQ (α n j) (T n) (hα n j)
    simpa only [Real.exp_log (hscale0 n)] using hb
  exact cone_offset_nonpos_of_lifted_cells π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    scale hscale source tiles points
    (fun n j => f n (center n * anchorSuffix n j * chart n (z₀ n))) p E B T I q₀ α
    cell hcell hcell0 hcelltop hsmall hB hp hsep hthick hcover P₁ P₂ (ell (b₂ - b₁))
    ε U V Dvol lower tileLoss hε hU hV hDvol hlower htileLoss hU0 hV0 hDvol0
    htile0 hT hI hαbound hTvol hIvol hcoordinates hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProbeRestrictionPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous two-frame restrictions for the offset packing -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- A quotient restriction in the first sheet and an ideal restriction in
the second sheet combine for the same thickened endpoints. The containing
product regions and translated quotient coordinates are constructed here. -/
theorem cone_offset_nonpos_of_probe_restrictions
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (frame : ∀ n, Fin (tiles n) → N × D)
    (hframe : ∀ n j,
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
        f n (center n * base n * chart n (z₀ n)) =
          ι (frame n j).1 * κ (frame n j).2)
    (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hfirst : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
        (x * (ι z.1 * κ z.2))) 1 ∈ T n)
    (hideal : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      quotientSectionResidual π σ hs (factorTranslate φ (p n j x) z).1 ∈ I n)
    (hD : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      (factorTranslate φ (p n j x) z).2 ∈ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (η U V Dvol lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hα : ∀ n j, μQ (actionQ (frame n j).2 '' T n) =
      ENNReal.ofReal (Real.exp (ell
        (height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
          f n (center n * base n * chart n (z₀ n)))).toAdd)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  let E := fun n j => {u : N | π u ∈ π (frame n j).1 • (actionQ (frame n j).2 '' T n) ∧
    quotientSectionResidual π σ hs u ∈ I n}
  have hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n := by
    filter_upwards [hfirst, hideal, hD] with n hnFirst hnIdeal hnD
    intro j x hx
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨?_, hnIdeal j x hx z hz⟩, hnD j x hx z hz⟩
    have hpoint : (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
        (x * (ι z.1 * κ z.2)) =
          ι (factorTranslate φ (p n j x) z).1 * κ (factorTranslate φ (p n j x) z).2 := by
      rw [← mul_assoc, ← hp n j x hx]
      exact (factorTranslate_projection φ ι κ hc (p n j x) z).symm
    exact quotient_restriction_in_anchor_frame ι κ π actionQ act hact
      (f n (center n * base n * chart n (z₀ n)))
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))
      (x * (ι z.1 * κ z.2)) (factorTranslate φ (p n j x) z).1 (frame n j).1
      (factorTranslate φ (p n j x) z).2 (frame n j).2 hpoint (hframe n j) (T n)
      (hnFirst j x hx z hz)
  exact cone_offset_nonpos_of_profile_cells π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    scale hscale hscale0 source tiles points height f center base anchorSuffix chart q z₀ A b₁ b₂
    p E B T I (fun n j => π (frame n j).1) (fun n j => (actionQ (frame n j).2).toEquiv)
    cell hcell hcell0 hcelltop hsmall hB hp hsep hthick hcover
    P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor hU hV hDvol hlower htileLoss
    hU0 hV0 hDvol0 htile0 hT hI hα hTvol hIvol (fun _ _ _ hx => hx)
    hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LowerPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FixedSlicePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing on a fixed Cartan slice

A finite net in the ambient group pulls back to a cover of the nilpotent
parameter set. Conjugation preserving Haar makes the mass of every pulled-back
ball independent of the slice position. This is the fixed-position part of
the manuscript's lower packing argument, with no assumption on an image's
absolute continuity or multiplicity.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

/-- A net of an image gives a lower cardinality bound whenever the preimage
of each covering ball has uniformly bounded mass. The source set need not be
measurable. -/
theorem exists_separated_image_net_volume_bound
    {N G : Type} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (f : N → G) {S : Set N}
    (hS : TotallyBounded (f '' S)) {r : ℝ} (hr : 0 < r) (C : ℝ≥0∞)
    (hball : ∀ y ∈ f '' S, μ (f ⁻¹' closedBall y r) ≤ C) :
    ∃ t : Finset G, (↑t : Set G) ⊆ f '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * C := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded hS hr
  refine ⟨t, ht, hsep, ?_⟩
  calc
    μ S ≤ μ (⋃ y ∈ t, f ⁻¹' closedBall y r) := measure_mono (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover (f x) ⟨x, hx, rfl⟩
      exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
    _ ≤ ∑ y ∈ t, μ (f ⁻¹' closedBall y r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, C := Finset.sum_le_sum (fun y hy => hball y (ht hy))
    _ = (t.card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MetricSpace G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)

omit [MeasurableSpace N] in
/-- Compute the entire fiber of an ambient ball on a fixed slice. The
identity-neighborhood in the nilpotent group is conjugated, then translated. -/
theorem fixedSlice_ball_preimage
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    (fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r =
      (fun n => v * φ d n) '' (ι ⁻¹' closedBall (1 : G) r) := by
  ext u
  constructor
  · intro hu
    let n := φ d⁻¹ (v⁻¹ * u)
    have hn : φ d n = v⁻¹ * u := by simp [n]
    refine ⟨n, ?_, ?_⟩
    · change dist (ι n) 1 ≤ r
      have he : (x * ι v * κ d) * ι n = x * ι u * κ d := by
        have hc := hconj d n
        rw [hn] at hc
        have hh : κ d * ι n = ι (v⁻¹ * u) * κ d := by
          rw [hc]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        calc
          (x * ι v * κ d) * ι n = x * ι v * (κ d * ι n) := by simp only [mul_assoc]
          _ = x * ι v * (ι (v⁻¹ * u) * κ d) := by rw [hh]
          _ = x * ι u * κ d := by simp [mul_assoc]
      have hd := dist_mul_left (x * ι v * κ d) (ι n) 1
      rw [he, mul_one] at hd
      exact hd ▸ hu
    · simp [hn]
  · rintro ⟨n, hn, rfl⟩
    change dist (x * ι (v * φ d n) * κ d) (x * ι v * κ d) ≤ r
    rw [map_mul, hconj]
    have he : x * (ι v * (κ d * ι n * (κ d)⁻¹)) * κ d =
        (x * ι v * κ d) * ι n := by group
    rw [he]
    calc
      dist ((x * ι v * κ d) * ι n) (x * ι v * κ d) = dist (ι n) 1 := by
        simpa only [mul_one] using dist_mul_left (x * ι v * κ d) (ι n) 1
      _ ≤ r := hn

variable [MeasurableMul N]

/-- Haar mass of a slice ball depends only on its radius. In particular it
does not grow with the Cartan position or the center of the ball. -/
theorem fixedSlice_ball_measure
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    μ ((fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) := by
  rw [fixedSlice_ball_preimage ι κ φ hconj]
  let e : N ≃ᵐ N :=
    { toEquiv :=
        { toFun := fun n => v * φ d n
          invFun := fun n => φ d⁻¹ (v⁻¹ * n)
          left_inv := by intro n; simp
          right_inv := by intro n; simp }
      measurable_toFun := (measurable_const_mul v).comp (hφ d).measurable
      measurable_invFun := (hφ d⁻¹).measurable.comp (measurable_const_mul v⁻¹) }
  have hmp : MeasurePreserving e μ μ := (measurePreserving_mul_left μ v).comp (hφ d)
  change μ (e '' _) = _
  have hm := hmp.measure_preimage_equiv (e '' (ι ⁻¹' closedBall (1 : G) r))
  rw [Set.preimage_image_eq _ e.injective] at hm
  exact hm.symm

/-- The fixed-position lower packing estimate. The only volume constant is
the Haar mass of the identity ball pulled back to the nilpotent subgroup. -/
theorem exists_fixedSlice_separated_net
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (S : Set N)
    (hS : TotallyBounded ((fun u : N => x * ι u * κ d) '' S))
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_separated_image_net_volume_bound μ _ hS hr
  rintro y ⟨v, _, rfl⟩
  exact (fixedSlice_ball_measure ι κ φ μ hφ hconj x d v r).le

variable [TopologicalSpace N] [ContinuousMul G]

omit [IsIsometricSMul G G] [MeasurableMul N] [ContinuousMul G] in
/-- A closed subgroup realization gives a finite packing constant at every
fixed radius, since the ambient metric is proper. -/
theorem fixedSlice_packing_constant_lt_top
    [ProperSpace G] (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (hι : Topology.IsClosedEmbedding ι) (r : ℝ) :
    μ (ι ⁻¹' closedBall (1 : G) r) < ⊤ :=
  (hι.isProperMap.isCompact_preimage (isCompact_closedBall 1 r)).measure_lt_top

/-- Any subset of a compact parameter set satisfies the fixed-slice lower
packing bound. Its image need not be measurable. -/
theorem exists_fixedSlice_separated_net_of_compact
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Continuous ι) (x : G) (d : D) {K S : Set N}
    (hK : IsCompact K) (hS : S ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_fixedSlice_separated_net ι κ φ μ hφ hconj x d S
  · exact ((hK.image ((continuous_const.mul hι).mul continuous_const)).totallyBounded).subset
      (image_mono hS)
  · exact hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeImageBridge
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bridge between the two actual probe images -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

variable {G W Z V : Type} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- At the same Cartan coordinate the common affine profile gives a
sublinear endpoint height, independently of its affine offset. -/
theorem basedImage_height_le_of_common_profile
    (height : G →* Multiplicative W) (f : G → G)
    (x first second : G) (r : ℝ) (chart : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z : Z)
    {ε₁ ε₂ : ℝ}
    (hfirst : ‖rescaledMapProfile (fun g => (height (f g)).toAdd) x first r chart z -
      (A (q z) + b)‖ ≤ ε₁)
    (hsecond : ‖rescaledMapProfile (fun g => (height (f g)).toAdd) x second r chart z -
      (A (q z) + b)‖ ≤ ε₂) :
    ‖(height (basedImage f (x * first * chart z) (x * second * chart z))).toAdd‖ ≤
      Real.exp r * (ε₁ + ε₂) := by
  have hh := relative_height_of_common_affine_profiles
    (fun g => (height (f g)).toAdd) x second first r chart q A b z z hsecond hfirst
  rw [basedImage_height]
  simpa only [sub_self, map_zero, smul_zero, sub_zero, add_comm] using hh

/-- Profile agreement controls the endpoint heights uniformly over a
retained family of probes, with one scale threshold for the whole family. -/
theorem eventually_uniform_probe_height_small {J : ℕ → Type}
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (x : ℕ → G) (first second : ∀ n, J n → G) (good : ∀ n, Set (J n))
    (scale ε : ℕ → ℝ) (chart : ℕ → Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z : ℕ → Z)
    (hscale : ∀ n, 0 < scale n) (hε : Tendsto ε atTop (𝓝 0))
    (hgood : ∀ᶠ n in atTop, ∀ j ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
        (x n) (first n j) (Real.log (scale n)) (chart n) (z n) -
          (A (q (z n)) + b)‖ ≤ ε n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd)
        (x n) (second n j) (Real.log (scale n)) (chart n) (z n) -
          (A (q (z n)) + b)‖ ≤ ε n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ j ∈ good n,
      ‖(height (basedImage (f n) (x n * first n j * chart n (z n))
        (x n * second n j * chart n (z n)))).toAdd‖ ≤ δ * scale n := by
  have hsmall : ∀ᶠ n in atTop, ε n + ε n ≤ δ :=
    (hε.add hε).eventually (eventually_le_nhds (by simpa using hδ))
  filter_upwards [hgood, hsmall] with n hn hεn
  intro j hj
  have hh := basedImage_height_le_of_common_profile height (f n) (x n)
    (first n j) (second n j) (Real.log (scale n)) (chart n) q A b (z n)
    (hn j hj).1 (hn j hj).2
  rw [Real.exp_log (hscale n)] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hεn (hscale n).le])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeRestrictionComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the two restrictions on the same probe endpoint -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G Q : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]

omit [Group G] [MetricSpace G] [IsIsometricSMul G G] in
/-- Choose factor lifts everywhere while retaining the simultaneous
restrictions wherever the eventual geometric construction applies. -/
theorem choose_eventual_probe_lifts {J : ℕ → Type}
    (project : N × D → G) (hsurj : Function.Surjective project)
    (endpoint : ∀ n, J n → G → G) (points : ∀ n, J n → Finset G)
    (P : ∀ n, J n → G → N × D → Prop)
    (h : ∀ᶠ n in Filter.atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p, project p = endpoint n j x ∧ P n j x p) :
    ∃ p : ∀ n, J n → G → N × D,
      (∀ n j x, project (p n j x) = endpoint n j x) ∧
      ∀ᶠ n in Filter.atTop, ∀ j, ∀ x ∈ points n j, P n j x (p n j x) := by
  classical
  let good := fun n => ∀ j, ∀ x ∈ points n j,
    ∃ p, project p = endpoint n j x ∧ P n j x p
  have hp (n : ℕ) (j : J n) (x : G) :
      ∃ p, project p = endpoint n j x ∧ (good n → x ∈ points n j → P n j x p) := by
    by_cases hg : good n
    · by_cases hx : x ∈ points n j
      · obtain ⟨p, he, hP⟩ := hg j x hx
        exact ⟨p, he, fun _ _ => hP⟩
      · obtain ⟨p, he⟩ := hsurj (endpoint n j x)
        exact ⟨p, he, fun _ hmem => (hx hmem).elim⟩
    · obtain ⟨p, he⟩ := hsurj (endpoint n j x)
      exact ⟨p, he, fun hg' => (hg hg').elim⟩
  choose p he hP using hp
  refine ⟨p, he, ?_⟩
  filter_upwards [h] with n hn
  intro j x hx
  exact hP n j x hn hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredProbeOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality from measured, eventual probe lifts -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Actual simultaneous probe restrictions and the quotient Haar character
force the affine offset sign. Factor lifts and tile frames are chosen here;
no independent compatibility premise about these choices is required. -/
theorem cone_offset_nonpos_of_measured_probe_lifts
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (hlifts : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p : N × D,
        ι p.1 * κ p.2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x ∧
        ∀ z ∈ cell,
          act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
            (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (η U V Dvol lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  classical
  let start := fun n j => f n (center n * anchorSuffix n j * chart n (z₀ n))
  let origin := fun n => f n (center n * base n * chart n (z₀ n))
  let P := fun (n : ℕ) (j : Fin (tiles n)) (x : G) (p : N × D) => ∀ z ∈ cell,
    act ((origin n)⁻¹ * (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
    quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
    (factorTranslate φ p z).2 ∈ B n
  obtain ⟨p, hp, hrestr⟩ := choose_eventual_probe_lifts
    (fun p : N × D => ι p.1 * κ p.2) hsurj
    (fun n j x => (start n j)⁻¹ * x) points P hlifts
  have hf : ∀ n j, ∃ frame : N × D,
      ι frame.1 * κ frame.2 = (start n j)⁻¹ * origin n :=
    fun n j => hsurj _
  choose frame hframe using hf
  have hfirst : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      act ((origin n)⁻¹ * (x * (ι z.1 * κ z.2))) 1 ∈ T n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).1)
  have hideal : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      quotientSectionResidual π σ hs (factorTranslate φ (p n j x) z).1 ∈ I n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).2.1)
  have hD : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      (factorTranslate φ (p n j x) z).2 ∈ B n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).2.2)
  have hα (n j) : μQ (actionQ (frame n j).2 '' T n) =
      ENNReal.ofReal (Real.exp (ell (height ((start n j)⁻¹ * origin n)).toAdd)) * μQ (T n) := by
    have he : act ((start n j)⁻¹ * origin n) '' T n =
        π (frame n j).1 • (actionQ (frame n j).2 '' T n) := by
      rw [← hframe n j, ← Set.image_smul, Set.image_image]
      congr 1
      funext q
      exact hact _ _ q
    have hh := hHaar ((start n j)⁻¹ * origin n) (T n)
    rw [he, measure_smul] at hh
    exact hh
  exact cone_offset_nonpos_of_probe_restrictions π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 source tiles points height f center base anchorSuffix
    chart q z₀ A b₁ b₂ p frame (fun n j => (hframe n j).symm) B T I
    cell hcell hcell0 hcelltop hsmall hB (fun n j x _ => hp n j x) hsep
    hfirst hideal hD hcover P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor
    hU hV hDvol hlower htileLoss hU0 hV0 hDvol0 htile0 hT hI hα hTvol hIvol hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredTwoPathOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality from measured, eventual probe lifts -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Two actual controlled paths, a short image bridge and a small second
endpoint height suffice for the offset sign after measured probe packing. -/
theorem cone_offset_nonpos_of_measured_two_paths
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (hpaths : ∀ᶠ n in atTop, ∀ (basePoint anchorPoint first second : G)
      (path₁ : Path (1 : G) (basePoint⁻¹ * first))
      (path₂ : Path (1 : G) (anchorPoint⁻¹ * second)),
      PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      ‖(height (anchorPoint⁻¹ * second)).toAdd‖ ≤ δ * scale n →
      dist second first ≤ δ * scale n →
      ∃ p : N × D, ι p.1 * κ p.2 = anchorPoint⁻¹ * first ∧
        ∀ z ∈ cell,
          act (basePoint⁻¹ * (first * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n)
    (hgeometry : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ (second : G)
        (path₁ : Path (1 : G) ((f n (center n * base n * chart n (z₀ n)))⁻¹ * x))
        (path₂ : Path (1 : G) ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        ‖(height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)).toAdd‖ ≤
          δ * scale n ∧ dist second x ≤ δ * scale n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (U V Dvol lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  have hlifts : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p : N × D,
        ι p.1 * κ p.2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x ∧
        ∀ z ∈ cell,
          act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
            (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n := by
    filter_upwards [hpaths, hgeometry] with n hn hg
    intro j x hx
    obtain ⟨second, path₁, path₂, hm₁, hm₂, hh₁, hh₂, hs, hd⟩ := hg j x hx
    exact hn _ _ x second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hs hd
  exact cone_offset_nonpos_of_measured_probe_lifts π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 source tiles points height f center base anchorSuffix
    chart q z₀ A b₁ b₂ B T I cell hcell hcell0 hcelltop hsmall hB hsep hsurj hlifts
    hcover P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor
    hU hV hDvol hlower htileLoss hU0 hV0 hDvol0 htile0 hT hI hHaar hTvol hIvol hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredRegionOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality from measured, eventual probe lifts -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Apply the offset count directly to the measured regions produced by
Cartan path lifting. All quotient, ideal and Cartan volume bounds are read
from those regions; only the source counts and actual paths are supplied. -/
theorem MeasuredProbeRegions.offset_nonpos_of_two_paths
    (π : N →* Q) (hπ : Continuous π)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (R : MeasuredProbeRegions π μQ μI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ
      R.sectionMap R.section_rightInverse).symm (μQ.prod μI))
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell E₁ E₂ η Apath Bpath δ n)
    (hgeometry : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ (second : G)
        (path₁ : Path (1 : G) ((f n (center n * base n * chart n (z₀ n)))⁻¹ * x))
        (path₂ : Path (1 : G) ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        ‖(height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)).toAdd‖ ≤
          δ * scale n ∧ dist second x ≤ δ * scale n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ : ℝ) (ell : W →L[ℝ] ℝ) (lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  have hpaths' : ∀ᶠ n in atTop, ∀ (basePoint anchorPoint first second : G)
      (path₁ : Path (1 : G) (basePoint⁻¹ * first))
      (path₂ : Path (1 : G) (anchorPoint⁻¹ * second)),
      PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      ‖(height (anchorPoint⁻¹ * second)).toAdd‖ ≤ δ * scale n →
      dist second first ≤ δ * scale n →
      ∃ p : N × D, ι p.1 * κ p.2 = anchorPoint⁻¹ * first ∧
        ∀ z ∈ cell,
          act (basePoint⁻¹ * (first * (ι z.1 * κ z.2))) 1 ∈ R.quotientRegion n ∧
          quotientSectionResidual π R.sectionMap R.section_rightInverse
            (factorTranslate φ p z).1 ∈ R.idealRegion n ∧
          (factorTranslate φ p z).2 ∈ R.cartanRegion n := by
    filter_upwards [hpaths] with n hn
    intro basePoint anchorPoint first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hs hd
    obtain ⟨u, d, he, hc⟩ := hn basePoint anchorPoint first second path₁ path₂
      hm₁ hm₂ hh₁ hh₂ hs hd
    exact ⟨(u, d), he, hc⟩
  exact cone_offset_nonpos_of_measured_two_paths π hπ R.sectionMap R.section_rightInverse
    μQ μI μ ν hμ φ ι κ hc hφ actionQ act hact scale hscale hscale0
    source tiles points height f center base anchorSuffix chart q z₀ A b₁ b₂
    R.cartanRegion R.quotientRegion R.idealRegion cell hcell hcell0 hcelltop hsmall
    R.cartan_finite hsep hsurj η δ Apath Bpath E₁ E₂ hpaths' hgeometry
    hcover P₁ P₂ ell (fun n => (μQ (R.quotientRegion n)).toReal) R.idealLoss
    (fun n => (ν (R.cartanRegion n)).toReal) lower tileLoss hη hbase hanchor
    R.quotient_subexponential R.ideal_subexponential R.cartan_subexponential
    hlower htileLoss (fun _ => ENNReal.toReal_nonneg) R.idealLoss_nonneg
    (fun _ => ENNReal.toReal_nonneg) htile0 R.quotient_finite R.ideal_finite hHaar
    (fun _ => le_rfl) (fun n => (R.ideal_volume n).le) (fun _ => le_rfl) hsource htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeImageGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual good probes supply the two-path packing geometry -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology NNReal

variable {G W V Z : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [AddCommGroup V] [Module ℝ V]

omit [IsIsometricSMul G G] in
/-- A finite image cover retains the witness needed to use the two actual
paths. The second endpoint height is derived from its common affine profile;
the image bridge is derived from the source bridge and the Lipschitz bound. -/
theorem probe_image_two_path_geometry
    {Y : ℕ → Type} (good : ∀ n, Set (Y n)) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n)) (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchor : ∀ n, Fin (tiles n) → G)
    (first second : ∀ n, Y n → G) (scale η : ℕ → ℝ)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b : W) (E₁ E₂ : Set W)
    (L B δ D : ℝ) (Λ : ℝ≥0)
    (hscale : ∀ n, 0 < scale n) (hη : Tendsto η atTop (𝓝 0))
    (hδ : 0 < δ) (hLip : ∀ n, LipschitzWith Λ (f n)) (hD : (Λ : ℝ) * D ≤ δ)
    (hpoint : ∀ n j x, x ∈ points n j → ∃ y ∈ good n,
      tile n y = j ∧ f n (center n * first n y * chart n (z₀ n)) = x)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (anchor n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ D * scale n)
    (hpaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (f n)
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (f n)
          (center n * anchor n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n)))) :
    ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ (secondPoint : G)
        (path₁ : Path (1 : G) ((f n (center n * base n * chart n (z₀ n)))⁻¹ * x))
        (path₂ : Path (1 : G)
          ((f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint)),
        PathMetricBound path₁ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        ‖(height ((f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint)).toAdd‖ ≤
          δ * scale n ∧ dist secondPoint x ≤ δ * scale n := by
  have hheight := eventually_uniform_probe_height_small height f center
    (fun n y => anchor n (tile n y)) second good scale η chart q A b z₀
    hscale hη hprofiles hδ
  filter_upwards [hheight, hbridge, hpaths] with n hnheight hnbridge hnpaths
  intro j x hx
  obtain ⟨y, hy, rfl, rfl⟩ := hpoint n j x hx
  obtain ⟨p₁, p₂, hm₁, hm₂, hh₁, hh₂⟩ := hnpaths y hy
  refine ⟨f n (center n * second n y * chart n (z₀ n)), p₁, p₂,
    hm₁, hm₂, hh₁, hh₂, hnheight y hy, ?_⟩
  calc
    _ ≤ (Λ : ℝ) * dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) := (hLip n).dist_le_mul _ _
    _ ≤ (Λ : ℝ) * (D * scale n) :=
      mul_le_mul_of_nonneg_left (hnbridge y hy) Λ.coe_nonneg
    _ = ((Λ : ℝ) * D) * scale n := (mul_assoc _ _ _).symm
    _ ≤ δ * scale n := mul_le_mul_of_nonneg_right hD (hscale n).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeImageTileCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tile covers retaining the actual good-probe witnesses -/

namespace PolycyclicRecognition

/-- Image collisions need not have a preferred inverse. A finite image
set is covered by the images of its good-probe tiles, with a witness in
the original retained set for every tile membership. -/
theorem exists_probe_image_tile_cover {Y G : Type} {m : ℕ}
    (K : Set Y) (image : Y → G) (tile : Y → Fin m) (source : Finset G)
    (hsource : (source : Set G) ⊆ image '' K) :
    ∃ points : Fin m → Finset G,
      (∀ j, points j ⊆ source) ∧
      (∀ x ∈ source, ∃ j, x ∈ points j) ∧
      ∀ j x, x ∈ points j ↔ x ∈ source ∧ ∃ y ∈ K, tile y = j ∧ image y = x := by
  classical
  let points := fun j => source.filter (fun x => ∃ y ∈ K, tile y = j ∧ image y = x)
  refine ⟨points, fun _ => Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, he⟩ := hsource hx
    exact ⟨tile y, Finset.mem_filter.mpr ⟨hx, y, hy, rfl, he⟩⟩
  · intro j x
    exact Finset.mem_filter

/-- The same construction simultaneously chooses the finite tile cover
at every scale of the probe sequence. -/
theorem exists_probe_image_tile_cover_sequence {Y : ℕ → Type} {G : Type}
    (K : ∀ n, Set (Y n)) (image : ∀ n, Y n → G) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n)) (source : ℕ → Finset G)
    (hsource : ∀ n, (source n : Set G) ⊆ image n '' K n) :
    ∃ points : ∀ n, Fin (tiles n) → Finset G,
      (∀ n j, points n j ⊆ source n) ∧
      (∀ n x, x ∈ source n → ∃ j, x ∈ points n j) ∧
      ∀ n j x, x ∈ points n j ↔
        x ∈ source n ∧ ∃ y ∈ K n, tile n y = j ∧ image n y = x := by
  classical
  choose points hsub hcover hpoint using fun n =>
    exists_probe_image_tile_cover (K n) (image n) (tile n) (source n) (hsource n)
  exact ⟨points, hsub, hcover, hpoint⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RetainedProbeAnchors
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the good anchors needed by measured packing -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set

theorem occupiedTileAnchor_eq {G X : Type} {m : ℕ}
    (points : Fin m → Finset X) (anchor : Fin m → G) (fallback : G)
    {j : Fin m} {x : X} (hx : x ∈ points j) :
    occupiedTileAnchor points anchor fallback j = anchor j := by
  simp [occupiedTileAnchor, show (points j).Nonempty from ⟨x, hx⟩]

/-- The simultaneous good-probe estimate extends to every tile after
replacing empty tiles. This supplies the all-anchor premise of packing
without requiring unselected anchors to have good profiles. -/
theorem occupiedTileAnchor_profile_bound
    {G X W : Type} [NormedAddCommGroup W]
    {Y : ℕ → Type} (good : ∀ n, Set (Y n)) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n))
    (points : ∀ n, Fin (tiles n) → Finset X)
    (anchor : ∀ n, Fin (tiles n) → G) (fallback : ℕ → G)
    (profile : ℕ → G → W) (target : ℕ → W) (ε : ℕ → ℝ)
    (hwitness : ∀ n j x, x ∈ points n j → ∃ y ∈ good n, tile n y = j)
    (hfallback : ∀ᶠ n in atTop, ‖profile n (fallback n) - target n‖ ≤ ε n)
    (hgood : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖profile n (anchor n (tile n y)) - target n‖ ≤ ε n) :
    ∀ᶠ n in atTop, ∀ j,
      ‖profile n (occupiedTileAnchor (points n) (anchor n) (fallback n) j) - target n‖ ≤ ε n := by
  filter_upwards [hfallback, hgood] with n hn hgoodn
  intro j
  by_cases h : (points n j).Nonempty
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy, he⟩ := hwitness n j x hx
    rw [occupiedTileAnchor_eq _ _ _ hx, ← he]
    exact hgoodn y hy
  · simpa [occupiedTileAnchor, h] using hn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredGoodProbeOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measured offset inequality from retained good probes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators NNReal

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Apply the measured two-path argument to the retained good probes.
The actual source bridge and the common second-sheet profile give the
short target bridge. Empty tiles use the original neighboring anchor,
so only selected anchors require the good-profile estimate. -/
theorem MeasuredProbeRegions.offset_nonpos_of_good_probes
    (π : N →* Q) (hπ : Continuous π)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (R : MeasuredProbeRegions π μQ μI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ
      R.sectionMap R.section_rightInverse).symm (μQ.prod μI))
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    {Y : ℕ → Type} (good : ∀ n, Set (Y n))
    (tile : ∀ n, Y n → Fin (tiles n))
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (fallback : ℕ → G) (first second : ∀ n, Y n → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (Dbridge : ℝ) (Λ : ℝ≥0) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (f n)) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell E₁ E₂ η Apath Bpath δ n)
    (hpoint : ∀ n j x, x ∈ points n j → ∃ y ∈ good n,
      tile n y = j ∧ f n (center n * first n y * chart n (z₀ n)) = x)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (anchorSuffix n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (f n)
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (f n)
          (center n * anchorSuffix n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))))
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ : ℝ) (ell : W →L[ℝ] ℝ) (lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hfallback : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (fallback n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  let anchor := fun n => occupiedTileAnchor (points n) (anchorSuffix n) (fallback n)
  have hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchor n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n := by
    have hwitness : ∀ n j x, x ∈ points n j → ∃ y ∈ good n, tile n y = j := by
      intro n j x hx
      obtain ⟨y, hy, hj, _⟩ := hpoint n j x hx
      exact ⟨y, hy, hj⟩
    exact occupiedTileAnchor_profile_bound good tiles tile points anchorSuffix fallback
      (fun n g => rescaledMapProfile (fun x => (height (f n x)).toAdd) (center n) g
        (Real.log (scale n)) (chart n) (z₀ n))
      (fun n => A (q (z₀ n)) + b₂) η hwitness hfallback
      (hprofiles.mono (fun _ hn y hy => (hn y hy).1))
  have hgeometry := probe_image_two_path_geometry good tiles tile points height f
    center base anchorSuffix first second scale η chart q z₀ A b₂ E₁ E₂
    Apath Bpath δ Dbridge Λ hscale0 hη hδ hLip hD hpoint hprofiles hbridge hprobePaths
  apply R.offset_nonpos_of_two_paths π hπ μQ μI μ ν φ ι κ hc hφ actionQ act hact
    scale hscale hscale0 P₂ hμ source tiles points height f center base anchor
    chart q z₀ A b₁ b₂ cell hcell hcell0 hcelltop hsmall hsep hsurj
    η δ Apath Bpath E₁ E₂ hpaths _ hcover P₁ ell lower tileLoss
    hη hbase hanchor hlower htileLoss htile0 hHaar hsource htiles
  filter_upwards [hgeometry] with n hn
  intro j x hx
  obtain ⟨secondPoint, p₁, p₂, hm₁, hm₂, hh₁, hh₂, hs, hd⟩ := hn j x hx
  have ha : anchor n j = anchorSuffix n j := occupiedTileAnchor_eq _ _ _ hx
  have he : (f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint =
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * secondPoint := by rw [ha]
  refine ⟨secondPoint, p₁, p₂.cast rfl he, hm₁, hm₂.cast rfl he, hh₁, hh₂, ?_, hd⟩
  rw [he]
  exact hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeCellVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive probe probabilities give actual endpoint volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- A positive fraction of the original cell becomes a corresponding
amount of actual volume under the section-coordinate embedding. -/
theorem probe_cell_image_volume_lower
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X → Y) (he : MeasurableEmbedding e)
    (A K : Set X) (hA0 : μ A ≠ 0) (hAt : μ A ≠ ⊤)
    (hK : MeasurableSet K) (hKA : K ⊆ A)
    {c : ℝ} (hc : 0 ≤ c)
    (hmass : ENNReal.ofReal c ≤ (cellProbabilityMeasure μ A hA0 hAt : Measure X) K) :
    c * (μ A).toReal ≤ ((Measure.map e μ) (e '' K)).toReal := by
  have hm := ENNReal.toReal_mono (measure_ne_top
    (cellProbabilityMeasure μ A hA0 hAt : Measure X) K) hmass
  rw [ENNReal.toReal_ofReal hc, cellProbabilityMeasure_apply_toReal μ A K hA0 hAt hK,
    inter_eq_left.mpr hKA] at hm
  have hvol := (le_div_iff₀ (ENNReal.toReal_pos hA0 hAt)).mp hm
  simpa only [he.map_apply, preimage_image_eq _ he.injective] using hvol

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeSourcePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated source counts for the retained probe volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {N D G : Type} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
  (hι : Topology.IsClosedEmbedding ι)
  (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)

include hι hφ hconj

/-- Positive probe volume supplies genuinely separated image endpoints.
The constant is independent of the source sheet, its Cartan pivot, the
normalized map and the point at which its image is centered. -/
theorem exists_fixedSlice_image_net_constant
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : NormalizedPair G Λ) (x a : G) (d : D)
      (S : Set N), IsCompact S →
      ∃ t : Finset G,
        (↑t : Set G) ⊆ (fun n => basedImage p.val.1 a (x * ι n * κ d)) '' S ∧
        (∀ u ∈ t, ∀ v ∈ t, u ≠ v → 1 ≤ dist u v) ∧
        c * (μ S).toReal ≤ (t.card : ℝ) := by
  classical
  let ρ := (Λ : ℝ) * ((Λ : ℝ) + 1)
  have hρ : 0 < ρ := mul_pos hΛ (by positivity)
  let C := μ (ι ⁻¹' closedBall (1 : G) ρ)
  have hC : C ≠ ⊤ := (fixedSlice_packing_constant_lt_top ι μ hι ρ).ne
  let c := 1 / (C.toReal + 1)
  have hden : 0 < C.toReal + 1 := by positivity
  refine ⟨c, div_pos zero_lt_one hden, ?_⟩
  intro p x a d S hS
  obtain ⟨s, hs, hsep, hmass⟩ := exists_fixedSlice_separated_net_of_compact
    ι κ φ μ hφ hconj hι.continuous x d hS (Subset.refl S) hρ
  obtain ⟨hcard, hsep'⟩ := basedImage_separated_card p hΛ a s hsep
  refine ⟨s.image (basedImage p.val.1 a), ?_, hsep', ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨n, hn, rfl⟩ := hs hv
    exact ⟨n, hn, rfl⟩
  · have hm := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hC) hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hm
    rw [hcard]
    have hm' : (μ S).toReal ≤ (s.card : ℝ) * (C.toReal + 1) := by
      calc
        _ ≤ (s.card : ℝ) * C.toReal := hm
        _ ≤ (s.card : ℝ) * (C.toReal + 1) := by gcongr; linarith
    dsimp only [c]
    calc
      (1 / (C.toReal + 1)) * (μ S).toReal = (μ S).toReal / (C.toReal + 1) := by ring
      _ ≤ (s.card : ℝ) := (div_le_iff₀ hden).mpr hm'

/-- A quarter of the original probe cell yields the full source exponent,
uniformly over a sequence of maps, centers and moving Cartan pivots. -/
theorem exists_probe_source_count_sequence
    {P : Type} [TopologicalSpace P] [MeasurableSpace P]
    (ν : Measure P) (e : ℕ → P → N)
    (he : ∀ n, MeasurableEmbedding (e n)) (hec : ∀ n, Continuous (e n))
    (hμ : ∀ n, μ = Measure.map (e n) ν)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x a : ℕ → G) (d : ℕ → D) (A K : ℕ → Set P)
    (hA0 : ∀ n, ν (A n) ≠ 0) (hAt : ∀ n, ν (A n) ≠ ⊤)
    (hK : ∀ n, IsCompact (K n)) (hKm : ∀ n, MeasurableSet (K n))
    (hKA : ∀ n, K n ⊆ A n)
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure ν (A n) (hA0 n) (hAt n) : Measure P) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (ν (A n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y => basedImage (p n).val.1 (a n) (x n * ι (e n y) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_fixedSlice_image_net_constant
    ι κ φ μ hι hφ hconj hΛ
  have ht (n : ℕ) : ∃ t : Finset G,
      (↑t : Set G) ⊆
        (fun y => basedImage (p n).val.1 (a n) (x n * ι (e n y) * κ (d n))) '' K n ∧
      (∀ u ∈ t, ∀ w ∈ t, u ≠ w → 1 ≤ dist u w) ∧
      (c * v / 4) * Real.exp (scale n * P₁) ≤ (t.card : ℝ) := by
    obtain ⟨t, ht, hsep, hcard⟩ := hcount (p n) (x n) (a n) (d n)
      (e n '' K n) ((hK n).image (hec n))
    have hm := probe_cell_image_volume_lower ν (e n) (he n) (A n) (K n)
      (hA0 n) (hAt n) (hKm n) (hKA n) (by norm_num : (0 : ℝ) ≤ 1 / 4) (hmass n)
    rw [← hμ n] at hm
    refine ⟨t, ?_, hsep, ?_⟩
    · simpa only [image_image, Function.comp_def] using ht
    · calc
        (c * v / 4) * Real.exp (scale n * P₁) =
            c * ((1 / 4) * (v * Real.exp (scale n * P₁))) := by ring
        _ ≤ c * ((1 / 4) * (ν (A n)).toReal) := by gcongr; exact hvol n
        _ ≤ c * (μ (e n '' K n)).toReal := mul_le_mul_of_nonneg_left hm hc.le
        _ ≤ (t.card : ℝ) := hcard
  choose source hsub hsep hcount using ht
  exact ⟨c * v / 4, source, by positivity, hsub, hsep, hcount⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionProbePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source counts in the actual dilated ideal-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal Pointwise

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology N] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- The original product probe measure, the moving scalar dilation, and
fixed-pivot metric packing give one source exponent with a uniform positive
constant. The retained mass is measured before choosing its base sample. -/
theorem exists_dilated_section_probe_counts
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N)) (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm (μQ.prod μI))
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hι : Topology.IsClosedEmbedding ι)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μ μ)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x a : ℕ → G) (d : ℕ → D)
    (Z : Set Q) (J : ℕ → Set π.ker)
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ℕ → Set (Q × π.ker))
    (hK : ∀ n, IsCompact (K n)) (hKm : ∀ n, MeasurableSet (K n))
    (hKsub : ∀ n, K n ⊆ Z ×ˢ J n)
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure (μQ.prod μI) (Z ×ˢ J n)
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Q × π.ker)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Q × π.ker => basedImage (p n).val.1 (a n)
          (x n * ι (S n ((y.2 : N) * σ y.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  let chart := quotientSectionHomeomorph π hπ σ hs
  let e := fun n => chart.symm.trans (S n)
  have he (n : ℕ) : MeasurableEmbedding (e n) := (e n).measurableEmbedding
  have heμ (n : ℕ) : μ = Measure.map (e n) (μQ.prod μI) := by
    change μ = Measure.map ((S n) ∘ chart.symm) (μQ.prod μI)
    rw [← Measure.map_map (S n).measurable chart.symm.measurable, ← hμ]
    exact (hS n).map_eq.symm
  have hA0 (n : ℕ) : (μQ.prod μI) (Z ×ˢ J n) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hZ0 (hJ0 n)
  have hAt (n : ℕ) : (μQ.prod μI) (Z ×ˢ J n) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hZt (hJt n)
  have hq : 0 < (μQ Z).toReal := ENNReal.toReal_pos hZ0 hZt
  have hv' : 0 < (μQ Z).toReal * v := mul_pos hq hv
  have hvol' (n : ℕ) : ((μQ Z).toReal * v) * Real.exp (scale n * P₁) ≤
      ((μQ.prod μI) (Z ×ˢ J n)).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hvol n) hq.le
  obtain ⟨c, source, hc, hsub, hsep, hcount⟩ := exists_probe_source_count_sequence
    ι κ φ μ hι hφ hconj (μQ.prod μI) (fun n => e n) he (fun n => (e n).continuous) heμ
    hΛ p x a d (fun n => Z ×ˢ J n) K hA0 hAt hK hKm hKsub hmass scale P₁ hv' hvol'
  exact ⟨c, source, hc, hsub, hsep, hcount⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionSubtypeProbePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source counts for the compact subtype probes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal Pointwise

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology N] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]


variable [T2Space N] [T2Space Q]

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- Compact good probes selected on the original product cell give the
actual separated image count. Their subtype probability is transported
exactly; the choice of starting sample causes no loss of source volume. -/
theorem exists_dilated_section_subtype_probe_counts
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N)) (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm (μQ.prod μI))
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hι : Topology.IsClosedEmbedding ι)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μ μ)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x a : ℕ → G) (d : ℕ → D)
    (Z : Set Q) (J : ℕ → Set π.ker)
    (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ∀ n, Set (Z ×ˢ J n)) (hK : ∀ n, IsCompact (K n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQ.prod μI) (Z ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Z ×ˢ J n)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Z ×ˢ J n => basedImage (p n).val.1 (a n)
          (x n * ι (S n ((y.val.2 : N) * σ y.val.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  let ambientK := fun n => Subtype.val '' K n
  have hproperties (n) := cellSubtypeProbability_compact_image (μQ.prod μI)
    (Z ×ˢ J n) (hZm.prod (hJm n))
    (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) (K n) (hK n)
  have hmass' (n) : ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure (μQ.prod μI) (Z ×ˢ J n)
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Q × π.ker)) (ambientK n) := by
    rw [(hproperties n).2.2.2]
    exact hmass n
  obtain ⟨c, source, hc, hsource, hsep, hcount⟩ := exists_dilated_section_probe_counts
    π hπ σ hs μQ μI μ hμ ι κ φ hι hφ hconj S hS hΛ p x a d Z J hZ0 hZt hJ0 hJt
    ambientK (fun n => (hproperties n).1) (fun n => (hproperties n).2.1)
    (fun n => (hproperties n).2.2.1) hmass' scale P₁ hv hvol
  refine ⟨c, source, hc, ?_, hsep, hcount⟩
  intro n
  simpa only [ambientK, image_image] using hsource n

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- For normalized quasi-isometries the source net consists of the actual
image points. The count and separation are unchanged, and the image
witnesses now match the two-path offset theorem directly. -/
theorem exists_absolute_section_subtype_probe_counts
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N)) (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm (μQ.prod μI))
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hι : Topology.IsClosedEmbedding ι)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μ μ)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x : ℕ → G) (d : ℕ → D)
    (Z : Set Q) (J : ℕ → Set π.ker)
    (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ∀ n, Set (Z ×ˢ J n)) (hK : ∀ n, IsCompact (K n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQ.prod μI) (Z ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Z ×ˢ J n)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Z ×ˢ J n => (p n).val.1
          (x n * ι (S n ((y.val.2 : N) * σ y.val.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  obtain ⟨c, source, hc, hsource, hsep, hcount⟩ := exists_dilated_section_subtype_probe_counts
    π hπ σ hs μQ μI μ hμ ι κ φ hι hφ hconj S hS hΛ p x (fun _ => 1) d
    Z J hZm hJm hZ0 hZt hJ0 hJt K hK hmass scale P₁ hv hvol
  refine ⟨c, source, hc, ?_, hsep, hcount⟩
  intro n
  simpa only [basedImage, (p n).property.2, inv_one, one_mul] using hsource n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IndependentConditionedOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset comparison with different source and target cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators NNReal

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G] [ProperSpace G]
  [T2Space N] [T2Space Q]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

omit [T2Space Q] in
/-- Source counting uses the original polar-cone quotient; target restrictions
use its transformed cone. Their Haar products need not have the same quotient
or normalization. The source translation retains the original profile center. -/
theorem MeasuredProbeRegions.offset_nonpos_of_independent_conditioned_probes
    (π : N →* Q) (hπ : Continuous π)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (R : MeasuredProbeRegions π μQ μI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ
      R.sectionMap R.section_rightInverse).symm (μQ.prod μI))
    {QS : Type} [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS]
    [T2Space QS] [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
    (πS : N →* QS) (hπS : Continuous πS)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure N)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (φ d) μS μS)
    (σ : C(QS, N)) (hσ : ∀ q, πS (σ q) = q)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σ hσ).symm
      (μQS.prod μIS))
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μS μS)
    (hι : Topology.IsClosedEmbedding ι)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (d : ℕ → D) (ZQ : Set QS) (J : ℕ → Set πS.ker)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (good : ∀ n, Set (ZQ ×ˢ J n)) (hgood : ∀ n, IsCompact (good n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)) (good n))
    (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ)
    (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (height : G →* Multiplicative W)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (fallback : ℕ → G) (first second : ∀ n, (ZQ ×ˢ J n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (translation : ℕ → N)
    (hfirst : ∀ n y, first n y = ι (translation n) * ι (S n
      ((y.val.2 : N) * σ y.val.1)))
    (hchart : ∀ n, chart n (z₀ n) = κ (d n))
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (Dbridge : ℝ) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (p n).val.1) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell E₁ E₂ η Apath Bpath δ n)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (anchorSuffix n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (p n).val.1
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (p n).val.1
          (center n * anchorSuffix n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))))
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hfallback : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n) (fallback n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  classical
  obtain ⟨lower, source, hlower, hsource, hsep, hcount⟩ :=
    exists_absolute_section_subtype_probe_counts πS hπS σ hσ
      μQS μIS μS hμS ι κ φ hι hφS hc S hS hΛ p
      (fun n => center n * ι (translation n)) d ZQ J
      hZm hJm hZ0 hZt hJ0 hJt good hgood hmass scale P₁ hv hvol
  let image := fun n (y : ZQ ×ˢ J n) =>
    (p n).val.1 (center n * first n y * chart n (z₀ n))
  have hsource' : ∀ n, (source n : Set G) ⊆ image n '' good n := by
    intro n
    simpa only [image, hfirst, hchart, mul_assoc] using hsource n
  obtain ⟨points, hsub, hcover, hpoint⟩ :=
    exists_probe_image_tile_cover_sequence good image tiles tile source hsource'
  apply R.offset_nonpos_of_good_probes π hπ μQ μI μ ν φ ι κ hc hφ actionQ act hact
    scale hscale hscale0 P₂ hμ source tiles points good tile height (fun n => (p n).val.1)
    center base anchorSuffix fallback first second chart q z₀ A b₁ b₂
    cell hcell hcell0 hcelltop hsmall
    (fun n j x hx y hy hxy => hsep n x (hsub n j hx) y (hsub n j hy) hxy)
    hsurj η δ Apath Bpath E₁ E₂ Dbridge Λ hδ hLip hD hpaths
    (fun n j x hx => ((hpoint n j x).mp hx).2) hprofiles hbridge hprobePaths
    hcover P₁ ell (fun _ => lower) tileLoss hη hbase hfallback
    (sequence_subexponential_lower_const hscale hlower) htileLoss htile0 hHaar
    (Eventually.of_forall hcount) htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinkedProbeOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The offset inequality from the actual three linked probe chains -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators NNReal

variable {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G] [ProperSpace G]
  [T2Space N] [T2Space Q]


variable {W V Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

omit [T2Space Q] in
/-- Insert the three actual linked chains into the independent-quotient
volume comparison. The first and third chains supply the image paths; the
second supplies the retained anchor profile. All profiles retain their
original center, and their common error is derived from the chain bounds. -/
theorem MeasuredProbeRegions.offset_nonpos_of_linked_probe_bounds
    (π : N →* Q) (hπ : Continuous π)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (R : MeasuredProbeRegions π μQ μI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ
      R.sectionMap R.section_rightInverse).symm (μQ.prod μI))
    {QS : Type} [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS]
    [T2Space QS] [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
    (πS : N →* QS) (hπS : Continuous πS)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure N)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (φ d) μS μS)
    (σ : C(QS, N)) (hσ : ∀ q, πS (σ q) = q)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σ hσ).symm
      (μQS.prod μIS))
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μS μS)
    (hι : Topology.IsClosedEmbedding ι)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (d : ℕ → D) (ZQ : Set QS) (J : ℕ → Set πS.ker)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (good : ∀ n, Set (ZQ ×ˢ J n)) (hgood : ∀ n, IsCompact (good n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)) (good n))
    (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ)
    (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (height : G →* Multiplicative W)
    (center : ℕ → G) (sample origin neighbor : ℕ → N)
    (anchorRoot : ∀ n, Fin (tiles n) → N) (secondRoot : ∀ n, (ZQ ×ˢ J n) → N)
    (length : Fin 3 → ℕ)
    (vertex : ∀ k n, (ZQ ×ˢ J n) → Fin (length k + 1) → N)
    (hstart : ∀ n y, vertex 0 n y 0 = origin n)
    (hthird : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (length 1)))
    (hfirst : ∀ n y, vertex 0 n y (Fin.last (length 0)) =
      origin n * S n ((y.val.2 : N) * σ y.val.1))
    (hanchor : ∀ n y, vertex 1 n y (Fin.last (length 1)) = anchorRoot n (tile n y))
    (hsecond : ∀ n y, vertex 2 n y (Fin.last (length 2)) = secondRoot n y)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b : Bool → W)
    (hchart : ∀ n, chart n (z₀ n) = κ (d n))
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (δ C Dbridge : ℝ) (E : Fin 3 → Set W) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (p n).val.1) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell (E 0) (E 2)
      (fun n => 2 * η n) C C δ n)
    (hbaseProfiles : ∀ᶠ n in atTop, ∀ s : Bool,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (ι (sample n * if s then neighbor n else origin n)) (Real.log (scale n))
        (chart n) (z₀ n) - (A (q (z₀ n)) + b s)‖ ≤ η n)
    (hprefixProfiles : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ k j,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (ι (sample n * vertex k n y j)) (Real.log (scale n))
        (chart n) (z₀ n) - (A (q (z₀ n)) + b (k != 0))‖ ≤ 2 * η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * ι (sample n * secondRoot n y) * chart n (z₀ n))
        (center n * ι (sample n * vertex 0 n y (Fin.last (length 0))) *
          chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ k,
      ∃ path : Path (1 : G) (basedImage (p n).val.1
        (center n * ι (sample n * vertex k n y 0) * chart n (z₀ n))
        (center n * ι (sample n * vertex k n y (Fin.last (length k))) * chart n (z₀ n))),
        PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ E k, ‖(height (path t)).toAdd - scale n • w‖ ≤
          4 * scale n * η n + C * (1 + Real.log (2 + scale n)))
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (b true - b false) ≤ 0 := by
  let base := fun n => ι (sample n * origin n)
  let fallback := fun n => ι (sample n * neighbor n)
  let anchors := fun n j => ι (sample n * anchorRoot n j)
  let first := fun n y => ι (sample n * vertex 0 n y (Fin.last (length 0)))
  let second := fun n y => ι (sample n * secondRoot n y)
  have herr : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul 2
  have hfirst' : ∀ n y, first n y = ι (sample n * origin n) *
      ι (S n ((y.val.2 : N) * σ y.val.1)) := by
    intro n y
    dsimp only [first]
    rw [hfirst]
    simp only [map_mul, mul_assoc]
  have hprofiles' : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (anchors n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n ∧
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n := by
    filter_upwards [hprefixProfiles] with n hn y hy
    have ha := hn y hy 1 (Fin.last (length 1))
    have hs := hn y hy 2 (Fin.last (length 2))
    simp only [hanchor, hsecond, show ((1 : Fin 3) != 0) = true from rfl,
      show ((2 : Fin 3) != 0) = true from rfl] at ha hs
    exact ⟨ha, hs⟩
  have hprobePaths' : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (p n).val.1
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (p n).val.1
          (center n * anchors n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E 0, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * (2 * η n) + C * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E 2, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * (2 * η n) + C * (1 + Real.log (2 + scale n))) := by
    filter_upwards [hprobePaths] with n hn y hy
    obtain ⟨p₀, hm₀, hh₀⟩ := hn y hy 0
    obtain ⟨p₂, hm₂, hh₂⟩ := hn y hy 2
    let p₀' : Path (1 : G) (basedImage (p n).val.1
        (center n * base n * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n))) :=
      p₀.cast rfl (by simp only [base, first, hstart])
    let p₂' : Path (1 : G) (basedImage (p n).val.1
        (center n * anchors n (tile n y) * chart n (z₀ n))
        (center n * second n y * chart n (z₀ n))) :=
      p₂.cast rfl (by simp only [anchors, second, hthird, hanchor, hsecond])
    refine ⟨p₀', p₂', hm₀, hm₂, ?_, ?_⟩
    · intro t
      obtain ⟨w, hw, hb⟩ := hh₀ t
      refine ⟨w, hw, ?_⟩
      change ‖(height (p₀ t)).toAdd - scale n • w‖ ≤ _
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · intro t
      obtain ⟨w, hw, hb⟩ := hh₂ t
      refine ⟨w, hw, ?_⟩
      change ‖(height (p₂ t)).toAdd - scale n • w‖ ≤ _
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      ring
  have hbase' : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (base n) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b false)‖ ≤ 2 * η n := by
    filter_upwards [hbaseProfiles] with n hn
    exact (hn false).trans (by nlinarith [hη0 n])
  have hfallback' : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (fallback n) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n := by
    filter_upwards [hbaseProfiles] with n hn
    exact (hn true).trans (by nlinarith [hη0 n])
  exact R.offset_nonpos_of_independent_conditioned_probes π hπ μQ μI μ ν φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 P₂ hμ πS hπS μQS μIS μS hφS σ hσ hμS
    S hS hι hΛ p d ZQ J hZm hJm hZ0 hZt hJ0 hJt good hgood hmass P₁ hv hvol
    tiles tile height center base anchors fallback first second chart q z₀ A (b false) (b true)
    (fun n => sample n * origin n) hfirst' hchart cell hcell hcell0 hcelltop
    hsmall hsurj (fun n => 2 * η n) δ C C (E 0) (E 2) Dbridge hδ hLip hD hpaths
    hprofiles' hbridge hprobePaths' ell tileLoss herr hbase' hfallback'
    htileLoss htile0 hHaar htiles

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialGoodCells
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative mass is unchanged by the actual translated exponential chart -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G I : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- Both the good set and the original cell acquire exactly the same
Jacobian, including the deterministic right suffix. No density estimate is
lost when the independently sampled coordinate good set is put in the group. -/
theorem translated_exponential_cell_ratio
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (k : G)
    (A Q : Set (Fin (finrank ℝ L) → ℝ)) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let f := fun y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm) y * k
    (μ (f '' A)).toReal / (μ (f '' Q)).toReal = (volume A).toReal / (volume Q).toReal := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar e hnil Exp hExp b₀
  let g := (Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm
  have himage (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (fun y => g y * k) '' S = (fun y : G => y * k) '' (g '' S) :=
    image_comp (fun y : G => y * k) g S
  have hm (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (μ ((fun y => g y * k) '' S)).toReal =
        (|(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
          Real.exp (r * columnBasisWeight cost β.val)) * (volume S).toReal := by
    rw [himage, measure_image_mul_right μ]
    dsimp only [μ, g]
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r S]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
  dsimp only
  change (μ ((fun y => g y * k) '' A)).toReal /
    (μ ((fun y => g y * k) '' Q)).toReal = _
  rw [hm, hm, mul_div_mul_left]
  exact mul_ne_zero (abs_ne_zero.mpr (wordBasis_det_ne_zero X words b₀ β)) (Real.exp_ne_zero _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCellTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate-cube sampling is the actual translated Cartan-cell law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
theorem map_cube_eq_translated_groupBox_probability
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) :
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β r).equivFun.symm) y * k
    ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2) (f := sample) (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN (M.boxBasis T hunimod eW E β r) k).measurable.aemeasurable =
      M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k := by
  dsimp only
  let b := M.boxBasis T hunimod eW E β r
  let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm) y * k
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have heq : (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 =
      sample '' cube := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  change ProbabilityMeasure.map (cellProbabilityMeasure volume cube _ _) (f := sample) (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN b k).measurable.aemeasurable =
    cellProbabilityMeasure μ ((fun y => y * k) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1) _ _
  have hprops := M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN
    b₀ E β r k
  have hzero : μ (sample '' cube) ≠ 0 := by simpa only [heq] using hprops.2.1
  have hfinite : μ (sample '' cube) ≠ ∞ := by simpa only [heq] using hprops.2.2
  have hmap := map_cellProbabilityMeasure_of_image_ratio volume μ sample
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN b k).measurable
    cube (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 hzero hfinite
    (fun A => translated_exponential_cell_ratio haarN F.N.equiv (cartanRootIdeal_nilpotent H T)
      F.ExpN F.isExpN chartN hchartN M.letter M.wordList b₀ β
      (M.boxCost T hunimod eW E) r k A cube)
  simpa only [heq] using hmap

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
/-- A raw sheet-profile law can equivalently be sampled in the standard
coordinate cube. This transfers the coordinate affinity theorem to the
original Haar cell without changing either probability law. -/
theorem cube_profile_law_eq_cell_profile_law
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier)
    {X : Type} [MeasurableSpace X] (profile : F.N.carrier → X) (hp : Measurable profile) :
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β r).equivFun.symm) y * k
    ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (profile ∘ sample)) (hp.comp (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN (M.boxBasis T hunimod eW E β r) k).measurable).aemeasurable = ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k) (f := profile) hp.aemeasurable := by
  dsimp only
  rw [← M.map_cube_eq_translated_groupBox_probability T F hunimod eW haarN chartN hchartN b₀ E β r k]
  apply ProbabilityMeasure.toMeasure_injective
  exact (Measure.map_map hp
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β r) k).measurable).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConcentratedRootFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentrated profiles at the actual moving contact pivot -/

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
theorem exists_concentrated_root_frames
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
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
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∃ z₀ : ℕ → Z,
      (∀ᶠ n in atTop,
        F.profileChart (br n) (z₀ n).val =
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : C(Z, W) × C(Z, W))
    (_hf : f ∈ (limitLaw : Measure _).support)
    (_haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (_hlim :
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
            (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)),
    let chart := fun n (z : Z) => F.profileChart (br n) z.val
    let q := fun z : Z => h (b.equivFun.symm z.val)
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        (∀ s : Bool,
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (if s then base n else origin n)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (D.vertex k n y j)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y 0))) * chart n (z₀ n))
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y (Fin.last (P k).length)))) * chart n (z₀ n))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  exact M.exists_concentrated_profile_frames T F hunimod eW hExp realize haarN haarD
    dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
    hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
    scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
    hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRestrictedNeighborLaw
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The neighboring law in the coordinates of the linked probe selection -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The actual Haar neighboring law gives the joint coordinate-cube law of
the two original profiles restricted to any compact probe-height set.
Supported pairs remain supported. No new limiting-law assumption is used. -/
theorem restricted_neighbor_cube_law
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale r : ℕ → ℝ)
    (base step : ℕ → F.N.carrier) (origin next : ℕ → cartanRootIdeal H)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = base n)
    (hnext : ∀ n, F.ExpN (F.N.equiv (next n)) = base n * step n)
    (hD : Continuous F.ExpD) (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n))
    (x : ℕ → G) (bD : ℕ → Basis (Fin (finrank ℝ H)) ℝ H)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * base n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 →
      ∀ z, (profile n q).val z = rescaledMapProfile (J n) (x n) (F.inclusionN q)
        (r n) (F.profileChart (bD n)) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (base n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
        atTop (𝓝 ν))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)] [BorelSpace (C(Z, W) × C(Z, W))]
    (f : S × S) (hf : f ∈ (ν : Measure (S × S)).support) :
    let restrictPair := fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z)
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    Tendsto (fun n => ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (fun y =>
        ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
          (M.boxBasis T hunimod eW E β (scale n)) (bD n) y (origin n)).restrict Z,
         (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
          (M.boxBasis T hunimod eW E β (scale n)) (bD n) y (next n)).restrict Z))) ((F.measurable_fixed_sampledProbeProfile (chartN.continuous.congr hchartN) hD (J n) (hJ n) (x n) (r n) (M.boxBasis T hunimod eW E β (scale n)) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile (chartN.continuous.congr hchartN) hD (J n) (hJ n) (x n) (r n) (M.boxBasis T hunimod eW E β (scale n)) (bD n) (next n) Z)).aemeasurable)
      atTop (𝓝 (ProbabilityMeasure.map ν (f := restrictPair) ((((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_fst)).prodMk ((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_snd))).measurable.aemeasurable))) ∧
      restrictPair f ∈ (ProbabilityMeasure.map ν (f := restrictPair) ((((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_fst)).prodMk ((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_snd))).measurable.aemeasurable) :
        Measure (C(Z, W) × C(Z, W))).support := by
  dsimp only
  let restrictPair := fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z)
  have hrp : Continuous restrictPair :=
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_fst)).prodMk
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨?_, mem_support_map_of_continuous ν restrictPair hrp hf⟩
  let cellLaw := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN
    hchartN b₀ E β (scale n) (base n)
  let raw := fun n q => (profile n q, profile n (q * step n))
  have hraw n : Measurable (raw n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have hlim := sampled_projection_tendsto cellLaw raw hraw ν hν restrictPair hrp
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  let sample := fun n y => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y * base n
  apply hlim.congr'
  filter_upwards [] with n
  have hlaw := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN
    hchartN b₀ E β (scale n) (base n) (restrictPair ∘ raw n) (hrp.measurable.comp (hraw n))
  apply hlaw.symm.trans
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [ae_mem_cellProbabilityMeasure volume cube measurableSet_Icc
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2] with y hy
  have hm : ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one]
    exact ⟨y, hy, rfl⟩
  have h₁ := hactual n (sample n y) (Or.inl ⟨_, hm, rfl⟩)
  have h₂ := hactual n (sample n y * step n) (Or.inr ⟨_, hm, rfl⟩)
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z
  · change (profile n (sample n y)).val z.val = rescaledMapProfile (J n) (x n)
      (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) y (origin n))
      (r n) (F.profileChart (bD n)) z.val
    rw [h₁]
    simp only [CartanFactorModel.sampledProbeSuffix, sample, Function.comp_apply,
      map_mul, horigin n]
  · change (profile n (sample n y * step n)).val z.val = rescaledMapProfile (J n) (x n)
      (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) y (next n))
      (r n) (F.profileChart (bD n)) z.val
    rw [h₂]
    simp only [CartanFactorModel.sampledProbeSuffix, sample, Function.comp_apply,
      map_mul, hnext, mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOriginalNeighborFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration from the original neighboring-cell law -/

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

variable [IsTopologicalGroup F.N.carrier]

set_option maxHeartbeats 1000000 in
/-- The original Haar neighboring law supplies the restricted law used by
concentration. The sampled points retain the original center. -/
theorem exists_original_neighbor_root_frames
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
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
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (baseGroup step : ℕ → F.N.carrier)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * baseGroup n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (S × S))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (baseGroup n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 law))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
    (hf : f ∈ (law : Measure (S × S)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∃ z₀ : ℕ → Z,
      (∀ᶠ n in atTop,
        F.profileChart (br n) (z₀ n).val =
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))],
    let chart := fun n (z : Z) => F.profileChart (br n) z.val
    let q := fun z : Z => h (b.equivFun.symm z.val)
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        (∀ s : Bool,
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (if s then base n else origin n)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (D.vertex k n y j)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y 0))) * chart n (z₀ n))
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y (Fin.last (P k).length)))) * chart n (z₀ n))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  obtain ⟨Z, C, hZ, hZV, hC, z₀, hz₀, hframes⟩ :=
    M.exists_concentrated_root_frames T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ
  refine ⟨Z, C, hZ, hZV, hC, z₀, hz₀, ?_⟩
  intro instCompact ν instInner instMeas instBorel instProdBorel instApprox
  have hrestricted := M.restricted_neighbor_cube_law T F hunimod eW haarN
    chartN hchartN b₀ E β scale (fun n => max (Real.log (scale n)) 0)
    baseGroup step origin base horigin hbase hD
    (fun n g => (π ((p n).val.1 g)).toAdd)
    (fun n => (hπ.comp (p n).property.1.1).continuous) x
    (fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
      (max (Real.log (scale n)) 0)) S profile hp hactual law hlaw Z f hf
  apply hframes ν (ProbabilityMeasure.map law
    (f := (fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z))) ((((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_fst)).prodMk ((ContinuousMap.continuous_restrict Z).comp (continuous_subtype_val.comp continuous_snd))).measurable.aemeasurable)) A bval
    (f.1.val.restrict Z, f.2.val.restrict Z) hrestricted.2
  · intro s z
    cases s with
    | false => simpa using haffine false z.val (hZV z.property)
    | true => simpa using haffine true z.val (hZV z.property)
  · exact hrestricted.1

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOriginalNeighborOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A trace comparison from the original neighboring-cell law -/

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

variable [IsTopologicalGroup F.N.carrier]


variable {QS QT : Type}
  [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS] [T2Space QS]
  [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
  [Group QT] [TopologicalSpace QT] [IsTopologicalGroup QT]
  [SecondCountableTopology QT] [MeasurableSpace QT] [BorelSpace QT]
  [MeasurableMul F.D.carrier]
  (πS : F.N.carrier →* QS) (ZQ : Set QS) (J : ℕ → Set πS.ker)
  [∀ n, CompactSpace (ZQ ×ˢ J n)] [∀ n, Nonempty (ZQ ×ˢ J n)]

set_option maxHeartbeats 1000000 in
/-- Concentrate the original law, then compare its actual linked probes.
All source cells and their volume/count bounds remain explicit. -/
theorem original_neighbor_offset_nonpos_oai
    [Nonempty (Fin M.letterCount)]
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
    (probe : Fin 3 → ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (baseGroup step : ℕ → F.N.carrier)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * baseGroup n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (S × S))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (baseGroup n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 law))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
    (hf : f ∈ (law : Measure (S × S)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (hπS : Continuous πS) (σS : C(QS, F.N.carrier))
    (hσS : ∀ q, πS (σS q) = q)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure F.N.carrier)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (F.action d) μS μS)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σS hσS).symm
      (μQS.prod μIS))
    (flow : ℕ → F.N.carrier ≃ₜ F.N.carrier)
    (hflow : ∀ n, MeasurePreserving (flow n) μS μS)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (hregular : ∀ n,
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)).InnerRegular)
    (P₁ P₂ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ) (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (anchorRoot : ∀ n, Fin (tiles n) → F.N.carrier)
    (secondRoot : ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
    (hfirst : ∀ n y, F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length))) =
      baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1))
    (hanchor : ∀ n y, F.ExpN (F.N.equiv (D.vertex 1 n y (Fin.last (P 1).length))) =
      anchorRoot n (tile n y))
    (hsecond : ∀ n y, F.ExpN (F.N.equiv (D.vertex 2 n y (Fin.last (P 2).length))) =
      secondRoot n y)
    (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
    (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
    (hbridge : ∀ᶠ n in atTop, ∀ y : ZQ ×ˢ J n,
      dist (F.inclusionN (secondRoot n y) * Exp (scale n •
          (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
    (πT : F.N.carrier →* QT) (hπT : Continuous πT)
    (μT : Measure QT) (μTI : Measure πT.ker)
    (μ : Measure F.N.carrier) (νD : Measure F.D.carrier)
    [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite νD]
    [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [νD.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
    (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod νD) cell ≠ 0) (hcelltop : (μ.prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions πT μT μTI νD scale P₂,
        μ = Measure.map (quotientSectionHomeomorph πT hπT
          R.sectionMap R.section_rightInverse).symm (μT.prod μTI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 0)
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μT E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (bval true - bval false) ≤ 0 := by
  obtain ⟨Z, Cp, hZ, hZV, hCp, z₀, hz₀, frames⟩ :=
    M.exists_original_neighbor_root_frames T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ
      chartN hchartN baseGroup step horigin hbase S profile hp hactual law hlaw A bval f hf haffine
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let : MeasurableSpace C(Z, W) := borel _
  let : BorelSpace C(Z, W) := ⟨rfl⟩
  let : MeasurableSpace (C(Z, W) × C(Z, W)) := borel _
  let : BorelSpace (C(Z, W) × C(Z, W)) := ⟨rfl⟩
  let ν := fun n => cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n)
    (hZm.prod (hJm n))
    (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n))
  let : ∀ n, (ν n : Measure (ZQ ×ˢ J n)).InnerRegular := hregular
  obtain ⟨η, sample, good, hη0, hη, hgood, hframes⟩ := frames ν
  let ηnonneg := fun n => (hη0 n).le
  obtain ⟨regions, hμ, hregions⟩ := regionFactory η ηnonneg hη Cp hCp
  let br := fun n => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
  let chart := fun n (z : Z) => F.profileChart (br n) z.val
  let q := fun z : Z => eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
      GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let dseq := fun n => F.ExpD (F.D.equiv ((br n).equivFun.symm (z₀ n).val))
  let sampled := fun n => F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n)
  let vertex := fun j n y l => F.ExpN (F.N.equiv (D.vertex j n y l))
  have hchart : ∀ n, chart n (z₀ n) = F.inclusionD (dseq n) := fun _ => rfl
  have hstart : ∀ n y, vertex 0 n y 0 = baseGroup n := by
    intro n y
    exact (congrArg (fun v => F.ExpN (F.N.equiv v)) (D.first_start n y)).trans (horigin n)
  have hthird : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (P 1).length) := by
    intro n y
    exact congrArg (fun v => F.ExpN (F.N.equiv v)) (D.third_start n y)
  have hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤ (ν n : Measure _) (good n) := by
    intro n
    have he : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    simpa only [he] using (hgood n).2.2.le
  have hbaseProfiles : ∀ᶠ n in atTop, ∀ s : Bool,
      ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (sampled n * if s then baseGroup n * step n else baseGroup n))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ ≤ η n := by
    filter_upwards [hframes] with n hn s
    cases s with
    | false => simpa [sampled, chart, br, q, horigin] using (hn.1 false).le
    | true => simpa [sampled, chart, br, q, hbase] using (hn.1 true).le
  have hprefix : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ j l,
      ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (sampled n * vertex j n y l))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + bval (j != 0))‖ ≤ 2 * η n := by
    filter_upwards [hframes] with n hn y hy j l
    exact (hn.2.1 y hy j l).le
  have hb : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (x n * F.inclusionN (sampled n * secondRoot n y) * chart n (z₀ n))
        (x n * F.inclusionN (sampled n * vertex 0 n y (Fin.last (P 0).length)) *
          chart n (z₀ n)) ≤ Dbridge * scale n := by
    filter_upwards [hbridge, hz₀] with n hn hz y _hy
    have hzchart : chart n (z₀ n) = Exp (scale n •
        (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := hz.1
    rw [hzchart]
    change dist (x n * F.inclusionN (sampled n * secondRoot n y) * _)
      (x n * F.inclusionN (sampled n *
        F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length)))) * _) ≤ _
    rw [hfirst n y]
    simpa only [map_mul, mul_assoc, dist_mul_left] using hn y
  exact MeasuredProbeRegions.offset_nonpos_of_linked_probe_bounds
    (N := F.N.carrier) (D := F.D.carrier) (G := G) (Q := QT) (W := W) (V := W)
    πT hπT μT μTI μ νD F.action F.inclusionN F.inclusionD F.conjugation hφ
    actionQ act hact scale hscale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) P₂ regions hμ
    πS hπS μQS μIS μS hφS σS hσS hμS flow hflow F.closedN hΛ p dseq
    ZQ J hZm hJm hZ0 hZt hJ0 hJt good (fun n => (hgood n).1) hmass P₁ hv hvol tiles tile
    π x sampled baseGroup (fun n => baseGroup n * step n) anchorRoot secondRoot
    (fun j => (P j).length) vertex hstart hthird hfirst hanchor hsecond
    chart q z₀ A bval hchart cell hcell hcell0 hcelltop hsmall F.surjective
    η ηnonneg hη δtarget Cp Dbridge
    (fun k => (fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe k)
    hδtarget (fun n => (p n).property.1.1) hDb hregions hbaseProfiles hprefix hb
    (by filter_upwards [hframes] with n hn; exact hn.2.2)
    ell tileLoss htileLoss htile0 hHaar htiles

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos_oai := @OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos_oai
