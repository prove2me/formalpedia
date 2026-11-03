-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:31:57.487181+00:00
-- url     : https://prove2.me/submissions/3a7cffb5-4f1c-4fe9-9265-14ed83c70db4

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_sampling_geometry
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_profile_estimates

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanGeneratorPool_lieSpan [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) = ⊤ := by
  let N := cartanRootIdeal H
  let U := LieSubalgebra.lieSpan ℝ N (cartanGeneratorPool H)
  have himage : N.incl '' cartanGeneratorPool H =
      {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      have hN : v ∈ N := LieSubmodule.subset_lieSpan hv
      exact ⟨⟨v, hN⟩, hv, rfl⟩
  have hmap : U.map N.incl = N.toLieSubalgebra := by
    rw [LieSubalgebra.map_lieSpan, himage]
    change cartanRootSubalgebra H = N.toLieSubalgebra
    apply SetLike.coe_injective
    exact congrArg (fun V : Submodule ℝ L => (V : Set L))
      (cartanRootSubalgebra_eq_ideal H T)
  apply top_unique
  intro v _
  have hv : (v : L) ∈ U.map N.incl := by rw [hmap]; exact v.property
  obtain ⟨w, hw, heq⟩ := hv
  have : w = v := Subtype.ext heq
  change v ∈ U
  exact this ▸ hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledBasisChange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential margins between two rescalings of the same basis -/

namespace PolycyclicRecognition

open Module

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L]

/-- Exact coordinate change between two exponential rescalings. -/
theorem repr_change_exponentialRescaleBasis (b : Basis J ℝ L)
    (s t : J → ℝ) (r : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b s r).repr x j =
      (exponentialRescaleBasis b t r).repr x j * Real.exp (r * (t j - s j)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  have he : Real.exp (-(r * t j)) * Real.exp (r * (t j - s j)) =
      Real.exp (-(r * s j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_right_comm, he]

/-- A common difference between the exponents gives an exponential gain
or loss in the whole coordinate maximum norm. -/
theorem norm_change_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (s t : J → ℝ) {r α : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ j, t j - s j ≤ α) (x : L) :
    ‖(exponentialRescaleBasis b s r).equivFun x‖ ≤
      Real.exp (r * α) * ‖(exponentialRescaleBasis b t r).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b s r).repr x j| ≤ _
  rw [repr_change_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ‖(exponentialRescaleBasis b t r).equivFun x‖ * Real.exp (r * α) :=
      mul_le_mul (norm_le_pi_norm ((exponentialRescaleBasis b t r).equivFun x) j)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hgap j) hr))
        (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := mul_comm _ _

end PolycyclicRecognition

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformProfileConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform concentration and independent suffix sampling -/

noncomputable section
namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- If every deterministic choice has vanishing bad probability, the
bound is uniform over all permitted choices at each scale. -/
theorem eventually_uniform_lt_of_all_selections
    {A : ℕ → Type} [∀ n, Nonempty (A n)] (p : ∀ n, A n → ℝ≥0∞)
    (hp : ∀ a : ∀ n, A n, Tendsto (fun n => p n (a n)) atTop (𝓝 0))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ a, p n a < η := by
  classical
  let a : ∀ n, A n := fun n => if h : ∃ a, η ≤ p n a then h.choose else Classical.arbitrary _
  have ha := (hp a).eventually (gt_mem_nhds hη)
  filter_upwards [ha] with n hn b
  by_contra h
  have hex : ∃ b, η ≤ p n b := ⟨b, le_of_not_gt h⟩
  have hb : η ≤ p n (a n) := by
    dsimp only [a]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact (not_le_of_gt hn) hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ThreeProbeConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint concentration of the three actual probe chains -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Concentration is transitive through the measured anchor profile. -/
theorem bad_distance_triangle_tendsto_zero
    {X S : Type} [MeasurableSpace X] [PseudoMetricSpace S]
    (μ : ℕ → Measure X) (f g h : ℕ → X → S)
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DeterministicProbabilityComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic affine comparisons extracted from probable comparisons -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A constant event cannot have vanishing positive probability unless
its deterministic error tends to zero. -/
theorem deterministic_distance_tendsto_zero_of_probability
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y)
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {_x | ε ≤ dist (a n) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := (hp ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hh] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  by_contra h
  have he : {x : X | ε ≤ dist (a n) (b n)} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact le_of_not_gt h
  rw [he, measure_univ] at hn
  exact (lt_irrefl (1 : ℝ≥0∞)) hn

/-- Two deterministic approximants agree asymptotically when their
sampled profiles can be compared on a common probability law. -/
theorem deterministic_distance_tendsto_zero_of_coupled_profiles
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y) (f g : ℕ → X → Y)
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply deterministic_distance_tendsto_zero_of_probability μ a b
  intro ε hε
  apply bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) g (fun n _ => b n) _ hright ε hε
  exact fun η hη => bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) f g hleft hpair η hη

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteAffineSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical finite labels and separation from translated competitors -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

theorem minimizingFiniteLabel_le {L : Type} [Fintype L] [Nonempty L]
    (cost : L → ℝ) (a : L) : cost (minimizingFiniteLabel cost) ≤ cost a :=
  (Finset.exists_min_image Finset.univ cost Finset.univ_nonempty).choose_spec.2 a
    (Finset.mem_univ a)

/-- The canonical choices inherit any vanishing competitor bound. -/
theorem minimizingFiniteLabel_tendsto_zero
    {L : Type} [Fintype L] [Nonempty L] (cost : ℕ → L → ℝ)
    (hnonneg : ∀ n a, 0 ≤ cost n a)
    (a : ℕ → L) (ha : Tendsto (fun n => cost n (a n)) atTop (𝓝 0)) :
    Tendsto (fun n => cost n (minimizingFiniteLabel (cost n))) atTop (𝓝 0) :=
  squeeze_zero (fun n => hnonneg n _) (fun n => minimizingFiniteLabel_le (cost n) (a n)) ha

/-- Subtracting the value at the identity costs at most a factor of two
in the uniform norm. This removes arbitrary offsets from a comparison. -/
theorem linear_profile_distance_le_twice_affine
    {Z W : Type} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    (A B : C(Z, W)) (z₀ : Z) (hA : A z₀ = 0) (hB : B z₀ = 0) (b c : W) :
    dist A B ≤ 2 * dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c) := by
  let D := dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c)
  have hoff : dist b c ≤ D := by
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hA, hB, zero_add] using
      (A + ContinuousMap.const Z b).dist_apply_le_dist
        (g := B + ContinuousMap.const Z c) z₀
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) dist_nonneg)).mpr
  intro z
  have hpoint : dist (A z + b) (B z + c) ≤ D :=
    (A + ContinuousMap.const Z b).dist_apply_le_dist
      (g := B + ContinuousMap.const Z c) z
  calc
    dist (A z) (B z) = dist (A z + b) (B z + b) := (dist_add_right _ _ _).symm
    _ ≤ dist (A z + b) (B z + c) + dist (B z + c) (B z + b) := dist_triangle _ _ _
    _ = dist (A z + b) (B z + c) + dist b c := by rw [dist_add_left, dist_comm c b]
    _ ≤ D + D := add_le_add hpoint hoff
    _ = 2 * D := by ring

/-- Finitely many distinct centered profiles have a uniform positive
separation, even after arbitrary offsets are added. -/
theorem exists_finite_affine_label_separation
    {Z W L : Type} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    [Fintype L] [Nonempty L] (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a a' b b',
      dist (A a + ContinuousMap.const Z b) (A a' + ContinuousMap.const Z b') < ε → a = a' := by
  classical
  let cost : L × L → ℝ := fun p => if p.1 = p.2 then 1 else dist (A p.1) (A p.2) / 3
  have hpos p : 0 < cost p := by
    dsimp only [cost]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (dist_pos.mpr (fun he => h (hA he))) (by norm_num)
  let p := minimizingFiniteLabel cost
  refine ⟨cost p, hpos p, ?_⟩
  intro a a' b b' hd
  by_contra hne
  have hmin := minimizingFiniteLabel_le cost (a, a')
  have hdist := linear_profile_distance_le_twice_affine (A a) (A a') z₀
    (hzero a) (hzero a') b b'
  have he : cost (a, a') = dist (A a) (A a') / 3 := by simp [cost, hne]
  have hposdist : 0 < dist (A a) (A a') := dist_pos.mpr (fun h => hne (hA h))
  change cost p ≤ cost (a, a') at hmin
  rw [he] at hmin
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledAffineComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic comparison through a change of scale

Two ordinary sampling laws need not agree. Their mixed comparison and the
exact change of coordinates suffice to compare the deterministic affine
approximations. Finite separation then identifies their linear parts.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem bad_probability_tendsto_zero_of_dist_le
    {X Y Z : Type} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (μ : ℕ → Measure X) (f g : ℕ → X → Y) (u v : ℕ → X → Z)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ n x, dist (u n x) (v n x) ≤ K * dist (f n x) (g n x))
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (u n x) (v n x)}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (hp (ε / K) (div_pos hε hK)) (fun _ => zero_le)
  intro n
  apply measure_mono
  intro x hx
  exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hx.trans (hbound n x))

/-- Vanishing affine discrepancy identifies finite labels and their offsets. -/
theorem affine_labels_and_offsets_of_distance_tendsto_zero
    {Z W L : Type} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [Fintype L] [Nonempty L]
    (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0)
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hd : Tendsto (fun n => dist (A (a n) + ContinuousMap.const Z (b n))
      (A (a' n) + ContinuousMap.const Z (b' n))) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (b' n)) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hsep⟩ := exists_finite_affine_label_separation A hA z₀ hzero
  constructor
  · filter_upwards [hd.eventually (gt_mem_nhds hε)] with n hn
    exact hsep _ _ _ _ hn
  · apply squeeze_zero (fun _ => dist_nonneg) _ hd
    intro n
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hzero, zero_add] using
      (A (a n) + ContinuousMap.const Z (b n)).dist_apply_le_dist
        (g := A (a' n) + ContinuousMap.const Z (b' n)) z₀

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExactProfileTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic affine comparison after an exact change of chart -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Two deterministic approximants can be compared under a single law
when their sampled profiles are related by an exact Lipschitz transport. -/
theorem deterministic_distance_tendsto_zero_of_exact_transport
    {X Y Z : Type} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (μ : ℕ → ProbabilityMeasure X) (a : ℕ → Y) (b : ℕ → Z)
    (f : ℕ → X → Y) (g : ℕ → X → Z) (H : ℕ → Z → Y)
    {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ n x, f n x = H n (g n x))
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  apply deterministic_distance_tendsto_zero_of_coupled_profiles μ a (fun n => H n (b n))
    f f hleft
  · intro ε hε
    simpa only [dist_self, Set.ofPred_false, measure_empty,
      show ¬ε ≤ (0 : ℝ) from not_le.mpr hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · intro ε hε
    apply bad_probability_tendsto_zero_of_dist_le (fun n => (μ n : Measure X))
      g (fun n _ => b n) f (fun n _ => H n (b n)) hK
      (fun n x => by rw [hmatch n x]; exact hH n _ _) hright hε

theorem dist_transportCompactProfile_le
    {Z Z' W : Type} [TopologicalSpace Z] [TopologicalSpace Z']
    [CompactSpace Z] [CompactSpace Z'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (ψ : C(Z, Z')) (c : W) (f g : C(Z', W)) :
    dist (transportCompactProfile t ψ c f) (transportCompactProfile t ψ c g) ≤
      |t| * dist f g := by
  apply (ContinuousMap.dist_le (mul_nonneg (abs_nonneg _) dist_nonneg)).mpr
  intro z
  change dist (t • f (ψ z) + c) (t • g (ψ z) + c) ≤ _
  rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (f.dist_apply_le_dist (g := g) (ψ z)) (abs_nonneg _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanProbabilityConverse
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean error implies convergence in probability -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Markov's inequality gives the probability direction for an integrable
nonnegative profile error, without a global bound off its sampling cell. -/
theorem bad_probability_tendsto_zero_of_mean
    {X : Type} [MeasurableSpace X] (μ : ℕ → ProbabilityMeasure X)
    (f : ℕ → X → ℝ) (hi : ∀ n, Integrable (f n) (μ n : Measure X))
    (hf : ∀ n, 0 ≤ᵐ[(μ n : Measure X)] f n)
    (hm : Tendsto (fun n => ∫ x, f n x ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ f n x}) atTop (𝓝 0) := by
  have hbound n : ((μ n : Measure X) {x | ε ≤ f n x}).toReal ≤
      (∫ x, f n x ∂(μ n : Measure X)) / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa only [measureReal_def, mul_comm] using
      mul_meas_ge_le_integral_of_nonneg (hf n) (hi n) ε
  have hreal : Tendsto (fun n => ((μ n : Measure X) {x | ε ≤ f n x}).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound (by simpa using hm.div_const ε)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal hreal

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSamplingMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical affine choices for compactly carried sampling laws -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

theorem integrable_continuous_of_ae_mem_compact
    {X E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] (μ : Measure X) [IsFiniteMeasure μ]
    {C : Set X} (hC : IsCompact C) (hfull : ∀ᵐ x ∂μ, x ∈ C)
    {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) hC
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hfull] at hi

theorem canonicalAffineLabel_mean_tendsto_zero
    {X Y L : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    [Finite L] [Nonempty L]
    (μ : ℕ → Measure X) (f : ℕ → X → Y) (A : ℕ → L → Y)
    (h : ∃ a : ℕ → L, Tendsto (fun n => ∫ x, dist (f n x) (A n (a n)) ∂μ n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      dist (f n x) (A n (canonicalAffineLabel (μ n) (f n) (A n))) ∂μ n)
      atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := h
  let : Fintype L := Fintype.ofFinite L
  exact minimizingFiniteLabel_tendsto_zero
    (fun n a => ∫ x, dist (f n x) (A n a) ∂μ n)
    (fun _ _ => integral_nonneg (fun _ => dist_nonneg)) a ha

/-- Compact support supplies the integrability required by Markov's
inequality, including for the canonical minimizing affine label. -/
theorem compact_profile_probability_of_mean
    {X Y : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (C : ℕ → Set X)
    (hC : ∀ n, IsCompact (C n)) (hfull : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x ∈ C n)
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (a : ℕ → Y)
    (hm : Tendsto (fun n => ∫ x, dist (f n x) (a n) ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ dist (f n x) (a n)})
      atTop (𝓝 0) :=
  bad_probability_tendsto_zero_of_mean μ _
    (fun n => integrable_continuous_of_ae_mem_compact (μ n : Measure X) (hC n) (hfull n)
      ((hf n).dist continuous_const))
    (fun _ => Eventually.of_forall (fun _ => dist_nonneg)) hm hε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearProfilesOnBall
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite linear profiles tested on one fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem linearMap_eq_of_eqOn_closedBall {R : ℝ} (hR : 0 < R)
    (f g : V →ₗ[ℝ] W) (h : EqOn f g (Metric.closedBall 0 R)) : f = g := by
  ext x
  let c := R / (‖x‖ + 1)
  have hc : 0 < c := div_pos hR (by positivity)
  have hx : c • x ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖x‖ ≤ c * (‖x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = R := div_mul_cancel₀ _ (by positivity)
  have hh := h hx
  rw [map_smul, map_smul] at hh
  exact smul_right_injective W hc.ne' hh

theorem linearBallProfile_injective (q : V →L[ℝ] W) (hq : Function.Surjective q)
    {R : ℝ} (hR : 0 < R) : Function.Injective (fun A => linearBallProfile q A R) := by
  intro A B h
  have he : A.toLinearMap.comp q.toLinearMap = B.toLinearMap.comp q.toLinearMap :=
    linearMap_eq_of_eqOn_closedBall hR _ _ (fun z hz =>
      congrArg (fun f : C(Metric.closedBall (0 : V) R, W) => f ⟨z, hz⟩) h)
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact DFunLike.congr_fun he v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasepointAffineSeparation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-label separation and center errors after changing basepoint -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric
open scoped Topology

/-- Comparing transported affine profiles identifies their finite linear
labels and measures the exact remaining center error. -/
theorem affine_labels_offsets_of_chart_transport
    {V W L : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (q : V →L[ℝ] W) (hq : Function.Surjective q)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    {R S : ℝ} (hR : 0 < R) (_hS : 0 < S)
    (a a' : ℕ → L) (b b' c : ℕ → W) (v : ℕ → W) (t : ℕ → ℝ)
    (ψ : ℕ → C(closedBall (0 : V) R, closedBall (0 : V) S))
    (hheight : ∀ᶠ n in atTop, ∀ z, t n • q (ψ n z) = q z - v n)
    (hd : Tendsto (fun n => dist
      (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
      (transportCompactProfile (t n) (ψ n) (c n)
        (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))))
      atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (t n • b' n + c n - A (a' n) (v n))) atTop (𝓝 0) := by
  let P := fun l => linearBallProfile q (A l) R
  have hP : Function.Injective P := (linearBallProfile_injective q hq hR).comp hA
  let z₀ : closedBall (0 : V) R := ⟨0, by simpa using hR.le⟩
  have hzero : ∀ l, P l z₀ = 0 := by intro l; change A l (q 0) = 0; simp
  have he n (hn : ∀ z, t n • q (ψ n z) = q z - v n) :
      transportCompactProfile (t n) (ψ n) (c n)
      (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n)) =
      P (a' n) + ContinuousMap.const _ (t n • b' n + c n - A (a' n) (v n)) := by
    ext z
    change t n • (A (a' n) (q (ψ n z)) + b' n) + c n =
      A (a' n) (q z) + (t n • b' n + c n - A (a' n) (v n))
    rw [smul_add, ← map_smul, hn, map_sub]
    abel
  have hd' : Tendsto (fun n => dist (P (a n) + ContinuousMap.const _ (b n))
      (P (a' n) + ContinuousMap.const _ (t n • b' n + c n - A (a' n) (v n))))
      atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hheight] with n hn
    rw [he n hn]
  exact affine_labels_and_offsets_of_distance_tendsto_zero P hP z₀ hzero a a' b _ hd'

/-- Vanishing mean offsets remove the affine constants from the comparison,
leaving precisely the normalized error in the two center heights. -/
theorem center_error_tendsto_zero_of_offsets
    {W L : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : L → W →L[ℝ] W) (a : ℕ → L) (b b' c v : ℕ → W) (t : ℝ)
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0))
    (hoff : Tendsto (fun n => dist (b n) (t • b' n + c n - A (a n) (v n)))
      atTop (𝓝 0)) :
    Tendsto (fun n => c n - A (a n) (v n)) atTop (𝓝 0) := by
  let e := fun n => t • b' n + c n - A (a n) (v n)
  have hdiff : Tendsto (fun n => b n - e n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hoff)
  have ht : Tendsto (fun n => t • b' n) atTop (𝓝 0) := by
    simpa only [smul_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).smul hb')
  have hh := (hb.sub hdiff).sub ht
  have hh' : Tendsto (fun n => c n - A (a n) (v n)) atTop (𝓝 (0 - 0 - 0)) :=
    hh.congr' (Eventually.of_forall (fun n => by dsimp only [e]; abel))
  simpa only [sub_zero] using hh'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of normalized cell laws under Haar-preserving maps -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- If the inverse image of the smaller cell lies in the sampling cell,
the pushed normalized sampling law dominates its normalized restriction.
The loss is exactly the ratio of the two Haar volumes. -/
theorem normalized_cell_transport_domination
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (C D : Set X) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (hcover : τ ⁻¹' C ⊆ D)
    (S : Set X) (hS : MeasurableSet S) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure X) S ≤
      (μ D / μ C) * (cellProbabilityMeasure μ D hD0 hDfin : Measure X) (τ ⁻¹' S) := by
  have hm : μ (S ∩ C) ≤ μ (τ ⁻¹' S ∩ D) := calc
    μ (S ∩ C) = μ (τ ⁻¹' (S ∩ C)) :=
      (hτ.measure_preimage (hS.inter hC).nullMeasurableSet).symm
    _ ≤ μ (τ ⁻¹' S ∩ D) := measure_mono (fun _ hx => ⟨hx.1, hcover hx.2⟩)
  change (((μ C)⁻¹ • μ.restrict C) S) ≤
    (μ D / μ C) * (((μ D)⁻¹ • μ.restrict D) (τ ⁻¹' S))
  rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hS,
    Measure.restrict_apply (hτ.measurable hS)]
  change (μ C)⁻¹ * μ (S ∩ C) ≤
    (μ D / μ C) * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D))
  calc
    _ ≤ (μ C)⁻¹ * μ (τ ⁻¹' S ∩ D) := mul_le_mul' le_rfl hm
    _ = _ := by
      rw [div_eq_mul_inv]
      have he : μ D * (μ C)⁻¹ * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D)) =
          (μ C)⁻¹ * (μ D * (μ D)⁻¹) * μ (τ ⁻¹' S ∩ D) := by ac_rfl
      rw [he, ENNReal.mul_inv_cancel hD0 hDfin, mul_one]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DifferentCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Density comparison with different starting and target cells -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- The starting law is arbitrary. Only the target-to-suffix volume ratio
enters the domination constant, including when the two scales differ. -/
theorem different_cell_pair_domination
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ProbabilityMeasure X) (A : Set X)
    (hA : ∀ᵐ a ∂(ν : Measure X), a ∈ A)
    (μ : Measure Y) (C D : Set Y) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → Y → Y)
    (hτ : ∀ a ∈ A, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ A, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × Y => (p.1, τ p.1 p.2)))
    (B : Set (X × Y)) (hB : MeasurableSet B) :
    (ν : Measure X).prod (cellProbabilityMeasure μ C hC0 hCfin : Measure Y) B ≤
      (μ D / μ C) * (ν : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y)
        ((fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B) := by
  let P := (fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B
  have hP : MeasurableSet P := hpair hB
  rw [Measure.prod_apply hB, Measure.prod_apply hP]
  calc
    _ ≤ ∫⁻ a, (μ D / μ C) *
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y) (Prod.mk a ⁻¹' P)
        ∂(ν : Measure X) := by
      apply lintegral_mono_ae
      filter_upwards [hA] with a ha
      exact normalized_cell_transport_domination μ C D hC hC0 hCfin hD0 hDfin
        (τ a) (hτ a ha) (hcover a ha) (Prod.mk a ⁻¹' B)
        ((measurable_const.prodMk measurable_id) hB)
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hP)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslatedCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A changed Haar cell dominated by independent suffix sampling -/

namespace PolycyclicRecognition
open MeasureTheory Set
open scoped ENNReal

/-- A measure-preserving change of the target cell is dominated by the
independent starting-cell and suffix law. The inverse-cover inclusion supplies
the required geometric hypothesis. -/
theorem translated_cell_domination
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ProbabilityMeasure X) (A : Set X)
    (hA : ∀ᵐ a ∂(ν : Measure X), a ∈ A)
    (μ : Measure Y) (C D : Set Y) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (ψ : Y → Y) (hψ : Measurable ψ) (τ : X → Y → Y) (m : X → Y → Y)
    (hτ : ∀ a ∈ A, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ A, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × Y => (p.1, τ p.1 p.2)))
    (hmatch : ∀ a k, ψ (τ a k) = m a k)
    (S : Set Y) (hS : MeasurableSet S) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure Y) (ψ ⁻¹' S) ≤
      (μ D / μ C) * (ν : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y)
        {p | m p.1 p.2 ∈ S} := by
  have hh := different_cell_pair_domination ν A hA μ C D hC hC0 hCfin hD0 hDfin
    τ hτ hcover hpair (univ ×ˢ (ψ ⁻¹' S)) (MeasurableSet.univ.prod (hψ hS))
  have he : (fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' (univ ×ˢ (ψ ⁻¹' S)) =
      {p | m p.1 p.2 ∈ S} := by
    ext p
    simp only [mem_preimage, mem_prod, mem_univ, true_and, hmatch, mem_ofPred_eq]
  simpa only [Measure.prod_prod, measure_univ, one_mul, he] using hh

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasepointCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual changed-center sampling law

The deterministic inclusion is isolated from its measure-theoretic use.
The conclusion concerns the translated and conjugated ordinary Haar cell,
with the exact volume ratio of the suffix cell.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Independent smaller-cell and suffix sampling dominates the actual
nilpotent factor after changing the ambient basepoint. -/
theorem basepoint_cell_domination
    {N D : Type} [Group N] [Group D] [MeasurableSpace N] [MeasurableMul₂ N]
    (φ : D →* MulAut N) (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (ν : ProbabilityMeasure N) (A : Set N)
    (hA : ∀ᵐ a ∂(ν : Measure N), a ∈ A)
    (C B : Set N) (hC : MeasurableSet C) (hB : MeasurableSet B)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hB0 : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (u : N) (d : D)
    (hcover : ∀ a₀ ∈ A, ∀ a ∈ C, (φ d a₀)⁻¹ * u⁻¹ * a ∈ B)
    (S : Set N) (hS : MeasurableSet S) :
    let K := (φ d) ⁻¹' B
    (cellProbabilityMeasure μ C hC0 hCfin : Measure N)
        ((fun a => φ d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      (μ B / μ C) * (ν : Measure N).prod
        (cellProbabilityMeasure μ K
          (by rw [(hφ d).measure_preimage hB.nullMeasurableSet]; exact hB0)
          (by rw [(hφ d).measure_preimage hB.nullMeasurableSet]; exact hBfin) : Measure N)
        {p | p.1 * p.2 ∈ S} := by
  dsimp only
  have hK0 : μ ((φ d) ⁻¹' B) ≠ 0 := by
    rw [(hφ d).measure_preimage hB.nullMeasurableSet]
    exact hB0
  have hKfin : μ ((φ d) ⁻¹' B) ≠ ∞ := by
    rw [(hφ d).measure_preimage hB.nullMeasurableSet]
    exact hBfin
  have h := translated_cell_domination ν A hA μ C ((φ d) ⁻¹' B)
    hC hC0 hCfin hK0 hKfin
    (fun a => φ d⁻¹ (u⁻¹ * a))
    ((hφ d⁻¹).measurable.comp (measurable_const.mul measurable_id))
    (fun a k => u * φ d (a * k)) (fun a k => a * k)
    (by
      intro a ha
      simpa only [Function.comp_def, map_mul, mul_assoc] using
        (measurePreserving_mul_left μ (u * φ d a)).comp (hφ d))
    (by
      intro a ha k hk
      change φ d k ∈ B
      have hc := hcover a ha (u * φ d (a * k)) hk
      simpa only [map_mul, mul_assoc, inv_mul_cancel_left] using hc)
    (measurable_fst.prodMk
      (measurable_const.mul ((hφ d).measurable.comp (measurable_fst.mul measurable_snd))))
    (by intro a k; simp)
    S hS
  rwa [(hφ d).measure_preimage hB.nullMeasurableSet] at h

/-- The conjugated suffix cell can be packaged as a probability law, with
any established upper bound for its exact Haar-volume ratio. -/
theorem exists_basepoint_cell_domination
    {N D : Type} [Group N] [Group D] [MeasurableSpace N] [MeasurableMul₂ N]
    (φ : D →* MulAut N) (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (νA : ProbabilityMeasure N) (A : Set N)
    (hA : ∀ᵐ a ∂(νA : Measure N), a ∈ A)
    (C B : Set N) (hC : MeasurableSet C) (hB : MeasurableSet B)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hB0 : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (u : N) (d : D)
    (hcover : ∀ a₀ ∈ A, ∀ a ∈ C, (φ d a₀)⁻¹ * u⁻¹ * a ∈ B)
    {K : ℝ≥0∞} (hratio : μ B / μ C ≤ K) :
    ∃ ν : ProbabilityMeasure N,
      (∀ᵐ k ∂(ν : Measure N), φ d k ∈ B) ∧
      ∀ S : Set N, MeasurableSet S →
      (cellProbabilityMeasure μ C hC0 hCfin : Measure N)
        ((fun a => φ d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      K * (νA : Measure N).prod (ν : Measure N) {p | p.1 * p.2 ∈ S} := by
  let Q := (φ d) ⁻¹' B
  have hQ : MeasurableSet Q := (hφ d).measurable hB
  have hQmass : μ Q = μ B := (hφ d).measure_preimage hB.nullMeasurableSet
  have hQ0 : μ Q ≠ 0 := hQmass ▸ hB0
  have hQfin : μ Q ≠ ∞ := hQmass ▸ hBfin
  let ν := cellProbabilityMeasure μ Q hQ0 hQfin
  refine ⟨ν, ?_, ?_⟩
  · exact ae_mem_cellProbabilityMeasure μ Q hQ hQ0 hQfin
  · intro S hS
    exact (basepoint_cell_domination φ μ hφ νA A hA C B hC hB
      hC0 hCfin hB0 hBfin u d hcover S hS).trans (mul_le_mul' hratio le_rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasepointProfileIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact basepoint changes for the sampled height profiles -/

namespace PolycyclicRecognition

/-- A change of ambient basepoint by `u d` conjugates the nilpotent sample
and left translates the Cartan sample. Factor overlap is allowed. -/
theorem factor_basepoint_change
    {N D G : Type} [Group N] [Group D] [Group G]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (u a : N) (d z : D) :
    (x * (ι u * κ d)) * ι (φ d⁻¹ (u⁻¹ * a)) * κ (d⁻¹ * z) =
      x * ι a * κ z := by
  rw [hconj, map_inv, map_mul, map_inv, map_mul, map_inv]
  group

/-- Matched sample points have exactly the same unnormalized value.
Only the two deterministic center values differ. -/
theorem rescaled_profile_basepoint_change
    {G W Z Z' : Type} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x y a b : G) (φ : Z → G) (ψ : Z' → G)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : Z) (z' : Z')
    (hpoint : x * a * φ z = y * b * ψ z') :
    r • rescaledMapProfile J x a (Real.log r) φ z =
      s • rescaledMapProfile J y b (Real.log s) ψ z' + (J y - J x) := by
  simp only [rescaledMapProfile, Real.exp_log hr, Real.exp_log hs, smul_smul,
    mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hs.ne', one_smul]
  rw [hpoint]
  abel

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DominatedProfileConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring affine approximation through a dominated sampling law -/

namespace PolycyclicRecognition
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Ordinary affine approximation and suffix concentration give the same
approximation for a changed sampling law dominated by the independent
starting-point and suffix distribution. -/
theorem dominated_profile_concentration
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ ν : ℕ → ProbabilityMeasure X) (ξ : ℕ → Measure X)
    (ψ : ℕ → X → X) (m : ℕ → X → X → X)
    (f : ℕ → X → Y) (a : ℕ → Y)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (f n x) (a n)})
    (hdom : ∀ᶠ n in atTop, ∀ S : Set X, MeasurableSet S →
      ξ n (ψ n ⁻¹' S) ≤ K * (μ n : Measure X).prod (ν n : Measure X)
        {p | m n p.1 p.2 ∈ S})
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (f n x) (a n)}) atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n (m n p.1 p.2)) (f n p.1)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ξ n {x | ε ≤ dist (f n (ψ n x)) (a n)}) atTop (𝓝 0) := by
  have ho : ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | η ≤ dist (f n p.1) (a n)}) atTop (𝓝 0) := by
    intro η hη
    have he n : {p : X × X | η ≤ dist (f n p.1) (a n)} =
        {x | η ≤ dist (f n x) (a n)} ×ˢ univ := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, mul_one] using hordinary η hη
  have hp := bad_distance_triangle_tendsto_zero
    (fun n => (μ n : Measure X).prod (ν n : Measure X))
    (fun n p => f n (m n p.1 p.2)) (fun n p => f n p.1) (fun n _ => a n)
    hsuffix ho ε hε
  have hlim := ENNReal.Tendsto.const_mul hp (Or.inr hK)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hdom] with n hn
  exact hn _ (hmeas n ε)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DominatedAffineComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine comparison under the changed-center sampling law -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The proved density domination and suffix concentration transport the
target affine approximant to the source law, where the exact chart identity
compares the two deterministic approximants. -/
theorem deterministic_distance_tendsto_zero_of_dominated_transport
    {X Y Z : Type} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (ξ μ ν : ℕ → ProbabilityMeasure X) (a : ℕ → Y) (b : ℕ → Z)
    (f : ℕ → X → Y) (g : ℕ → X → Z) (ψ : ℕ → X → X)
    (m : ℕ → X → X → X) (H : ℕ → Z → Y)
    {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ᶠ n in atTop, ∀ x, f n x = H n (g n (ψ n x)))
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (g n x) (b n)})
    (hdom : ∀ᶠ n in atTop, ∀ S : Set X, MeasurableSet S →
      (ξ n : Measure X) (ψ n ⁻¹' S) ≤ D * (μ n : Measure X).prod (ν n : Measure X)
        {p | m n p.1 p.2 ∈ S})
    (hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ξ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (g n (m n p.1 p.2)) (g n p.1)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  have hsource' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ξ n : Measure X) {x | ε ≤ dist (a n) (H n (g n (ψ n x)))}) atTop (𝓝 0) := by
    intro ε hε
    apply (hsource ε hε).congr'
    filter_upwards [hmatch] with n hn
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, hn x]
  apply deterministic_distance_tendsto_zero_of_exact_transport ξ a b
    (fun n x => H n (g n (ψ n x)))
    (fun n x => g n (ψ n x)) H hK hH (fun _ _ => rfl) hsource'
  intro ε hε
  exact dominated_profile_concentration μ ν (fun n => (ξ n : Measure X)) ψ m g b
    hD hmeas hdom hordinary hsuffix hε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DominatedAffineLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite labels and normalized center error from dominated sampling -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

/-- The density bound, the two concentration statements and the exact chart
identities give both eventual equality of labels and a vanishing center
error. No height conclusion is assumed. -/
theorem affine_labels_center_error_of_dominated_transport
    {X V W L : Type} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (q : V →L[ℝ] W) (hq : Function.Surjective q)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (ξ μ ν : ℕ → ProbabilityMeasure X)
    (a a' : ℕ → L) (b b' c v : ℕ → W) {t : ℝ} (ht : 0 < t)
    (φ : ℕ → C(closedBall (0 : V) R, closedBall (0 : V) S))
    (ψ : ℕ → X → X) (m : ℕ → X → X → X)
    (f : ℕ → X → C(closedBall (0 : V) R, W))
    (g : ℕ → X → C(closedBall (0 : V) S, W))
    (hheight : ∀ᶠ n in atTop, ∀ z, t • q (φ n z) = q z - v n)
    (hmatch : ∀ᶠ n in atTop, ∀ x,
      f n x = transportCompactProfile t (φ n) (c n) (g n (ψ n x)))
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (g n x)
      (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))})
    (hdom : ∀ᶠ n in atTop, ∀ U : Set X, MeasurableSet U →
      (ξ n : Measure X) (ψ n ⁻¹' U) ≤ D *
        (μ n : Measure X).prod (ν n : Measure X) {p | m n p.1 p.2 ∈ U})
    (hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure X)
      {x | ε ≤ dist (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
        (f n x)}) atTop (𝓝 0))
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure X)
      {x | ε ≤ dist (g n x)
        (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))})
      atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (g n (m n p.1 p.2)) (g n p.1)}) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => c n - A (a' n) (v n)) atTop (𝓝 0) := by
  have hd := deterministic_distance_tendsto_zero_of_dominated_transport ξ μ ν
    (fun n => linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
    (fun n => linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))
    f g ψ m (fun n => transportCompactProfile t (φ n) (c n)) ht
    (fun n u w => by
      simpa only [abs_of_pos ht] using dist_transportCompactProfile_le t (φ n) (c n) u w)
    hmatch hD hmeas hdom hsource hordinary hsuffix
  obtain ⟨heq, hoff⟩ := affine_labels_offsets_of_chart_transport q hq A hA hR hS
    a a' b b' c v (fun _ => t) φ hheight hd
  exact ⟨heq, center_error_tendsto_zero_of_offsets A a' b b' c v t hb hb' hoff⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_EventualSupportedSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent suffix sampling with eventual support conditions -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The initial finitely many laws need not be carried by the permitted
sets. The same selection argument applies after the eventual support bound. -/
theorem independent_eventually_supported_bad_probability_tendsto_zero
    {A K : ℕ → Type} [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (K n)]
    (μ : ∀ n, ProbabilityMeasure (A n)) (ν : ∀ n, ProbabilityMeasure (K n))
    (D : ∀ n, Set (K n)) (hne : ∀ n, (D n).Nonempty)
    (hcarried : ∀ᶠ n in atTop, ∀ᵐ k ∂(ν n : Measure (K n)), k ∈ D n)
    (B : ∀ n, Set (A n × K n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ∀ n, K n, (∀ n, k n ∈ D n) →
      Tendsto (fun n => (μ n : Measure (A n)) ((fun a => (a, k n)) ⁻¹' B n))
        atTop (𝓝 0)) :
    Tendsto (fun n => (μ n : Measure (A n)).prod (ν n : Measure (K n)) (B n))
      atTop (𝓝 0) := by
  let : ∀ n, Nonempty (D n) := fun n => (hne n).to_subtype
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact False.elim ((not_lt_of_ge bot_le) hc)
  · intro c hc
    obtain ⟨d, hd0, hdc⟩ := exists_between hc
    have hb := eventually_uniform_lt_of_all_selections
      (fun n (k : D n) => (μ n : Measure (A n)) ((fun a => (a, k.val)) ⁻¹' B n))
      (fun k => hp (fun n => (k n).val) (fun n => (k n).property)) hd0
    filter_upwards [hb, hcarried] with n hn hν
    apply lt_of_le_of_lt _ hdc
    rw [Measure.prod_apply_symm (hB n)]
    calc
      _ ≤ ∫⁻ _, d ∂(ν n : Measure (K n)) := by
        apply lintegral_mono_ae
        filter_upwards [hν] with k hk
        exact (hn ⟨k, hk⟩).le
      _ = d := by simp

/-- Choose the actual eventual geometric witnesses, filling unused early
indices arbitrarily. -/
theorem exists_eventually_chosen_sequence
    {X : ℕ → Type} [∀ n, Nonempty (X n)] (P : ∀ n, X n → Prop)
    (hP : ∀ᶠ n in atTop, ∃ x, P n x) :
    ∃ x : ∀ n, X n, ∀ᶠ n in atTop, P n (x n) := by
  classical
  let x := fun n => if h : ∃ x, P n x then h.choose else Classical.choice (inferInstance : Nonempty (X n))
  refine ⟨x, ?_⟩
  filter_upwards [hP] with n hn
  dsimp only [x]
  rw [dite_eq_left hn]
  exact hn.choose_spec

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarMeasureTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of an invariant automorphism to the section-coordinate Haar measure -/

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- A map preserving one Haar measure preserves every Haar normalization.
This permits use of the Haar measure constructed from ideal-section coordinates. -/
theorem measurePreserving_of_haarMeasure (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] (f : G → G)
    (hf : MeasurePreserving f μ μ) : MeasurePreserving f ν ν := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  refine ⟨hf.measurable, ?_⟩
  rw [Measure.map_smul, hf.map_eq]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedScaleBasisBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate comparison from the actual exponential widths -/

namespace PolycyclicRecognition
open Module

/-- Only the products of physical scale and word cost matter for a box. -/
theorem norm_exponentialRescaleBasis_le_of_exponents_le
    {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (u v : J → ℝ) (r t : ℝ)
    (h : ∀ j, t * v j ≤ r * u j) (x : L) :
    ‖(exponentialRescaleBasis b u r).equivFun x‖ ≤
      ‖(exponentialRescaleBasis b v t).equivFun x‖ := by
  have hh := norm_change_exponentialRescaleBasis_le b (fun j => r * u j)
    (fun j => t * v j) zero_le_one (α := 0)
    (fun j => sub_nonpos.mpr (h j)) x
  simpa only [exponentialRescaleBasis, one_mul, mul_zero, Real.exp_zero] using hh

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartLeftShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact changes of basepoint in nilpotent exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped Manifold

variable {L E G W I : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

theorem wordChartLeftShift_point {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) (z : Fin n → ℝ) :
    exponentialCoordinates e chart target (wordChartLeftShift e chart source target k z) =
      k⁻¹ * exponentialCoordinates e chart source z :=
  (exponentialCoordinates e chart target).apply_symm_apply _

variable [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]

/-- Height under this change of basepoint is exactly affine, at the two
physical scales. This identity is separate from metric compatibility. -/
theorem wordChartLeftShift_height
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (π : G →* Multiplicative W) (height : L →ₗ[ℝ] W)
    (hheight : ∀ v, (π (chart (e v))).toAdd = height v)
    (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (k : G)
    (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log s)
    s • height (b.equivFun.symm (wordChartLeftShift e chart br bs k z)) =
      r • height (b.equivFun.symm z) - (π k).toAdd := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
  let bs := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log s)
  have hp := congrArg (fun g => (π g).toAdd) (wordChartLeftShift_point e chart br bs k z)
  simp only [exponentialCoordinates_apply, hheight, map_mul, map_inv,
    toAdd_mul, toAdd_inv] at hp
  rw [word_length_chart_height X S β height hkill hs,
    word_length_chart_height X S β height hkill hr] at hp
  exact hp.trans (by abel)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordBallLeftShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact-ball restriction of the actual changed-center chart -/

noncomputable section
namespace PolycyclicRecognition

open Module Metric
open scoped Manifold

variable {L E G W I : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

variable [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]

/-- Normalizing the exact two-scale height identity produces the affine
translation required by the finite-label comparison. -/
theorem wordChartLeftShift_normalized_height
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (π : G →* Multiplicative W) (height : L →ₗ[ℝ] W)
    (hheight : ∀ v, (π (chart (e v))).toAdd = height v)
    (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (k : G)
    (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log s)
    (s / r) • height (b.equivFun.symm (wordChartLeftShift e chart br bs k z)) =
      height (b.equivFun.symm z) - r⁻¹ • (π k).toAdd := by
  have hh := wordChartLeftShift_height e chart π height hheight hkill X S β hr hs k z
  simp only [← bracketWordExponent_one] at hh
  have he := congrArg (fun w : W => r⁻¹ • w) hh
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at he
  simpa only [div_eq_mul_inv, mul_comm] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordBallSamplingSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting actual bounded chart maps at eventual sampling scales -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Metric
open scoped Manifold Topology

/-- The geometric witnesses can be selected along a sequence together with
continuous compact-ball chart maps. Early indices impose no conditions. -/
theorem exists_wordBall_sampling_sequence
    {L E G N : Type} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
    [MeasurableSpace N] [Nonempty N]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    {d : ℕ} (source target : ℕ → Basis (Fin d) ℝ L)
    {R S : ℝ} (hS : 0 ≤ S)
    (P : ℕ → N → G → ProbabilityMeasure N → Prop)
    (hP : ∀ᶠ n in atTop, ∃ (u : N) (k : G) (ν : ProbabilityMeasure N),
      P n u k ν ∧ ∀ z : Fin d → ℝ, ‖z‖ ≤ R →
        ‖wordChartLeftShift e chart (source n) (target n) k z‖ ≤ S) :
    ∃ (u : ℕ → N) (k : ℕ → G) (ν : ℕ → ProbabilityMeasure N)
      (φ : ℕ → C(closedBall (0 : Fin d → ℝ) R, closedBall (0 : Fin d → ℝ) S)),
      ∀ᶠ n in atTop, P n (u n) (k n) (ν n) ∧ ∀ z,
        (φ n z : Fin d → ℝ) = wordChartLeftShift e chart (source n) (target n) (k n) z := by
  classical
  let Z := C(closedBall (0 : Fin d → ℝ) R, closedBall (0 : Fin d → ℝ) S)
  let : Nonempty Z := ⟨ContinuousMap.const _ ⟨0, mem_closedBall_self hS⟩⟩
  let : Nonempty (ProbabilityMeasure N) :=
    ⟨⟨Measure.dirac (Classical.choice (inferInstance : Nonempty N)), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩⟩
  let Q := fun n (v : N × G × ProbabilityMeasure N × Z) =>
    P n v.1 v.2.1 v.2.2.1 ∧ ∀ z,
      (v.2.2.2 z : Fin d → ℝ) = wordChartLeftShift e chart (source n) (target n) v.2.1 z
  have hQ : ∀ᶠ n in atTop, ∃ v, Q n v := by
    filter_upwards [hP] with n hn
    obtain ⟨u, k, ν, hp, hbound⟩ := hn
    exact ⟨⟨u, k, ν, wordBallLeftShift e chart (source n) (target n) k R S hbound⟩,
      hp, fun _ => rfl⟩
  obtain ⟨v, hv⟩ := exists_eventually_chosen_sequence Q hQ
  exact ⟨(fun n => (v n).1), (fun n => (v n).2.1), (fun n => (v n).2.2.1),
    (fun n => (v n).2.2.2), hv⟩

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual residual automorphism

We identify the residual automorphism on a nonzero root with the analytic
exponential already estimated there. This removes a separate bound premise
for the automorphisms constructed from the Cartan action.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r1270f6_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- Inclusion intertwines the root residual operator and the actual ideal
derivation. -/
theorem rootInIdeal_residual_apply (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((rootAction H χ h - χ h • 1) v) =
      cartanIdealResidualDerivation T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  apply Subtype.ext
  change (((rootAction H χ h - χ h • 1) v : rootSpace H χ) : L) =
    cartanResidualDerivation T H h (v : L)
  rw [cartanResidualDerivation_apply_root T H h χ v.property]
  rfl

set_option maxHeartbeats 1000000 in
theorem rootInIdeal_residual_pow (h : H) (k : ℕ) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ (((rootAction H χ h - χ h • 1) ^ k) v) =
      ((cartanIdealResidualDerivation T H h).toLinearMap ^ k)
        (CartanWordModel.rootInIdeal χ hχ v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, rootInIdeal_residual_apply,
      pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
include T hχ in
/-- The ambient dimension also truncates the analytic root operator. -/
theorem rootResidual_pow_ambient_dim (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hinj : Function.Injective (CartanWordModel.rootInIdeal χ hχ) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : cartanRootIdeal H => (z : L)) hxy)
  apply hinj
  rw [rootInIdeal_residual_pow T H χ hχ h (finrank ℝ L) v,
    cartanIdealResidualDerivation_pow_eq_zero T H h]
  simp

set_option maxHeartbeats 1000000 in
/-- The polynomial Lie automorphism agrees with the analytic root residual
exponential, so the earlier operator norm bounds apply to this automorphism. -/
theorem rootInIdeal_residual_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h - χ h • 1)) v) =
      cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_finite_sum_of_pow_eq_zero _ (rootResidual_pow_ambient_dim T H χ hχ h),
    cartanIdealResidualAutomorphism_apply]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootInIdeal_residual_pow]

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r1270f6_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The full action is the analytic adjoint exponential on each nonzero root. -/
theorem rootInIdeal_adjoint_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h)) v) =
      cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, map_smul, rootInIdeal_residual_exp T H χ hχ h v]
  apply Subtype.ext
  change Real.exp (χ h) •
      (cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
    cartanWeightScale T H h _
  exact (cartanWeightScale_apply_root T H h χ
    (cartanIdealResidualAutomorphism_root_mem T H h χ _ v.property)).symm

section Representation

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r1270f6_2 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The constructed action agrees with conjugation in a compatible algebra
representation on every generating root. -/
theorem represented_adjoint_root (j : L →ₗ⁅ℝ⁆ A) (h : H) (v : rootSpace H χ) :
    j (cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
      NormedSpace.exp (j h) * j v * NormedSpace.exp (-j h) := by
  rw [← rootInIdeal_adjoint_exp T H χ hχ h v]
  have hh := represented_root_flow H χ j h 1 v
  simp only [one_smul] at hh
  exact hh

set_option maxHeartbeats 1000000 in
omit hχ χ in
/-- Lie generation extends the root calculation to every vector in the
nilpotent ideal. -/
theorem represented_adjoint_ideal (j : L →ₗ⁅ℝ⁆ A) (h : H) (x : cartanRootIdeal H) :
    j (cartanIdealAdjointAutomorphism T H h x : L) =
      NormedSpace.exp (j h) * j x * NormedSpace.exp (-j h) := by
  let u := algebraExpUnit (j h)
  change j (cartanIdealAdjointAutomorphism T H h x : L) =
    (u : A) * j x * (↑(u⁻¹) : A)
  have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) := by
    rw [cartanGeneratorPool_lieSpan H T]
    trivial
  have hmul (a b : A) :
      ((u : A) * a * (↑(u⁻¹) : A)) * ((u : A) * b * (↑(u⁻¹) : A)) =
        (u : A) * (a * b) * (↑(u⁻¹) : A) := by
    calc
      _ = (u : A) * a * ((↑(u⁻¹) : A) * u) * b * (↑(u⁻¹) : A) := by
        simp only [mul_assoc]
      _ = _ := by simp only [Units.inv_mul, mul_one, mul_assoc]
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, hx⟩ := hx
    have he : CartanWordModel.rootInIdeal ψ hψ ⟨x, hx⟩ = x := Subtype.ext rfl
    have hh := represented_adjoint_root T H ψ hψ j h ⟨x, hx⟩
    rw [he] at hh
    exact hh
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero, zero_mul]
  | add x y _ _ hx hy =>
    simpa only [map_add, AddMemClass.coe_add, mul_add, add_mul] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    simpa only [map_smul, SetLike.val_smul, smul_mul_assoc, mul_smul_comm,
      RingHom.id_apply] using congrArg (a • ·) hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    change j ⁅(cartanIdealAdjointAutomorphism T H h x : L),
      (cartanIdealAdjointAutomorphism T H h y : L)⁆ =
        (u : A) * j ⁅(x : L), (y : L)⁆ * (↑(u⁻¹) : A)
    rw [j.map_lie, j.map_lie, hx, hy]
    simp only [Ring.lie_def, mul_sub, sub_mul, hmul]

end Representation

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- Compatibility of exponentials in a faithful representation identifies
the constructed automorphism with actual ambient conjugation. -/
theorem adjointGroupAutomorphism_eq_conjugation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ι : N →* G) (d : H → G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ι (Exp (eN x))) = algebraExpUnit (j x))
    (hd : ∀ h, ρ (d h) = algebraExpUnit (j h)) (h : H) (g : N) :
    ι (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g) =
      d h * ι g * (d h)⁻¹ := by
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  apply hρ
  change ρ (ι (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hN, map_mul, map_mul, map_inv, hd]
  change algebraExpUnit (j (cartanIdealAdjointAutomorphism T H h x : L)) =
    algebraExpUnit (j h) * ρ (ι (Exp (eN x))) * (algebraExpUnit (j h))⁻¹
  rw [hN]
  rw [represented_adjoint_ideal T H j h x]
  exact algebraExpUnit_conj (algebraExpUnit (j h)) (j x)

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBasepointProfileIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact changes of center for the actual Cartan profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.D.carrier]
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)

include hchartD

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I] in
/-- The group identity underlying basepoint comparison uses the actual
Cartan charts and the actual conjugation action. -/
theorem profileChart_basepoint_change
    (source target : Basis (Fin (finrank ℝ H)) ℝ H)
    (x : G) (u a : F.N.carrier) (k : F.D.carrier) (z : Fin (finrank ℝ H) → ℝ) :
    x * F.inclusionN a * F.profileChart source z =
      (x * (F.inclusionN u * F.inclusionD k)) *
        F.inclusionN (F.action k⁻¹ (u⁻¹ * a)) *
          F.profileChart target (wordChartLeftShift F.D.equiv chartD source target k z) := by
  have hp := wordChartLeftShift_point F.D.equiv chartD source target k z
  have hi := congrArg F.inclusionD hp
  simp only [exponentialCoordinates_apply, hchartD, map_mul, map_inv] at hi
  change F.profileChart target (wordChartLeftShift F.D.equiv chartD source target k z) =
    (F.inclusionD k)⁻¹ * F.profileChart source z at hi
  have hf := factor_basepoint_change F.action F.inclusionN F.inclusionD F.conjugation
    x u a k (exponentialCoordinates F.D.equiv chartD source z)
  simp only [map_mul, map_inv, exponentialCoordinates_apply, hchartD] at hf
  rw [hi]
  simpa only [profileChart, map_mul, map_inv] using hf.symm

set_option maxHeartbeats 1000000 in
/-- The raw normalized profiles satisfy the exact change-of-center identity;
all errors arise later from affine approximation, not from this formula. -/
theorem realScaleProfile_basepoint_change
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J)
    (x : G) (u a : F.N.carrier) (k : F.D.carrier)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (z : Fin (finrank ℝ H) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log s)
    let y := x * (F.inclusionN u * F.inclusionD k)
    r • F.realScaleProfile hD J hJ x X S β r a z =
      s • F.realScaleProfile hD J hJ y X S β s (F.action k⁻¹ (u⁻¹ * a))
        (wordChartLeftShift F.D.equiv chartD br bs k z) + (J y - J x) := by
  dsimp only
  simp only [realScaleProfile_apply, max_eq_left (Real.log_nonneg hr),
    max_eq_left (Real.log_nonneg hs)]
  apply rescaled_profile_basepoint_change J x _ (F.inclusionN a) _ _ _
    (zero_lt_one.trans_le hr) (zero_lt_one.trans_le hs) z _
  exact F.profileChart_basepoint_change chartD hchartD _ _ x u a k z

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBasepointAffineComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-label comparison for the actual changed Cartan profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module MeasureTheory Filter Metric Set
open scoped Manifold Topology ENNReal

variable {EG G W I L : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [DecidableEq I] [Fintype L] [Nonempty L]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier] [Fintype L] [Nonempty L] [FiniteDimensional ℝ W] in
/-- Continuity in the nilpotent sample, including restriction to any compact
chart. This supplies all measurable bad sets below. -/
theorem continuous_realScaleProfile_restrict
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (Z : Set (Fin (finrank ℝ H) → ℝ)) :
    Continuous (fun k => (F.realScaleProfile hD J hJ x X S β r k).restrict Z) :=
  (ContinuousMap.continuous_restrict Z).comp
    ((continuous_rescaledContinuousProfile J hJ x (max (Real.log r) 0)
      (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
      (F.continuous_profileChart hD _)).comp F.closedN.continuous)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] [IsTopologicalGroup F.N.carrier] in
/-- The actual chart and group identities turn affine concentration into
agreement of finite labels and a sublinear center-height error. The sampling
and concentration assumptions are supplied by the preceding proved bridges. -/
theorem basepoint_affine_labels_of_sampling
    (hD : Continuous F.ExpD)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (π : G →* Multiplicative W) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height)
    (hchartheight : ∀ v, (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v)
    (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {R R' t : ℝ} (hR : 0 < R) (hR' : 0 < R') (ht : 0 < t)
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (htr : ∀ᶠ n in atTop, 1 ≤ t * r n)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x y : ℕ → G)
    (u : ℕ → F.N.carrier) (k : ℕ → F.D.carrier)
    (hfactor : ∀ᶠ n in atTop, y n = x n * (F.inclusionN (u n) * F.inclusionD (k n)))
    (hkheight : ∀ᶠ n in atTop,
      (π (F.inclusionD (k n))).toAdd = (π ((x n)⁻¹ * y n)).toAdd)
    (φ : ℕ → C(closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
      closedBall (0 : Fin (finrank ℝ H) → ℝ) R'))
    (hφ : ∀ᶠ n in atTop, ∀ z,
      (φ n z : Fin (finrank ℝ H) → ℝ) = wordChartLeftShift F.D.equiv chartD
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (r n)))
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (t * r n)))
        (k n) z)
    (ξ μ ν : ℕ → ProbabilityMeasure F.N.carrier) {D : ℝ≥0∞} (hDfinite : D ≠ ∞)
    (hdom : ∀ᶠ n in atTop, ∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action (k n)⁻¹ ((u n)⁻¹ * a)) ⁻¹' U) ≤
        D * (μ n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
          {p | p.1 * p.2 ∈ U})
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0)) :
    let q := (height.comp (WordBasisSelections.basis X S β).equivFun.symm.toLinearMap).toContinuousLinearMap
    let raw := fun n z => F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z
    let raw' := fun n z => F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n) z
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure F.N.carrier)
      {z | ε ≤ dist (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
        ((raw n z).restrict (closedBall 0 R))}) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure F.N.carrier)
      {z | ε ≤ dist ((raw' n z).restrict (closedBall 0 R'))
        (linearBallProfile q (A (a' n)) R' + ContinuousMap.const _ (b' n))}) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
      {p | ε ≤ dist ((raw' n (p.1 * p.2)).restrict (closedBall 0 R'))
        ((raw' n p.1).restrict (closedBall 0 R'))}) atTop (𝓝 0)) →
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => (r n)⁻¹ • (J n (y n) - J n (x n) -
        A (a' n) ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  dsimp only
  intro hsource hord hsuffix
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let c := fun n => (r n)⁻¹ • (J n (y n) - J n (x n))
  let v := fun n => (r n)⁻¹ • (π ((x n)⁻¹ * y n)).toAdd
  let f := fun n z => (F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z).restrict (closedBall 0 R)
  let g := fun n z => (F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n) z).restrict (closedBall 0 R')
  have hq : Function.Surjective q := hheight.comp bD.equivFun.symm.surjective
  have hnormalized : ∀ n, (t * r n) / r n = t := fun n =>
    mul_div_cancel_right₀ t (ne_of_gt (zero_lt_one.trans_le (hr n)))
  have hheight' : ∀ᶠ n in atTop, ∀ z, t • q (φ n z) = q z - v n := by
    filter_upwards [hφ, htr, hkheight] with n hn htn hk z
    change t • height (bD.equivFun.symm (φ n z)) =
      height (bD.equivFun.symm z) - (r n)⁻¹ • (π ((x n)⁻¹ * y n)).toAdd
    have hh := wordChartLeftShift_normalized_height F.D.equiv chartD
      (π.comp F.inclusionD) height hchartheight hkill X S β
      (zero_lt_one.trans_le (hr n)) (zero_lt_one.trans_le htn) (k n) z
    simpa only [hnormalized, ← hn z, MonoidHom.comp_apply, hk, q, bD, v,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply] using hh
  have hmatch : ∀ᶠ n in atTop, ∀ z,
      f n z = transportCompactProfile t (φ n) (c n)
        (g n (F.action (k n)⁻¹ ((u n)⁻¹ * z))) := by
    filter_upwards [hφ, hfactor, htr] with n hn hy htn z
    ext w
    change F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z w =
      t • F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n)
        (F.action (k n)⁻¹ ((u n)⁻¹ * z)) (φ n w) + c n
    have hh := F.realScaleProfile_basepoint_change chartD hchartD hD (J n) (hJ n)
      (x n) (u n) z (k n) X S β (hr n) htn w
    dsimp only at hh
    rw [← hy, ← hn w] at hh
    have he := congrArg (fun z : W => (r n)⁻¹ • z) hh
    have hs : (r n)⁻¹ * (t * r n) = t := by
      rw [mul_comm, ← div_eq_mul_inv, hnormalized]
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le (hr n))),
      one_smul, hs] using he
  have hmeas n ε : MeasurableSet {z | ε ≤ dist (g n z)
      (linearBallProfile q (A (a' n)) R' + ContinuousMap.const _ (b' n))} := by
    exact (isClosed_Ici.preimage ((F.continuous_realScaleProfile_restrict hD (J n)
      (hJ n) (y n) X S β (t * r n) (closedBall 0 R')).dist continuous_const)).measurableSet
  obtain ⟨heq, herr⟩ := affine_labels_center_error_of_dominated_transport q hq A hA hR hR'
    ξ μ ν a a' b b' c v ht φ (fun n z => F.action (k n)⁻¹ ((u n)⁻¹ * z))
    (fun _ z z' => z * z') f g hheight' hmatch hDfinite hmeas hdom hsource hord hsuffix hb hb'
  refine ⟨heq, ?_⟩
  simpa only [c, v, map_smul, ← smul_sub] using herr

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxRadiusVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact radius dependence of the original coordinate Haar boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

theorem exponential_box_radius_volume
    {L E G : Type} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal R ^ n *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR,
    exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one,
    exponential_basis_subset_measure e Exp chart hchart,
    exponential_basis_subset_measure e Exp chart hchart]
  have hcube : volume (Icc (fun _ : Fin n => -R) (fun _ => R)) =
      ENNReal.ofReal R ^ n * volume (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) := by
    simp only [Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    simp only [mul_one]
    exact mul_comm _ _
  rw [hcube]
  ac_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxRadiusProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite probabilities and exact ratios for larger Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem groupBox_radius_properties
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) {R : ℝ} (hR : 0 < R) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R
    let C := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
    MeasurableSet Q ∧ μ Q ≠ 0 ∧ μ Q ≠ ∞ ∧
      μ Q / μ C = ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) := by
  dsimp only
  have hu := M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ E β r 1
  simp only [mul_one, image_id'] at hu
  have hv := exponential_box_radius_volume F.N.equiv F.ExpN chartN hchartN b₀
    (M.boxBasis T hunimod eW E β r) hR.le
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  change μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R) =
    ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) *
      μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1) at hv
  have hme := measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN
    chartN hchartN (M.boxBasis T hunimod eW E β r) 1
  simp only [mul_one] at hme
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ R hR.le]
    exact hme.measurableSet_image.mpr measurableSet_Icc
  · rw [hv]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hR).ne') hu.2.1
  · rw [hv]
    exact ENNReal.mul_ne_top (by simp) hu.2.2
  · rw [hv, ENNReal.mul_div_cancel_right hu.2.1 hu.2.2]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of actual Cartan conjugation

The nilpotent residual exponential has determinant one. The scalar weight
factors multiply to one by the already proved trace balance. Consequently
conjugation on the nilpotent Cartan ideal preserves coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- The nonsemisimple part of the actual Cartan action has Jacobian one. -/
theorem det_cartanIdealResidualAutomorphism (h : H) :
    LinearMap.det (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  exact det_nilpotent_exp (cartanIdealResidualDerivation T H h).toLinearMap
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

namespace CartanWordModel

variable (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The diagonal scalar action has Jacobian given by the total word weight. -/
theorem det_idealWeightDilation (β : M.Bases) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap =
      Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  let F := (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
  let v := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val j))
  have hb (j) : F (b j) = v j • b j := by
    have hh := M.idealWeightDilation_word T h (β.val j)
    have he := WordBasisSelections.eval_words M.letter M.wordList β j
    change evalBracketWord M.letter (β.val j) = b j at he
    rw [he] at hh
    exact hh
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal v := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hb, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

set_option maxHeartbeats 1000000 in
include M in
/-- Unimodularity makes all word-basis scalar Jacobians equal to one. -/
theorem det_idealWeightDilation_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap = 1 := by
  let β : M.Bases := Classical.choice inferInstance
  rw [M.det_idealWeightDilation T β h]
  have ht := trace_cartan_word_basis H M.letter M.weight M.letter_root
    (WordBasisSelections.basis M.letter M.wordList β)
    (WordBasisSelections.words M.letter M.wordList β)
    (WordBasisSelections.eval_words M.letter M.wordList β) h
  have hz := trace_cartanRootIdeal_eq_zero T H hunimod h
  have hs : (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) = 0 := by
    rw [ht] at hz
    simp only [bracketWordExponent]
    rw [Finset.sum_comm]
    simpa only [Nat.cast_sum, Finset.sum_mul, WordBasisSelections.words] using hz
  rw [hs, Real.exp_zero]

set_option maxHeartbeats 1000000 in
include M in
/-- The full actual Cartan action, rather than only its scalar part, has
Jacobian one on the nilpotent ideal. -/
theorem det_idealAdjointAutomorphism_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det ((cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap.comp
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, M.det_idealWeightDilation_eq_one T hunimod,
    det_cartanIdealResidualAutomorphism, mul_one]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHaarConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Haar measure for Cartan boxes and conjugation

The determinant computation gives exact invariance under the actual Cartan
adjoint automorphisms. The same measure retains the explicit weighted-box
volume, so the lower packing argument and box rates use compatible measures.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [hNsc : SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)
  (haar : NilpotentExponentialHaarInput EN N)

include hunimod haar hNsc

set_option maxHeartbeats 1000000 in
/-- One Haar measure has both the exact word-box formula and invariance
under every Cartan adjoint action. -/
theorem exists_haar_adjoint_invariant_weighted_boxes
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ μ : Measure N, μ.IsHaarMeasure ∧
      (∀ h : H, MeasurePreserving (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h) μ μ) ∧
      ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ eN)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) r) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  let _ : SimplyConnectedSpace N := hNsc
  have hn : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hn)
  let b := b₀.map eN.toLinearEquiv
  let f := (Exp ∘ eN) ∘ b₀.equivFun.symm
  have hf : f = Exp ∘ b.equivFun.symm := by
    funext t
    change Exp (eN (b₀.equivFun.symm t)) = Exp ((b₀.map eN.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  refine ⟨Measure.map f volume, ?_, ?_, ?_⟩
  · rw [hf]
    exact hhaar _ b
  · intro h
    exact exponentialConjugate_measurePreserving eN Exp hbij chart hc b₀
      (cartanIdealAdjointAutomorphism T H h) (M.det_idealAdjointAutomorphism_eq_one T hunimod h)
  · intro cost β r R hR
    exact exponentialCoordinate_weighted_box_measure eN Exp chart hc b₀ M.letter M.wordList
      cost β r R hR

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem exp_cartanLog (d : D) : ExpD (eD (cartanLog H eD ExpD hbijD d)) = d := by
  unfold cartanLog
  rw [eD.apply_symm_apply]
  exact (Equiv.ofBijective ExpD hbijD).apply_symm_apply d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled words in the actual semidirect product

Nilpotent Cartan increments give polynomial bounds on every Cartan prefix.
The exact semidirect-product formula then reduces its nilpotent coordinate
to the controlled product estimate. No polynomial bound on prefixes is left
as an assumption of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
omit [T2Space D] in
/-- The required semidirect action identity follows from compatible
exponentials in an ambient faithful representation. -/
theorem action_eq_adjoint_of_representation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hconj : ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) (d : D) :
    φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d) := by
  apply MulEquiv.ext
  intro g
  apply hιN
  rw [hconj]
  have hh := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
    j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
  simpa only [exp_cartanLog] using hh.symm

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The published representation identifies the actual factor action with
the explicit full Cartan adjoint automorphism. -/
theorem cartan_action_eq_adjoint_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (d : F.D.carrier) :
    F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD hbijD d) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  exact M.action_eq_adjoint_of_representation T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
    F.D.equiv F.ExpD hbijD F.action j ρ hρ F.inclusionN F.closedN.injective F.inclusionD
    F.conjugation (fun x => by rw [F.compatibleN, hExp])
    (fun x => by rw [F.compatibleD, hExp]) d

open Module LieAlgebra LieModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHaarInvariance
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Cartan factor action preserves the chosen Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold NNReal

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M

set_option maxHeartbeats 1000000 in
/-- Trace zero and the published realization imply that the original
factor action preserves every Haar normalization, including the measure
constructed in ideal/quotient section coordinates. -/
theorem action_preserves_haar
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure] (d : F.D.carrier) :
    MeasurePreserving (F.action d) μ μ := by
  classical
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let b := (finBasis ℝ (cartanRootIdeal H)).map F.N.equiv.toLinearEquiv
  let coordinates := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chartN
  let _ : LocallyCompactSpace F.N.carrier := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨ν, hν, hinv, _⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN haarN (finBasis ℝ (cartanRootIdeal H))
  let _ : ν.IsHaarMeasure := hν
  apply measurePreserving_of_haarMeasure ν μ (F.action d)
  rw [cartan_action_eq_adjoint_of_published_realization T M F hExp realize hbijN hbijD dynkinN d]
  exact hinv _

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBasepointCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Haar domination for the changed Cartan sampling cell -/

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
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
/-- The changed-center cell is dominated by independent smaller-cell and
conjugated-suffix sampling, with the exact factor `L ^ dim N`. -/
theorem exists_basepoint_groupBox_domination
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r s : ℝ) {L : ℝ} (hL : 0 < L)
    (u : F.N.carrier) (d : F.D.carrier)
    (hcover : ∀ a₀ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β s 1,
      ∀ a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1,
      (F.action d a₀)⁻¹ * u⁻¹ * a ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L) :
    ∃ ν : ProbabilityMeasure F.N.carrier,
      (∀ᵐ k ∂(ν : Measure F.N.carrier), F.action d k ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L) ∧
      ∀ S : Set F.N.carrier, MeasurableSet S →
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r 1 :
        Measure F.N.carrier) ((fun a => F.action d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      (ENNReal.ofReal L ^ finrank ℝ (cartanRootIdeal H)) *
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β s 1 :
          Measure F.N.carrier).prod (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ S} := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let _ : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let A := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β s 1
  let C := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
  let B := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L
  let μA := M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β s 1
  have hAp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β s zero_lt_one
  have hCp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β r zero_lt_one
  have hBp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β r hL
  have hφ := F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod μ
  have hA : ∀ᵐ a ∂(μA : Measure F.N.carrier), a ∈ A := by
    simpa only [μA, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure μ A hAp.1 hAp.2.1 hAp.2.2.1
  obtain ⟨ν, hν, hd⟩ := exists_basepoint_cell_domination F.action μ hφ μA A hA C B
    hCp.1 hBp.1 hCp.2.1 hCp.2.2.1 hBp.2.1 hBp.2.2.1 u d hcover hBp.2.2.2.le
  refine ⟨ν, hν, ?_⟩
  intro S hS
  simpa only [μA, translatedGroupBoxProbability, mul_one, image_id'] using hd S hS

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBasepointConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Basepoint comparison from the established concentration estimates -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {EG G W I L P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I] [Finite L] [Nonempty L]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]
  [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
/-- The deterministic conclusion of the basepoint argument, keeping the
already proved sampling geometry and concentration estimates separate. -/
theorem nearby_labels_of_concentration
    (hD : Continuous F.ExpD)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (π : G →* Multiplicative W) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height)
    (hchartheight : ∀ v, (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v)
    (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    (J : P → G → W) (hJ : ∀ p, Continuous (J p))
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {ρ R η t : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R) (ht : 0 < t)
    (μ : ℝ → ProbabilityMeasure F.N.carrier) (B : ℝ → Set F.N.carrier)
    (hne : ∀ r, (B r).Nonempty) {D : ℝ≥0∞} (hDfinite : D ≠ ∞)
    (C : ℝ → Set F.N.carrier) (hcompact : ∀ r, IsCompact (C r))
    (hfull : ∀ r, ∀ᵐ z ∂(μ r : Measure F.N.carrier), z ∈ C r)
    (hgeometry : ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ᵐ a ∂(ν : Measure F.N.carrier), a ∈ B (t * scale n)) ∧
        (∀ U : Set F.N.carrier, MeasurableSet U →
          (μ (scale n) : Measure F.N.carrier) ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' U) ≤
            D * (μ (t * scale n) : Measure F.N.carrier).prod (ν : Measure F.N.carrier)
              {p | p.1 * p.2 ∈ U}) ∧
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD
            (exponentialRescaleBasis (WordBasisSelections.basis X S β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n)))
            (exponentialRescaleBasis (WordBasisSelections.basis X S β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (t * scale n)))
            k z‖ ≤ R) :
    let Z := closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let q := (height.comp (WordBasisSelections.basis X S β).equivFun.symm.toLinearMap).toContinuousLinearMap
    let raw := fun (p : P × G) r => F.realScaleProfile hD (J p.1) (hJ p.1) p.2 X S β r
    let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
    let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
      (fun k => (raw p r k).restrict Z)
      (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
    (∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G),
      ∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw (p n, x n) (scale n) k).restrict Z)
        (linearBallProfile q (A (a n)) R + ContinuousMap.const Z (b (p n, x n) (scale n)))
          ∂(μ (scale n) : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, ∀ p r, r₀ ≤ r → ‖b p r‖ ≤ ε) →
    (∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G) (k : ℕ → F.N.carrier),
      (∀ n, k n ∈ B (scale n)) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ (scale n) : Measure F.N.carrier)
        {z | ε ≤ dist ((raw (p n, x n) (scale n) (z * k n)).restrict Z)
          ((raw (p n, x n) (scale n) z).restrict Z)}) atTop (𝓝 0)) →
    ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n, x n) (scale n) = label (p n, y n) (t * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n, y n) (t * scale n)) ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  classical
  let : Fintype L := Fintype.ofFinite L
  dsimp only
  intro hmean huniform hsuffix scale hscale hstrict hscale1 hsmall1 pair x y hxy
  let Z := closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let raw := fun (p : P × G) r => F.realScaleProfile hD (J p.1) (hJ p.1) p.2 X S β r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z)
    (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
  let small := fun n => t * scale n
  have hsmall : Tendsto small atTop atTop := hscale.const_mul_atTop ht
  have hsmallstrict : StrictMono small := fun i j hij => mul_lt_mul_of_pos_left (hstrict hij) ht
  let ξ := fun n => μ (scale n)
  let μ' := fun n => μ (small n)
  let suffixBox := fun n => B (small n)
  let test :=  fun n (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier) =>
    F.inclusionN u * F.inclusionD k = (x n)⁻¹ * y n ∧
    (π (F.inclusionD k)).toAdd = (π ((x n)⁻¹ * y n)).toAdd ∧
    (∀ᵐ z ∂(ν : Measure F.N.carrier), z ∈ suffixBox n) ∧
    (∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' U) ≤
        (D) *
          (μ' n : Measure F.N.carrier).prod (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ U})
  let source := fun n => exponentialRescaleBasis bD
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
  let target := fun n => exponentialRescaleBasis bD
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (small n))
  have hdata : ∀ᶠ n in atTop, ∃ (u : F.N.carrier) (k : F.D.carrier)
      (ν : ProbabilityMeasure F.N.carrier), test n u k ν ∧
      ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
        ‖wordChartLeftShift F.D.equiv chartD (source n) (target n) k z‖ ≤ R := by
    filter_upwards [hgeometry scale hscale hscale1] with n hn
    have hg : dist 1 ((x n)⁻¹ * y n) ≤ η * scale n := by
      have he := dist_mul_left ((x n)⁻¹) (x n) (y n)
      calc
        dist 1 ((x n)⁻¹ * y n) = dist (x n) (y n) := by
          simpa only [inv_mul_cancel] using he
        _ ≤ η * scale n := hxy n
    obtain ⟨u, k, ν, hf, hh, hν, hdom, hchart⟩ := hn ((x n)⁻¹ * y n) hg
    exact ⟨u, k, ν, ⟨hf, hh, hν, hdom⟩,
      fun z hz => hchart z hz⟩
  obtain ⟨u, k, ν, φ, hselected⟩ := exists_wordBall_sampling_sequence F.D.equiv chartD
    source target hR.le test hdata
  have hfactor : ∀ᶠ n in atTop, y n = x n * (F.inclusionN (u n) * F.inclusionD (k n)) := by
    filter_upwards [hselected] with n hn
    rw [hn.1.1, mul_inv_cancel_left]
  have hkheight : ∀ᶠ n in atTop,
      (π (F.inclusionD (k n))).toAdd = (π ((x n)⁻¹ * y n)).toAdd :=
    hselected.mono (fun _ hn => hn.1.2.1)
  have hdom : ∀ᶠ n in atTop, ∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action (k n)⁻¹ ((u n)⁻¹ * a)) ⁻¹' U) ≤
        (D) *
          (μ' n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier) {p | p.1 * p.2 ∈ U} :=
    hselected.mono (fun _ hn => hn.1.2.2.2)
  have hchart := hselected.mono (fun _ hn => hn.2)
  have hmean' (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (hsm : StrictMono s)
      (hs1 : ∀ n, 1 ≤ s n) (z : ℕ → G) :
      Tendsto (fun n => ∫ w, dist ((raw (pair n, z n) (s n) w).restrict Z)
        (linearBallProfile q (A (label (pair n, z n) (s n))) R +
          ContinuousMap.const Z (b (pair n, z n) (s n))) ∂(μ (s n) : Measure F.N.carrier))
        atTop (𝓝 0) := by
    exact canonicalAffineLabel_mean_tendsto_zero (fun n => (μ (s n) : Measure F.N.carrier))
      (fun n w => (raw (pair n, z n) (s n) w).restrict Z)
      (fun n l => linearBallProfile q (A l) R + ContinuousMap.const Z (b (pair n, z n) (s n)))
      (hmean s hs hsm hs1 pair z)

  have hprob (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (hsm : StrictMono s)
      (hs1 : ∀ n, 1 ≤ s n) (z : ℕ → G) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (μ (s n) : Measure F.N.carrier)
        {w | ε ≤ dist ((raw (pair n, z n) (s n) w).restrict Z)
          (linearBallProfile q (A (label (pair n, z n) (s n))) R +
            ContinuousMap.const Z (b (pair n, z n) (s n)))}) atTop (𝓝 0) := by
    exact compact_profile_probability_of_mean (fun n => μ (s n)) _
      (fun n => hcompact (s n)) (fun n => hfull (s n)) _ (fun n => F.continuous_realScaleProfile_restrict
        hD (J (pair n)) (hJ _) (z n)
        X S β (s n) Z) _ (hmean' s hs hsm hs1 z) hε
  have hb (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (z : ℕ → G) :
      Tendsto (fun n => b (pair n, z n) (s n)) atTop (𝓝 0) := by
    have hv := huniform
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨S, hS⟩ := hv (ε / 2) (half_pos hε)
    filter_upwards [hs.eventually_ge_atTop S] with n hn
    exact lt_of_le_of_lt (by simpa only [dist_zero_right] using hS (pair n, z n) (s n) hn)
      (half_lt_self hε)
  have hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure F.N.carrier)
      {z | ε ≤ dist (linearBallProfile q (A (label (pair n, x n) (scale n))) ρ +
        ContinuousMap.const _ (b (pair n, x n) (scale n)))
        ((raw (pair n, x n) (scale n) z).restrict (Metric.closedBall 0 ρ))}) atTop (𝓝 0) := by
    apply bad_probability_tendsto_zero_of_dist_le (fun n => (ξ n : Measure F.N.carrier))
      (fun n z => (raw (pair n, x n) (scale n) z).restrict Z)
      (fun n _ => linearBallProfile q (A (label (pair n, x n) (scale n))) R +
        ContinuousMap.const Z (b (pair n, x n) (scale n)))
      _ _ zero_lt_one
    · intro n z
      rw [one_mul, dist_comm]
      apply (ContinuousMap.dist_le dist_nonneg).mpr
      intro w
      let w' : Z := ⟨w, (Metric.closedBall_subset_closedBall hρR) w.property⟩
      exact ((raw (pair n, x n) (scale n) z).restrict Z).dist_apply_le_dist
        (g := linearBallProfile q (A (label (pair n, x n) (scale n))) R +
          ContinuousMap.const Z (b (pair n, x n) (scale n))) w'
    · exact hprob scale hscale hstrict hscale1 x
  have hsuffix' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ' n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
        {p | ε ≤ dist ((raw (pair n, y n) (small n) (p.1 * p.2)).restrict Z)
          ((raw (pair n, y n) (small n) p.1).restrict Z)}) atTop (𝓝 0) := by
    intro ε hε
    apply independent_eventually_supported_bad_probability_tendsto_zero μ' ν suffixBox
    · exact fun n => hne (small n)
    · exact hselected.mono (fun _ hn => hn.1.2.2.1)
    · intro n
      have hp := F.continuous_realScaleProfile_restrict hD
        (J (pair n)) (hJ _) (y n) X S β (small n) Z
      exact (isClosed_Ici.preimage ((hp.comp (continuous_fst.mul continuous_snd)).dist
        (hp.comp continuous_fst))).measurableSet
    · intro z hz
      exact hsuffix small hsmall hsmallstrict hsmall1 pair y z hz ε hε

  exact F.basepoint_affine_labels_of_sampling hD
    chartD hchartD π height hheight hchartheight hkill A hA X S β
    hρ hR ht scale hscale1 (Eventually.of_forall hsmall1) (fun n => J (pair n))
    (fun n => hJ _) x y u k hfactor hkheight φ hchart ξ μ' ν hDfinite hdom
    (fun n => label (pair n, x n) (scale n)) (fun n => label (pair n, y n) (small n))
    (fun n => b (pair n, x n) (scale n)) (fun n => b (pair n, y n) (small n))
    (hb scale hscale x) (hb small hsmall y) hsource
    (hprob small hsmall hsmallstrict hsmall1 y) hsuffix'

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMixedScaleBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact box inclusions needed for adjacent-scale comparisons -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L W N : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (Exp : cartanRootIdeal H → N)

set_option maxHeartbeats 1000000 in
/-- Pointwise comparison of actual exponent widths gives inclusion of
exponential boxes, without an additional geometric assumption. -/
theorem groupBox_subset_of_exponent_le
    (E E' : Set W) (β : M.Bases) (r t R : ℝ)
    (h : ∀ w : M.wordList, r * M.boxCost T hunimod eW E w ≤
      t * M.boxCost T hunimod eW E' w) :
    M.groupBox T hunimod eW Exp E β r R ⊆
      M.groupBox T hunimod eW Exp E' β t R := by
  rintro q ⟨v, hv, hc⟩
  refine ⟨v, hv, le_trans ?_ hc⟩
  exact norm_exponentialRescaleBasis_le_of_exponents_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E' (β.val j))
    (fun j => M.boxCost T hunimod eW E (β.val j)) t r (fun j => h (β.val j)) v

set_option maxHeartbeats 1000000 in
/-- Every nearby larger scale fits inside the fixed strict enlargement
at the smaller scale. The coordinate radius is unchanged. -/
theorem groupBox_scale_le_enlargement
    [FiniteDimensional ℝ W] {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hcost : ∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w)
    (β : M.Bases) {r t δ R : ℝ} (hδ : 0 ≤ δ) (hrt : t ≤ (1 + δ) * r) :
    M.groupBox T hunimod eW Exp E β t R ⊆
      M.groupBox T hunimod eW Exp ((fun w => (1 + δ) • w) '' E) β r R := by
  apply M.groupBox_subset_of_exponent_le T hunimod eW Exp
  intro w
  rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith)]
  calc
    t * M.boxCost T hunimod eW E w ≤ ((1 + δ) * r) * M.boxCost T hunimod eW E w :=
      mul_le_mul_of_nonneg_right hrt (hcost w)
    _ = r * ((1 + δ) * M.boxCost T hunimod eW E w) := by ring

open scoped Manifold

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMetricBasepointSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual dominated sampling at a nearby basepoint -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold Pointwise Topology ENNReal

variable {EG G I : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  [IsTopologicalGroup F.D.carrier]

  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- A nearby center admits a changed sampling law dominated by independent
ordinary-cell and allowed-suffix sampling. The domination constant is exact
and independent of the map, centers and scale. -/
theorem exists_metric_basepoint_dominated_sampling
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {R : ℝ} (hR : 0 < R) :
    ∃ ρ η L : ℝ, 0 < ρ ∧ 0 < η ∧ 1 ≤ L ∧
      ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ᵐ a ∂(ν : Measure F.N.carrier), a ∈
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
            ((fun w => (1 + δ) • w) '' E) β ((1 - δ / 2) * scale n) 1) ∧
        (∀ S : Set F.N.carrier, MeasurableSet S →
          (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN
            b₀ E β (scale n) 1 : Measure F.N.carrier)
              ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
          (ENNReal.ofReal L ^ finrank ℝ (cartanRootIdeal H)) *
            (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN
              b₀ E β ((1 - δ / 2) * scale n) 1 : Measure F.N.carrier).prod
                (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ S}) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log ((1 - δ / 2) * scale n))
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  let α := 1 - δ / 2
  let t := (1 + δ) * α
  have hα : 1 / 2 ≤ α := by dsimp [α]; linarith only [hδ1]
  have hα1 : α < 1 := by dsimp [α]; linarith only [hδ]
  have ht : 1 < t := by
    have hp := mul_pos hδ (sub_pos.mpr hδ1)
    dsimp [t, α]
    nlinarith only [hp]
  obtain ⟨ρ, η, L, hρ, hη, hL, hgeometry⟩ := M.exists_metric_basepoint_sampling_geometry
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    hExp realize b₀ γ₀ hpath hK hLip X hDnil bD₀ βD hβD aD hmD
    E hE hne β hβ hlo hcost hα hα1 ht hR
  refine ⟨ρ, η, L, hρ, hη, hL, ?_⟩
  intro scale hs hs1
  filter_upwards [hgeometry scale hs hs1] with n hn g hg
  obtain ⟨u, k, huk, hkheight, hcover, hsupport, hchart⟩ := hn g hg
  obtain ⟨ν, hν, hdom⟩ := M.exists_basepoint_groupBox_domination T F hunimod eW
    hExp realize haarN haarD dynkinN chartN hchartN b₀ E β (scale n) (α * scale n)
    (zero_lt_one.trans_le hL) u k hcover
  refine ⟨u, k, ν, huk, hkheight, ?_, hdom, hchart⟩
  filter_upwards [hν] with z hz
  have hscale : t * scale n ≤ (1 + δ) * (α * scale n) := by
    dsimp only [t]
    rw [mul_assoc]
  exact M.groupBox_scale_le_enlargement T hunimod eW (F.ExpN ∘ F.N.equiv) hE hne
    (fun w => hlo.le.trans (hcost w)) β hδ.le hscale (hsupport hz)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxCompact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness of exponential coordinate boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L V G : Type} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace G]

theorem isCompact_exponentialCoordinateBox {n : ℕ}
    (e : L ≃ₗ[ℝ] V) (Exp : V → G) (chart : V ≃ₜ G)
    (hchart : ∀ x, chart x = Exp x) (b : Basis (Fin n) ℝ L)
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (exponentialCoordinateBox (Exp ∘ e) b R) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR]
  have hf : ((Exp ∘ e) ∘ b.equivFun.symm) =
      chart ∘ (b.map e).equivFun.symm := by
    funext t
    simp only [Function.comp_apply, hchart, Basis.map_equivFun]
    rfl
  rw [hf]
  exact isCompact_Icc.image
    (chart.continuous.comp (b.map e).equivFun.symm.toContinuousLinearEquiv.continuous)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMetricBasepointComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric basepoint comparison from established analytic estimates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold Pointwise Topology ENNReal

variable {EG G I : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  [IsTopologicalGroup F.D.carrier]

  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  {P L : Type} [Finite L] [Nonempty L]

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- The metric and Haar construction supplies all sampling premises for
basepoint comparison; the analytic estimates are a separate proved package. -/
theorem exists_metric_basepoint_comparison
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {R : ℝ} (hR : 0 < R)
    (J : P → G → W) (hJ : ∀ p, Continuous (J p))
    (A : L → W →L[ℝ] W) (hA : Function.Injective A) :
    let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
    let height := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
    let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
    let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN b₀ E β r 1
    let raw := fun (p : P × G) r => F.realScaleProfile (funext hchartD ▸ chartD.continuous)
      (J p.1) (hJ p.1) p.2 X (boundedBracketWords d) βD r
    CompactProfileEstimates raw μ q A R (fun r => M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) ((fun w => (1 + δ) • w) '' E) β r 1) →
    let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
    let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
      (fun k => (raw p r k).restrict Z)
      (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
    ∃ η : ℝ, 0 < η ∧ ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ (1 - δ / 2) * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n, x n) (scale n) = label (p n, y n) ((1 - δ / 2) * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n, y n) ((1 - δ / 2) * scale n)) ((π ((x n)⁻¹ * y n)).toAdd)))
        atTop (𝓝 0) := by
  dsimp only
  intro estimates
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN b₀ E β r 1
  let raw := fun (p : P × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p.1) (hJ p.1)
      p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z)
    (fun L => linearBallProfile q (A L) R + ContinuousMap.const Z (b p r))
  obtain ⟨ρ₀, η, D, hρ₀, hη, hD, hgeometry⟩ := M.exists_metric_basepoint_dominated_sampling
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD hExp realize
    b₀ γ₀ hpath hK hLip
    X hDnil bD₀ βD hβD aD hmD haarN haarD E hE hne β hβ hlo hcost hδ hδ1 hR
  let ρ := min ρ₀ R
  have hρ : 0 < ρ := lt_min hρ₀ hR
  have hρR : ρ ≤ R := min_le_right _ _
  have hρ₀' : ρ ≤ ρ₀ := min_le_left _ _
  refine ⟨η, hη, ?_⟩
  have hheight : Function.Surjective height := eW.surjective.comp (cartan_height_surjective T H)
  have hkill (u v : H) : height ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character (⁅u, v⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  have hchartheight v : (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v := by
    rw [hchartD, F.compatibleD, hπExp]
    rfl
  let suffixBox := fun r => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' E) β r 1
  have hboxne r : (suffixBox r).Nonempty := by
    refine ⟨1, 0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simp only [map_zero, norm_zero]; exact zero_le_one
  let C := fun r => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
  have hfull r : ∀ᵐ z ∂(μ r : Measure F.N.carrier), z ∈ C r := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀
      E β r zero_lt_one
    simpa only [μ, C, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hcompact r : IsCompact (C r) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β r) 1 zero_le_one
  have hα : 0 < 1 - δ / 2 := by linarith only [hδ1]
  apply F.nearby_labels_of_concentration (funext hchartD ▸ chartD.continuous)
    chartD hchartD π height hheight hchartheight hkill A hA J hJ
    X (boundedBracketWords d) βD hρ hR hρR hα μ suffixBox hboxne
    (D := ENNReal.ofReal D ^ finrank ℝ (cartanRootIdeal H)) (by simp) C hcompact hfull
  · intro scale hscale hscale1
    filter_upwards [hgeometry scale hscale hscale1] with n hn g hg
    obtain ⟨u, k, ν, hf, hh, hν, hdom, hchart⟩ := hn g hg
    exact ⟨u, k, ν, hf, hh, hν, hdom, fun z hz => hchart z (hz.trans hρ₀')⟩
  · exact estimates.mean
  · exact estimates.zeroMean
  · exact estimates.suffix


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

omit [FiniteDimensional ℝ W] in
/-- Each balanced positive-multiplicity basis controls the absolute value
of every generator weight, including its negative part. -/
theorem SupportDatum.abs_weight_le_basisSupport (D : SupportDatum W I B)
    (b : B) (i : I) (x : W) : |D.weight i x| ≤ D.basisSupport b x := by
  classical
  have hpos (y : W) : D.weight i y ≤ D.basisSupport b y := by
    have hn : (1 : ℝ) ≤ D.multiplicity b i := by exact_mod_cast D.positive b i
    calc
      D.weight i y ≤ max 0 (D.weight i y) := le_max_right _ _
      _ ≤ (D.multiplicity b i : ℝ) * max 0 (D.weight i y) :=
        le_mul_of_one_le_left (le_max_left _ _) hn
      _ ≤ D.basisSupport b y := by
        apply Finset.single_le_sum (s := Finset.univ) (f := fun j =>
          (D.multiplicity b j : ℝ) * max 0 (D.weight j y))
        · intro j _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
        · exact Finset.mem_univ i
  have hm := hpos (-x)
  rw [map_neg, D.basisSupport_neg] at hm
  exact abs_le.mpr ⟨by linarith, hpos x⟩

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem isClosed_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    IsClosed (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (α i).continuous continuous_const

/-- Positive balance and separation make the sampling polyhedron compact.
No boundedness assumption on the polyhedron is needed. -/
theorem SupportDatum.isCompact_weightSamplingPolytope (D : SupportDatum W I B) (b : B) :
    IsCompact (weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap)) := by
  classical
  let α : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi D.weight
  have hα : Function.Injective α := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply D.separates x
    intro i
    exact congrFun hx i
  have hemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hα)
  let C : ℝ := ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖
  have hbound : weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap) ⊆
      α ⁻¹' Icc (fun _ => -C) (fun _ => C) := by
    intro x hx
    have hs : D.basisSupport b x ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact max_le (norm_nonneg _) (hx i)
    constructor <;> intro i
    · exact neg_le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
    · exact le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
  exact (hemb.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_weightSamplingPolytope _) hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem isCompact_samplingPolytope : IsCompact (M.samplingPolytope T hunimod eW) := by
  exact (M.supportIn T hunimod eW).isCompact_weightSamplingPolytope (Classical.arbitrary M.Bases)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedBasepointComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published-input comparison at nearby basepoints -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

set_option maxHeartbeats 1000000 in
/-- Nearby centers have the same finite affine label, and the normalized
center-height error vanishes. All geometric and analytic bridge assumptions
are derived from the precise published inputs already used for the profiles. -/
theorem exists_uniform_published_basepoint_comparison_oai
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
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
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H)
    (hcanonical : ∀ i, cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ∀ i, ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : ∀ i, 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
      let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
      let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
        (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
      let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
        (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
          C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
      let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ r 1
      let raw := fun (p : NormalizedPair G Λ × G) r =>
        F.realScaleProfile (funext hchartD ▸ chartD.continuous)
          (fun g => (π (p.1.val.1 g)).toAdd) (hπ.comp p.1.property.1.1).continuous
          p.2 X (boundedBracketWords d) βD r
      let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
      let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
        (fun k => (raw p r k).restrict Z) (fun L => A L + ContinuousMap.const Z (b p r))
      ∃ η : ℝ, 0 < η ∧ ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop →
        StrictMono scale → (∀ n, 1 ≤ scale n) →
        (∀ n, 1 ≤ (1 - δ / 2) * scale n) →
        ∀ (pair : ℕ → NormalizedPair G Λ) (x y : ℕ → G),
        (∀ n, dist (x n) (y n) ≤ η * scale n) →
        (∀ᶠ n in atTop, label (pair n, x n) (scale n) =
          label (pair n, y n) ((1 - δ / 2) * scale n)) ∧
        Tendsto (fun n => (scale n)⁻¹ •
          ((π ((pair n).val.1 (y n))).toAdd - (π ((pair n).val.1 (x n))).toAdd -
            (label (pair n, y n) ((1 - δ / 2) * scale n)).val
              ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  classical
  obtain ⟨δ₁, hδ₁, hestimates⟩ := M.exists_uniform_published_profile_estimates T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  let δ₀ := min (1 / 2) δ₁
  refine ⟨δ₀, lt_min (by norm_num) hδ₁, ?_⟩
  intro δ hδ hδle R hR hZheight
  have hd1 : δ ≤ δ₁ := hδle.trans (min_le_right _ _)
  have hδlt : δ < 1 := lt_of_le_of_lt (hδle.trans (min_le_left _ _)) (by norm_num)
  have estimates := hestimates δ hδ hd1 R hR hZheight
  dsimp only
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    L.val.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : Function.Injective A := by
    intro a a' he
    apply Subtype.ext
    ext w
    exact DFunLike.congr_fun he w
  have hE := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
  have hlo : 0 < lo := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_gt hn)
    have hn' := mul_nonneg (Nat.cast_nonneg M.bound) hhi
    linarith only [hgap, hh, hn']
  exact M.exists_metric_basepoint_comparison T F hunimod eW π hπExp chartN hchartN
    chartD hchartD dynkinN dynkinD hExp realize bN γ hpath Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    X hDnil bD₀ βD hβD aD hmD haarN haarD Eall hE hne γ hγ hlo
    (fun w => (hcost w).1) hδ hδlt hR
    (fun p : NormalizedPair G Λ => fun g => (π (p.val.1 g)).toAdd)
    (fun p => (hπ.comp p.property.1.1).continuous) A hA estimates

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison_oai
